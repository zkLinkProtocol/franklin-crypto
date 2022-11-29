use super::*;
use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::plonk::circuit::BigUint;
use crate::plonk::circuit::bigint::Extension6Params;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::Engine;
use crate::bellman::GenericCurveAffine;
use crate::plonk::circuit::bigint::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::plonk::circuit::PrimeField;
use crate::plonk::circuit::boolean::Boolean;

use std::str::FromStr;


#[derive(Clone, Copy, Debug)]
pub enum Ops {
    // first output, then inputs
    ExpByX(usize, usize), 
    Mul(usize, usize, usize),
    Square(usize, usize),
    Conj(usize, usize),
    Frob(usize, usize, usize) // the last parameter is power
}


// prepared point is exactly point in jacobian coordinates defined over Fq2
struct PreparedPoint<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where G::Base : PrimeField
{
    x: Fp2<'a, E, G::Base, T>,
    y: Fp2<'a, E, G::Base, T>,
    z: Fp2<'a, E, G::Base, T>
}


pub trait PairingParams<E: Engine, G: GenericCurveAffine, T: Extension12Params<G::Base>> 
where G::Base : PrimeField
{
    fn get_miller_loop_scalar_decomposition() -> Vec<i64>; 
    fn get_x() -> BigUint;
    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize);
    
    // require: Q \in E(Fq2) and P \in E(Fq),
    // ensure: T = 2Q and l_Q,Q(P) \in Fq12 , where l_Q,Q is tangent line to the curve at Q
    fn double_and_eval<'a, CS: ConstraintSystem<E>>(
        ext_point: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>, 
        base_point: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<
        (Fp12<'a, E, G::Base, T>, PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>), 
        SynthesisError
    >;

    // require: Q, R \in E(Fq2) and P \in E(Fp),
    // ensure: T = Q + R and l_R,Q(P) \in Fp12 , where l is a unique line function passing through R and Q
    fn add_and_eval<'a, CS: ConstraintSystem<E>>(
        q: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>, 
        r: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<
        (Fp12<'a, E, G::Base, T>, PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>), 
        SynthesisError
    >;
        
    fn final_exp_easy_part<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &mut Fp12<'a, E, G::Base, T>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, G::Base, T>, SynthesisError> {
        // easy part: result = f^((q^6-1)*(q^2+1))
        // we use that one-time torus compression cost can be absorbed directly in the easy part computation as follows:
        // let m = m0 + w * m1 \in Fp12 be the Miller loop result, then:
        // m^{p^6−1} = (m0 + w*m1)^{p^6−1} = (m0 + w*m1)^{p^6} / (m0 + w*m1) = (m0 − w*m1)/(m0 + w*m1) = 
        // = (−m0/m1 + w)/(−m0/m1 − w) = Dec(-m0/m1)
        // hence: Enc(m^{(p^6-1)(p^2+1)}) = Enc(Dec(-m0/m1)^{p^2+1}) = (-m0/m1)^{p^2+1} = [[(-m0/m1)^{p^2) * (-m0/m1)]]
        // where all multiplications and power-maps inside [[ ]] are treated as operations on T2

        // we need to implement custom conversion m = m0 + w * m1 \in Fp12 -> -m0/m1 \in T2
        let params = elem.get_params();
        let x = if is_safe_version {
            // if m1 == 0 \them m actually belongs to \Fp6, and hence m^{p^6−1} = 1
            // modified formula is res = (!flag * m0) / (m1 + flag)
            let is_exceptional = Fp6::is_zero(&mut elem.c1, cs)?;
            let numer = Fp6::conditionally_select(cs, &is_exceptional, &Fp6::zero(params), &elem.c0)?;
            let denom = elem.c1.add(cs, &Fp6::from_boolean(&is_exceptional, params))?;
            let encoding = Fp6::div(cs, &numer, &denom)?;
            TorusWrapper::new(encoding, Boolean::Constant(true), is_exceptional)
        } else {
            // the result of Miller loop belongs to Fp12* and hence is never zero, 
            // hence m0 and m1 can't be zero simultaneously
            let encoding = Fp6::div(cs, &elem.c0, &elem.c1)?;
            TorusWrapper::new(encoding, Boolean::Constant(true), Boolean::Constant(false))
        };

        // now compute x^{p^2} * x
        let y = x.frobenius_power_map(cs, 2)?;
        TorusWrapper::mul(cs, &y, &x, is_safe_version)
    }

    fn final_exp_hard_part<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, elem: &TorusWrapper<'a, E, G::Base, T>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, G::Base, T>, SynthesisError> {
        let params = elem.get_params();
        let (ops_chain, num_of_variables) = self.get_hard_part_ops_chain();
        let x = Self::get_x();
        let mut scratchpad = vec![TorusWrapper::<'a, E, G::Base, T>::uninitialized(params); num_of_variables];
        scratchpad[0] = elem.clone();
        for op in ops_chain.into_iter() {
            match op {
                Ops::ExpByX(out_idx, in_idx) => {
                    scratchpad[out_idx] = TorusWrapper::pow(&scratchpad[in_idx], cs, &x, is_safe_version)?;
                },
                Ops::Mul(out_idx, left_idx, right_idx) => {
                    scratchpad[out_idx] = TorusWrapper::mul(
                        cs, &scratchpad[left_idx], &scratchpad[right_idx], is_safe_version
                    )?;
                },
                Ops::Square(out_idx, in_idx) => {
                    scratchpad[out_idx] = scratchpad[in_idx].square(cs, is_safe_version)?;
                },
                Ops::Conj(out_idx, in_idx) => {
                    scratchpad[out_idx] = scratchpad[in_idx].conjugation();
                },
                Ops::Frob(out_idx, in_idx, power) => {
                    scratchpad[out_idx] = scratchpad[in_idx].frobenius_power_map(cs, power)?;
                }
            }
        };
        Ok(scratchpad[0].clone())
    }

    fn miller_loop<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        base_point: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        ext_point: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<
        (Fp12<'a, E, G::Base, T>, PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>), 
        SynthesisError
    > {
        let params = &base_point.circuit_params.base_field_rns_params;
        let mut fp_12_acc = Fp12::one(params);
        let mut ext_point_acc = ext_point.clone();

        for bit in Self::get_miller_loop_scalar_decomposition().iter().rev() {
            let (new_ext_point_acc, line_eval) = Self::double_and_eval(cs, &ext_point_acc, &base_point)?;
            ext_point = new_ext_point_acc;
            fp_12_acc = Fp12::mul(cs, &fp_12_acc, &line_eval)?;
            
            let mut to_add = ext_point.clone();
            if bit == -1 {
                to_add.negate(cs)?;
            }
            if bit == 1 || bit == -1 {
                let (new_ext_point_acc, line_eval) = Self::add_and_eval(cs, &ext_point_acc, &to_add, &base_point)?;
                ext_point = new_ext_point_acc;
                fp_12_acc = Fp12::mul(cs, &fp_12_acc, &line_eval)?;
            }
        }
    }
}


#[derive(Clone, Copy, Debug)]
pub enum Bn256HardPartMethod {
    Devegili,
    FuentesCastaneda
}


#[derive(Clone, Debug)]
pub struct Bn256PairingParams<E: Engine> {
    hard_part_method: Bn256HardPartMethod,
    marker: std::marker::PhantomData<E>
}

impl<E: Engine> Bn256PairingParams<E> {
    fn new(hard_part_method: Bn256HardPartMethod) -> Self {
        Bn256PairingParams {
            hard_part_method,
            marker: std::marker::PhantomData::<E>
        }
    }

    // let x be parameter parametrizing particular curve in Bn256 family of curves
    // there are two competing agorithms for computing hard part of final exponentiation fot Bn256 family of curves
    // the first one is Devegili method which takes 3exp by x, 11 squaring, 14 muls
    // the second one is Fuentes-Castaneda methid which takes 3exp by x, 4 square, 10 muls and 3 Frobenius powers
    // we implement both of them and will select the most efficient later

    // Devegili method:
    // 1) a = f^x         7) a = conj(a)       13) t1 = t1^9       19) t0 = frob(f, 2)     25) t0 = t0^x
    // 2) b = a^2         8) b = frob(a)       14) a = t1 * a      20) b = b * t0          26) t0 = t0 * b
    // 3) a = b * f^2     9) b = a * b         15) t1 = f^4        21) t0 = b^x            27) a = t0 * a
    // 4) a = a^2         10) a = a * b        16) a = a * t1      22) t1 = t0^2           28) t0 = frob(f, 3)
    // 5) a = a * b       11) t0 = frob(f)     17) t0 = t0^2       23) t0 = t1^2           29) f = t0 * a
    // 6) a = a * f       12) t1 = t0 * f      18) b = b * t0      24) t0 = t0 * t1
    fn devegili_method() -> (Vec<Ops>, usize) {
        let (f, a, b, tmp, t0, t1) = (0, 1, 2, 3, 4, 5);
        let ops_chain = vec![
            /*1*/ Ops::ExpByX(a, f), /*2*/ Ops::Square(b, a), /*3*/ Ops::Square(tmp, f), Ops::Mul(a, b, tmp), 
            /*4*/ Ops::Square(a, a), /*5*/ Ops::Mul(a, a, b),  /*6*/ Ops::Mul(a, a, f), /*7*/ Ops::Conj(a, a),
            /*8*/ Ops::Frob(b, a, 1), /*9*/ Ops::Mul(b, a, b), /*10*/ Ops::Mul(a, a, b), /*11*/ Ops::Frob(t0, f, 1),
            /*12*/ Ops::Mul(t1, t0, f), /*13*/ Ops::Square(tmp, t1), Ops::Square(tmp, tmp), Ops::Square(tmp, tmp),
            Ops::Mul(tmp, tmp, t1), /*14*/ Ops::Mul(a, t1, a), /*15*/ Ops::Square(tmp, f), Ops::Square(t1, tmp),
            /*16*/ Ops::Mul(a, a, t1), /*17*/ Ops::Square(t0, t0), /*18*/ Ops::Mul(b, b, t0), /*19*/ Ops::Frob(t0, f, 2),
            /*20*/ Ops::Mul(b, b, t0), /*21*/ Ops::ExpByX(t0, b), /*22*/ Ops::Square(t1, t0), /*23*/ Ops::Square(t0, t1),
            /*24*/ Ops::Mul(t0, t0, t1), /*25*/ Ops::ExpByX(t0, t0), /*26*/ Ops::Mul(t0, t0, b), /*27*/ Ops::Mul(a, t0, a),
            /*28*/ Ops::Frob(t0, f, 3), /*29*/ Ops::Mul(f, t0, a)
        ];
        (ops_chain, 6)
    }

    // This is Fuentes-Castaneda method:
    // 1) a = f^x          5) t = b^x                        9) t = t^2                 13) f = f * frob(t, 3)
    // 2) a = a^2          6) f = f * frob(conj(f), 3)       10) t = t^x                14) f = f * frob(t)
    // 3) b = a^2          7) f = f * t                      11) b = b * t              15) f = f * b
    // 4) b = a * b        8) b = b * t                      12) t = b * conj(a)        16) f = f * frob(b, 2)
    fn fuentes_castaneda_method() -> (Vec<Ops>, usize) {
        let (f, a, b, tmp, t) = (0, 1, 2, 3, 4);
        let ops_chain = vec![
            /*1*/ Ops::ExpByX(a, f), /*2*/ Ops::Square(a, a), /*3*/ Ops::Square(b, a), /*4*/ Ops::Mul(b, a, b),
            /*5*/ Ops::ExpByX(t, b), /*6*/ Ops::Conj(tmp, f), Ops::Frob(tmp, tmp, 3), Ops::Mul(f, f, tmp),
            /*7*/ Ops::Mul(f, f, t), /*8*/ Ops::Mul(b, b, t), /*9*/ Ops::Square(t, t), /*10*/ Ops::ExpByX(t, t),
            /*11*/ Ops::Mul(b, b, t), /*12*/ Ops::Conj(tmp, a), Ops::Mul(t, b, tmp), /*13*/ Ops::Frob(tmp, t, 3),
            Ops::Mul(f, f, tmp), /*14*/ Ops::Frob(tmp, t, 1),  Ops::Mul(f, f, tmp), /*15*/ Ops::Mul(f, f, b),
            /*16*/  Ops::Frob(tmp, b, 2), Ops::Mul(f, f, tmp)
        ];
        (ops_chain, 5)
    }
}

impl<E: Engine> PairingParams<E, Bn256Fq, Bn256Extension12Params> for Bn256PairingParams<E> {
    fn get_x() -> BigUint {
        BigUint::from_str("6518589491078791937").expect("should parse")
    }

    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize) {
        match self.hard_part_method {
            Bn256HardPartMethod::Devegili => Self::devegili_method(),
            Bn256HardPartMethod::FuentesCastaneda => Self::fuentes_castaneda_method(),
        }
    }
}


// TODO: consider which strategy is optimal - 
// either this one: Guide to pairing based crypto using projective coordinates
// or this one: https://eprint.iacr.org/2010/354.pdf 

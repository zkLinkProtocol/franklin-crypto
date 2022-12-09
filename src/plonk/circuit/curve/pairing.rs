use super::*;
use crate::bellman::pairing::bn256::*;
use crate::plonk::circuit::BigUint;
use crate::plonk::circuit::bigint::Extension6Params;
use crate::bellman::SynthesisError;
use crate::plonk::circuit::Engine;
use crate::bellman::GenericCurveAffine;
use crate::plonk::circuit::bigint::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::plonk::circuit::PrimeField;
use crate::plonk::circuit::boolean::Boolean;
use crate::bellman::Field;

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


// prepared point is exactly point in Jacobian coordinates defined over Fq2
#[derive(Clone, Debug)]
pub struct PreparedPoint<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where G::Base : PrimeField
{
    x: Fp2<'a, E, G::Base, T>,
    y: Fp2<'a, E, G::Base, T>,
    z: Fp2<'a, E, G::Base, T>
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> PreparedPoint<'a, E, G, T> 
where G::Base : PrimeField
{
    fn from_coordinates(x: Fp2<'a, E, G::Base, T>, y: Fp2<'a, E, G::Base, T>, z: Fp2<'a, E, G::Base, T>) -> Self {
        PreparedPoint { x, y, z }
    }
    
    fn assert_if_normalized(&self) {
        assert!(self.z.is_constant());
        assert_eq!(self.z.get_value().unwrap(), T::Witness::one());
    }

    fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        res.y = res.y.negate(cs)?;
        Ok(res)
    }

    fn frobenius_power_map<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, power:usize
    )-> Result<Self, SynthesisError> {
        let x = self.x.frobenius_power_map(cs, power)?;
        let y = self.y.frobenius_power_map(cs, power)?; 
        let z = self.z.frobenius_power_map(cs, power)?;
        Ok(Self::from_coordinates(x, y, z))  
    }
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
        cs: &mut CS,
        q: &mut PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>, 
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<Fp12<'a, E, G::Base, T>, SynthesisError>;

    // require: Q, R \in E(Fq2) and P \in E(Fp),
    // ensure: T = Q + R and l_R,Q(P) \in Fp12 , where l is a unique line function passing through R and Q
    fn add_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        q: &mut PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>, 
        r: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<Fp12<'a, E, G::Base, T>, SynthesisError>;

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

        // actual value of compressed element is (m0 − w*m1)/(m0 + w*m1)
        let value = elem.get_value().map(|x| {
            let (c0, mut c1) = T::convert_from_structured_witness(x);
            c1.negate();
            let mut res = T::convert_to_structured_witness(c0, c1);
            let x_inv = x.inverse().unwrap();
            res.mul_assign(&x_inv);
            res
        });

        let value2 = elem.get_value().map(|x| {
            let mut res = x;
            res.frobenius_map(6);
            let x_inv = x.inverse().unwrap();
            res.mul_assign(&x_inv);
            res
        });
        assert_eq!(value, value2);

        // we need to implement custom conversion m = m0 + w * m1 \in Fp12 -> -m0/m1 \in T2
        let params = elem.get_params();
        let x = if is_safe_version {
            // if m1 == 0 \them m actually belongs to \Fp6, and hence m^{p^6−1} = 1
            // modified formula is res = (!flag * m0) / (m1 + flag)
            let is_exceptional = Fp6::is_zero(&mut elem.c1, cs)?;
            let numer = Fp6::conditionally_select(cs, &is_exceptional, &Fp6::zero(params), &elem.c0)?;
            let denom = elem.c1.add(cs, &Fp6::from_boolean(&is_exceptional, params))?;
            let mut encoding = Fp6::div(cs, &numer, &denom)?;
            encoding = encoding.negate(cs)?;
            TorusWrapper::new(encoding, Boolean::Constant(false), is_exceptional, value)
        } else {
            // the result of Miller loop belongs to Fp12* and hence is never zero, 
            // hence m0 and m1 can't be zero simultaneously
            let mut encoding = Fp6::div(cs, &elem.c0, &elem.c1)?;
            encoding = encoding.negate(cs)?;
            TorusWrapper::new(encoding, Boolean::Constant(false), Boolean::Constant(false), value)
        };

        // now compute x^{p^2} * x
        let y = x.frobenius_power_map(cs, 2)?;
        let res = TorusWrapper::mul(cs, &y, &x, is_safe_version)?;

        println!("easy part value: {}", res.value.unwrap());
        Ok(res)
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
                    scratchpad[out_idx] = scratchpad[in_idx].conjugation(cs)?;
                },
                Ops::Frob(out_idx, in_idx, power) => {
                    scratchpad[out_idx] = scratchpad[in_idx].frobenius_power_map(cs, power)?;
                }
            }
            
        };
        Ok(scratchpad[0].clone())
    }

    fn mul_by_sparse_01<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, full_elem: &Fp6<'a, E, G::Base, T::Ex6>, sparse_elem: &Fp6<'a, E, G::Base, T::Ex6>
    ) -> Result<Fp6<'a, E, G::Base, T::Ex6>, SynthesisError> {
        let (c0, c1, c2) = full_elem.get_coordinates();
        let (a, b, c) = sparse_elem.get_coordinates();
        assert!(c.is_constant());
        assert!(c.get_value().unwrap().is_zero());
        let alpha = T::Ex6::non_residue();

        let v0 = Fp2::mul(&c0, cs, &a)?;
        let v1 = Fp2::mul(&c1, cs, &b)?;
        
        let mut t0 = c1.add(cs, &c2)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&v1);
        t0 = Fp2::mul_with_chain(cs, &t0, &b, chain)?;
        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&v0);
        t0 = t0.mul_by_small_constant_with_chain(cs, alpha, chain)?;

        let mut t1 = c0.add(cs, &c1)?;
        let tmp = a.add(cs, &b)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&v0).add_neg_term(&v1);
        t1 = Fp2::mul_with_chain(cs, &tmp, &t1, chain)?;

        let mut t2 = c0.add(cs, &c2)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&v0).add_pos_term(&v1);
        t2 = Fp2::mul_with_chain(cs, &a, &t2, chain)?;

        let res = Fp6::from_coordinates(t0, t1, t2);
        let mut actual_res = full_elem.get_value().unwrap();
        actual_res.mul_assign(&sparse_elem.get_value().unwrap());
        assert_eq!(res.get_value().unwrap(), actual_res);

        Ok(res)
    }

    // implementaiion of sparse multiplication by element c = [c0, 0, 0, c3, c4, 0]
    fn mul_by_sparse_034<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        full_elem: &Fp12<'a, E, G::Base, T>,
        sparse_elem: &Fp12<'a, E, G::Base, T>
    ) -> Result<Fp12<'a, E, G::Base, T>, SynthesisError> {
        let z: Vec<Fp2<E, G::Base, <T::Ex6 as Extension6Params<G::Base>>::Ex2>> = {
            full_elem.get_base_field_coordinates().chunks(2).map(|ch| {
                Fp2::from_coordinates(ch[0].clone(), ch[1].clone())
            }).collect()
        };
        let x: Vec<Fp2<E, G::Base, <T::Ex6 as Extension6Params<G::Base>>::Ex2>> = {
            sparse_elem.get_base_field_coordinates().chunks(2).map(
                |ch| Fp2::from_coordinates(ch[0].clone(), ch[1].clone())
            ).collect()
        };
        for idx in [1, 2, 5].iter() {
            assert!(x[*idx].is_constant());
            assert!(x[*idx].get_value().unwrap().is_zero());
        }
        let params = full_elem.get_params();

        let fp6_sparse_elem = Fp6::from_coordinates(x[3].clone(), x[4].clone(), Fp2::zero(params));
        let b = Self::mul_by_sparse_01(cs, &full_elem.c1, &fp6_sparse_elem)?;

        let tmp = x[0].add(cs, &x[3])?;
        let fp6_sparse_elem = Fp6::from_coordinates(tmp, x[4].clone(), Fp2::zero(params));
        let fp6_full_elem = full_elem.c0.add(cs, &full_elem.c1)?;
        let e = Self::mul_by_sparse_01(cs, &fp6_full_elem, &fp6_sparse_elem)?;

        let a0 = z[0].mul(cs, &x[0])?;
        let a1 = z[1].mul(cs, &x[0])?;
        let a2 = z[2].mul(cs, &x[0])?;
        let a = Fp6::from_coordinates(a0, a1, a2);
        
        let mut chain = Fp6Chain::new();
        chain.add_pos_term(&e).add_neg_term(&a).add_neg_term(&b);
        let t1 = Fp6::collapse_chain(cs, chain)?;
       
        let mut t0 = Fp12::<'a, E, G::Base, T>::fp6_mul_subroutine(cs, &b)?;
        t0 = t0.add(cs, &a)?;
       
        let res = Fp12::from_coordinates(t0, t1);
        let mut actual_res = full_elem.get_value().unwrap();
        actual_res.mul_assign(&sparse_elem.get_value().unwrap());
        assert_eq!(res.get_value().unwrap(), actual_res);
        Ok(res)
    }

    fn miller_loop_postprocess<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        q: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        t: &mut PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        f: &Fp12<'a, E, G::Base, T>,
    ) -> Result<Fp12<'a, E, G::Base, T>, SynthesisError>;

    fn miller_loop<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        q: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<
        (Fp12<'a, E, G::Base, T>, PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>), 
        SynthesisError
    > {
        // we should enforce that addition and doubling in Jacobian coordinates are exception free
        let params = &p.circuit_params.base_field_rns_params;
        let mut f = Fp12::one(params);
        let mut t = q.clone();

        for bit in Self::get_miller_loop_scalar_decomposition().into_iter().rev().skip(1) {
            f = f.square(cs)?;
            let line_eval = Self::double_and_eval(cs, &mut t, &p)?;
            f = Self::mul_by_sparse_034(cs, &f, &line_eval)?;
           
            let mut to_add = q.clone();
            if bit == -1 {
                to_add = to_add.negate(cs)?;
            }
            if bit == 1 || bit == -1 {
                let line_eval = Self::add_and_eval(cs, &mut t, &to_add, &p)?;
                f = Self::mul_by_sparse_034(cs, &f, &line_eval)?;
            }
        }
        Ok((f, t))
    }

    fn pairing<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        q: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, G::Base, T>, SynthesisError> {
        // based on "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves"
        // by Jean-Luc Beuchat et. al. (Algorithm 1)
        let (mut f, mut t) = Self::miller_loop(cs, p, q)?;
        f = Self::miller_loop_postprocess(cs, &p, &q, &mut t, &f)?;
        let wrapped_f = Self::final_exp_easy_part(cs, &mut f, is_safe_version)?;
        self.final_exp_hard_part(cs, &wrapped_f, is_safe_version)
        //Ok(TorusWrapper::uninitialized(&p.circuit_params.base_field_rns_params))
    }
}


#[derive(Clone, Copy, Debug)]
pub enum Bn256HardPartMethod {
    Devegili,
    FuentesCastaneda,
    Naive
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
        let (f, f2, a, b, tmp, t0, t1) = (0, 1, 2, 3, 4, 5, 6);
        let ops_chain = vec![
            /*1*/ Ops::ExpByX(a, f), /*2*/ Ops::Square(b, a), /*3*/ Ops::Square(f2, f), Ops::Mul(a, b, f2), 
            /*4*/ Ops::Square(a, a), /*5*/ Ops::Mul(a, a, b),  /*6*/ Ops::Mul(a, a, f), /*7*/ Ops::Conj(a, a),
            /*8*/ Ops::Frob(b, a, 1), /*9*/ Ops::Mul(b, a, b), /*10*/ Ops::Mul(a, a, b), /*11*/ Ops::Frob(t0, f, 1),
            /*12*/ Ops::Mul(t1, t0, f), /*13*/ Ops::Square(tmp, t1), Ops::Square(tmp, tmp), Ops::Square(tmp, tmp),
            Ops::Mul(t1, tmp, t1), /*14*/ Ops::Mul(a, t1, a), /*15*/ Ops::Square(t1, f2),
            /*16*/ Ops::Mul(a, a, t1), /*17*/ Ops::Square(t0, t0), /*18*/ Ops::Mul(b, b, t0), /*19*/ Ops::Frob(t0, f, 2),
            /*20*/ Ops::Mul(b, b, t0), /*21*/ Ops::ExpByX(t0, b), /*22*/ Ops::Square(t1, t0), /*23*/ Ops::Square(t0, t1),
            /*24*/ Ops::Mul(t0, t0, t1), /*25*/ Ops::ExpByX(t0, t0), /*26*/ Ops::Mul(t0, t0, b), /*27*/ Ops::Mul(a, t0, a),
            /*28*/ Ops::Frob(t0, f, 3), /*29*/ Ops::Mul(f, t0, a)
        ];
        (ops_chain, 7)
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

    // this is algorithm implemented in pairing crate
    // fp
    // 1) fp2 = frob(f, 2)
    // 2) fp3 = fp2^p
    // 3) fu = f^x
    // 4) fu2 = fu^x
    // 5) fu3 = fu2^x
    // 6) y3 = conj(fu^p)
    // 7) fu2p = fu2^p
    // 8) fu3p = fu3^p
    // 9) y2 = frob(fu2, 2)
    // 10) y0 = fp * fp2 * fp3
    // 11) y1 = conj(f)
    // 12)  y5 = conj(fu2)
    // 13) y4 = conj(fu * fu2p)
    // 14) y6 = conj(fu3 * fu3p)^2 * y4 * y5
    // 15) t1 = y3 * y5 * y6
    // 16) y6 = y6 * y2
    // 17) t1 = t1^2
    // 18) t1 = t1 * y6
    // 19) t1 = t1^2
    // 2) t0 = t1 * y1
    // 21) t1 = t1 * y0
    // t0 = t0^2
    //  f = t0 * t1
    fn naive_method() -> (Vec<Ops>, usize) {
        let (f, fp, tmp, fp2, fp3, fu, fu2, fu3, y3, fu2p, fu3p, y2, y0, y1, y4, y5, y6, t0, t1) = (
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
        let ops_chain = vec![
            Ops::Frob(fp, f, 1), 
            Ops::Frob(fp2, f, 2), Ops::Frob(fp3, fp2, 1), Ops::ExpByX(fu, f), Ops::ExpByX(fu2, fu), Ops::ExpByX(fu3, fu2),
            Ops::Frob(tmp, fu, 1), Ops::Conj(y3, tmp), Ops::Frob(fu2p, fu2, 1), Ops::Frob(fu3p, fu3, 1),
            Ops::Frob(y2, fu2, 2), Ops::Mul(tmp, fp, fp2), Ops::Mul(y0, tmp, fp3),  Ops::Conj(y1, f),  
            Ops::Conj(y5, fu2), Ops::Mul(tmp, fu, fu2p),   Ops::Conj(y4, tmp), Ops::Mul(tmp, fu3, fu3p), 
            Ops::Conj(tmp, tmp), Ops::Square(tmp, tmp), Ops::Mul(tmp, tmp, y4), Ops::Mul(y6, tmp, y5),
            Ops::Mul(tmp, y3, y5), Ops::Mul(t1, tmp, y6), Ops::Mul(y6, y2, y6), Ops::Square(t1, t1),
            Ops::Mul(t1, t1, y6), Ops::Square(t1, t1), Ops::Mul(t0, t1, y1),  Ops::Mul(t1, t1, y0),
            Ops::Square(t0, t0), Ops::Mul(f, t0, t1)
        ];
        (ops_chain, 19)
    }

}


impl<E: Engine> PairingParams<E, <Bn256 as Engine>::G1Affine, Bn256Extension12Params> for Bn256PairingParams<E> {
    fn get_x() -> BigUint {
        BigUint::from_str("4965661367192848881").expect("should parse")
    }

    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize) {
        match self.hard_part_method {
            Bn256HardPartMethod::Devegili => Self::devegili_method(),
            Bn256HardPartMethod::FuentesCastaneda => Self::fuentes_castaneda_method(),
            Bn256HardPartMethod::Naive => Self::naive_method()
        }
    }

    fn get_miller_loop_scalar_decomposition() -> Vec<i64> {
        vec![
            0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
	        1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1
        ]
    }
    
    fn double_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        q: &mut PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
    ) -> Result<Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, SynthesisError>
    {
        // let Q = (X : Y: Z) and P = (x, y); T = 2Q = (X3 : Y3 : Z3) 
        // High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves" (alg. 26)
        // TODO: compare with our current implementation of projective doubling - may be this one is more effective
        // cost of the implementation: 2M + 7S + 5A 
        // and using our projecitve curve module the cost would be: 6M + 3S + 3A
        // so it bolis down to comparison of cost of squaring againts cost of multiplication
        // TODO: optimize later! (notice that z2 occures two often)

        use bellman::GenericCurveProjective;
        let mut old_q = <Bn256 as Engine>::G2::from_xyz_unchecked(
            q.x.get_value().unwrap(), q.y.get_value().unwrap(), q.z.get_value().unwrap()
        );
    
        // 1. tmp0 := X^2
        let tmp0 = q.x.square(cs)?;
        // 2. tmp1 := Y^2
        let tmp1 = q.y.square(cs)?;
        // 3. tmp2 := tmp1^2
        let tmp2 = tmp1.square(cs)?;
        // 4. tmp3 := (tmp1 + X)^2 - tmp0 - tmp2;
        let tmp = tmp1.add(cs, &q.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&tmp0).add_neg_term(&tmp2);
        let tmp3 = tmp.square_with_chain(cs, chain)?; 
        // 5. tmp3 := 2 * tmp3;
        let tmp3 = tmp3.double(cs)?;
        // 6. tmp4 := 3 * tmp0;
        let tmp4 = tmp0.scale(cs, 3)?;
        // 7. tmp6 := X + tmp4;
        let tmp6 = q.x.add(cs, &tmp4)?;
        // 8. tmp5 := tmp4^2
        let tmp5 = tmp4.square(cs)?;
        // 9.  X3 := tmp5 - 2*tmp3
        let tmp = tmp3.double(cs)?;
        let new_x = tmp5.sub(cs, &tmp)?;
        // 10. Z3 := (Y+Z)^2 - tmp1 - Z^2
        let z_squared = q.z.square(cs)?;
        let tmp = q.y.add(cs, &q.z)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&tmp1).add_neg_term(&z_squared);
        let new_z = tmp.square_with_chain(cs, chain)?;
        // 11. Y3 := (tmp3 - X1) * tmp4 - 8 * tmp2;
        let tmp = tmp3.sub(cs, &new_x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&tmp2.scale(cs, 8)?);
        let new_y = Fp2::mul_with_chain(cs, &tmp, &tmp4, chain)?;
        // 12. tmp3 := -2 * (tmp4 * Z^2)
        let tmp = tmp4.negate(cs)?;
        let tmp = tmp.double(cs)?;
        let tmp3 = tmp.mul(cs, &z_squared)?;
        // 13. tmp3 := tmp3 * xp (mul by base Field)
        let tmp3 = tmp3.mul_by_base_field(cs, &p.x)?;
        // 14. tmp6 := tmp6^2 - tmp0 - tmp5 - 4 * tmp1
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&tmp0).add_neg_term(&tmp5).add_neg_term(&tmp1.scale(cs, 4)?);
        let tmp6 = tmp6.square_with_chain(cs, chain)?;
        // 16. tmp0 := 2 * zt * zy^2 * yp (mul ny base Field)
        let mut tmp0 = new_z.double(cs)?;
        tmp0 = tmp0.mul(cs, &z_squared)?;
        tmp0 = tmp0.mul_by_base_field(cs, &p.y)?;
        // 17. line_function := [tmp0, 0, 0, tmp3, tmp6, 0]
        let zero = Fp2::zero(q.x.get_params()); 
        let fp6_x = Fp6::from_coordinates(tmp0, zero.clone(), zero.clone());
        let fp6_y = Fp6::from_coordinates(tmp3, tmp6, zero);

        let new_q = <Bn256 as Engine>::G2::from_xyz_unchecked(
            new_x.get_value().unwrap(), new_y.get_value().unwrap(), new_z.get_value().unwrap()
        );
        old_q.double();
        assert_eq!(old_q, new_q);
        
        *q = PreparedPoint { x: new_x, y: new_y, z: new_z };
        Ok(Fp12::from_coordinates(fp6_x, fp6_y))
    }

    fn add_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        acc: &mut PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>, 
        to_add: &PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>
    ) -> Result<Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, SynthesisError> {
        use bellman::GenericCurveProjective;
        let mut old_q = <Bn256 as Engine>::G2::from_xyz_unchecked(
            acc.x.get_value().unwrap(), acc.y.get_value().unwrap(), acc.z.get_value().unwrap()
        );
        let mut old_r = <Bn256 as Engine>::G2::from_xyz_unchecked(
            to_add.x.get_value().unwrap(), to_add.y.get_value().unwrap(), to_add.z.get_value().unwrap()
        );
        // also is airthmetic in jacobian coordinates exception free?
        // TODO: invetigate comparison between this approach and using formulas from projective curve crate
        // High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves" (alg. 27)
        // Q = (xq : yq : zq), R = (xr : yr : 1) and P = (xp, yp), T = Q + R = (xt: yt: zt)
        // 1) t2 = xq - xr
        // Z_R can be saved for later use

        // we assume that q is actuallu affine
        let q = &to_add;
        let r = &acc;
        q.assert_if_normalized();
        let z_r_squared = r.z.square(cs)?;
        let y_q_squared = q.y.square(cs)?;
        
        let tmp = q.y.add(cs, &r.z)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&z_r_squared).add_neg_term(&y_q_squared);
        let mut t1 = tmp.square_with_chain(cs, chain)?;

        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&r.x);
        let t2 = Fp2::mul_with_chain(cs, &q.x, &z_r_squared, chain)?;

        let t3 = t2.square(cs)?;
        let t4 = t3.scale(cs, 4)?;
        let t5 = t4.mul(cs, &t2)?;

        // t6 = t1 * z_r^2 − 2 y_r;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&r.y.double(cs)?);
        let t6 = Fp2::mul_with_chain(cs, &t1, &z_r_squared, chain)?;
    
        let t9 = t6.mul(cs, &q.x)?;
        let t7 = r.x.mul(cs, &t4)?;

        // tx = t6^2 - t5 - 2 * t7
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&t5).add_neg_term(&t7.double(cs)?);
        let tx = t6.square_with_chain(cs, chain)?;

        // tz = (z.r + t2)^2 - z.r^2 - t3
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&z_r_squared).add_neg_term(&t3);
        let tmp = r.z.add(cs, &t2)?;
        let tz = tmp.square_with_chain(cs, chain)?;
        
        // 9) t10 = yq + tz
        let t10 = q.y.add(cs, &tz)?;
        // 10) t8 = (t7 - tx) * t6
        let tmp = t7.sub(cs, &tx)?;
        let t8 = tmp.mul(cs, &t6)?;
        // 11) t0 = 2 * yr * t5
        let mut t0 = r.y.mul(cs, &t5)?;
        t0 = t0.double(cs)?;
        // 12) ty = t8 - t0
        let ty = t8.sub(cs, &t0)?;
        // 13) t10 = t10^2 - yq^2 -tz^2
        let qy_squared = q.y.square(cs)?;
        let tz_squared = tz.square(cs)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&qy_squared).add_neg_term(&tz_squared);
        let t10 = t10.square_with_chain(cs, chain)?;
        // 14) t9 = 2 * t9 - t10
        let t9 = t9.double(cs)?.sub(cs, &t10)?;
        // 15) t10 = 2 * tz * yp
        let mut t10 = tz.mul_by_base_field(cs, &p.y)?;
        t10 = t10.double(cs)?; 
        // 17) t1 = - 2 * t6 * xp
        let mut t1 = t6.mul_by_base_field(cs, &p.x)?;
        t1 = t1.negate(cs)?;
        t1 = t1.double(cs)?;
        // 18) line_function := [t10, 0, 0, t1, t9, 0]
        let zero = Fp2::zero(q.x.get_params()); 
        let fp6_x = Fp6::from_coordinates(t10, zero.clone(), zero.clone());
        let fp6_y = Fp6::from_coordinates(t1, t9, zero);

        let mut new_q = <Bn256 as Engine>::G2::from_xyz_unchecked(
            tx.get_value().unwrap(), ty.get_value().unwrap(), tz.get_value().unwrap()
        );
        old_q.add_assign(&old_r);
        assert_eq!(old_q, new_q);

        *acc = PreparedPoint { x: tx, y: ty, z: tz };
        Ok(Fp12::from_coordinates(fp6_x, fp6_y))
    } 

    
    fn miller_loop_postprocess<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        q: &PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>, 
        t: &mut PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>, 
        f: &Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>
    ) -> Result<Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, SynthesisError> {
        let params = q.x.get_params();
        let mut q1 = q.clone();
        q1.x.c1 = q1.x.c1.negate(cs)?;
        let cnst = <Bn256Extension12Params as Extension12Params<<Bn256 as Engine>::Fq>>::Ex6::FROBENIUS_COEFFS_C1[1];
        q1.x = q1.x.mul(cs, &Fp2::constant(cnst, params))?;
        q1.y.c1 = q1.y.c1.negate(cs)?;
        q1.y = q1.y.mul(cs, &Fp2::constant(XI_TO_Q_MINUS_1_OVER_2, params))?;

        let mut q2 = q.clone();
        let cnst = <Bn256Extension12Params as Extension12Params<<Bn256 as Engine>::Fq>>::Ex6::FROBENIUS_COEFFS_C1[2];
        q2.x = q2.x.mul(cs, &Fp2::constant(cnst, params))?;

        let line_eval_1 = Self::add_and_eval(cs, t, &q1, p)?;
        let line_eval_2 = Self::add_and_eval(cs, t, &q2, p)?;
        let mut f = Self::mul_by_sparse_034(cs, &f, &line_eval_1)?;
        f = Self::mul_by_sparse_034(cs, &f, &line_eval_2)?;

        Ok(f)
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
    use rand::{XorShiftRng, SeedableRng, Rng};
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::CurveAffine;

    #[test]
    fn test_miller_loop_for_bn256_curve() {
        const LIMB_SIZE: usize = 80;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);
        let pairing_params = Bn256PairingParams::<Bn256>::new(Bn256HardPartMethod::FuentesCastaneda);

        //let params = generate_optimal_circuit_params_for_bn\let mut rng = rand::thread_rng();
        let mut rng = rand::thread_rng();
        let p_wit: <Bn256 as Engine>::G1Affine = rng.gen();
        let q_wit: <Bn256 as Engine>::G2Affine = rng.gen();
        let miller_loop_wit = Bn256::miller_loop(
            [(&(p_wit.prepare()), &(q_wit.prepare()))].iter(),
        );
        //let pairing_res_wit = Bn256::pairing(p_wit, q_wit);
        let (q_wit_x, q_wit_y) = bellman::CurveAffine::as_xy(&q_wit); 

        let p = AffinePoint::alloc(&mut cs, Some(p_wit), &circuit_params).unwrap();
        let q_x = Fp2::alloc(&mut cs, Some(*q_wit_x), &circuit_params.base_field_rns_params).unwrap();
        let q_y = Fp2::alloc(&mut cs, Some(*q_wit_y), &circuit_params.base_field_rns_params).unwrap();  
        let q_z = Fp2::one(&circuit_params.base_field_rns_params);
        let q = PreparedPoint::from_coordinates(q_x, q_y, q_z);
        
        let counter_start = cs.get_current_step_number();
        //let wrapped_pairing_res = pairing_params.pairing(&mut cs, &p, &q, SAFE_VERSION).unwrap();
        //let mut pairing_res = wrapped_pairing_res.decompress(&mut cs).unwrap();
        let (mut f, mut t) = Bn256PairingParams::miller_loop(&mut cs, &p, &q).unwrap();
        f = Bn256PairingParams::miller_loop_postprocess(&mut cs, &p, &q, &mut t, &f).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        let mut actual_pairing_res = Fp12::alloc(
            &mut cs, Some(miller_loop_wit), &circuit_params.base_field_rns_params
        ).unwrap();
        Fp12::enforce_equal(&mut cs, &mut f, &mut actual_pairing_res).unwrap();

        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_final_exp_for_bn256_curve() {
        const LIMB_SIZE: usize = 80;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);
        let pairing_params = Bn256PairingParams::<Bn256>::new(Bn256HardPartMethod::FuentesCastaneda);

        //let params = generate_optimal_circuit_params_for_bn\let mut rng = rand::thread_rng();
        let mut rng = rand::thread_rng();
        let f_wit: <Bn256 as Engine>::Fqk = rng.gen();
        let exp_wit = Bn256::final_exponentiation(&f_wit);

        let mut f = Fp12::alloc(&mut cs, Some(f_wit), &circuit_params.base_field_rns_params).unwrap();
        let mut actual_exp = Fp12::alloc(&mut cs, exp_wit, &circuit_params.base_field_rns_params).unwrap();
        
        let counter_start = cs.get_current_step_number();
        let mut wrapped = Bn256PairingParams::final_exp_easy_part(&mut cs, &mut f, SAFE_VERSION).unwrap();
        wrapped = pairing_params.final_exp_hard_part(&mut cs, &wrapped, SAFE_VERSION).unwrap();
        let mut exp = wrapped.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);

        println!("exp val: {}", wrapped.value.unwrap());
        println!("actual val: {}", actual_exp.get_value().unwrap());
        
        Fp12::enforce_equal(&mut cs, &mut exp, &mut actual_exp).unwrap();

        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_pairing_for_bn256_curve() {
        const LIMB_SIZE: usize = 80;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);
        let pairing_params = Bn256PairingParams::<Bn256>::new(Bn256HardPartMethod::FuentesCastaneda);

        //let params = generate_optimal_circuit_params_for_bn\let mut rng = rand::thread_rng();
        let mut rng = rand::thread_rng();
        let p_wit: <Bn256 as Engine>::G1Affine = rng.gen();
        let q_wit: <Bn256 as Engine>::G2Affine = rng.gen();
        let mut res_wit = Bn256::pairing(p_wit, q_wit);
        //let pairing_res_wit = Bn256::pairing(p_wit, q_wit);
        // for Fuentes Castaneda we should additionally raise the result to the power
        // m = = 2x * (6*x^2 + 3 * x + 1)
        let mut lhs = BigUint::from(BN_U);
        lhs = lhs * 2u64;
        let mut rhs = BigUint::from(BN_U);
        rhs = rhs.clone() * rhs.clone() * 6u64 + rhs.clone() * 3u64 + 1u64;
        let x = lhs * rhs;
        res_wit = res_wit.pow(&x.to_u64_digits());
        // let res_wit = {
        //     let mut f = res_wit;
        //     let x = BN_U;

        //     fn exp_by_x(f: &mut Fq12, x: u64) {
        //         *f = f.pow(&[x]);
        //     }
            
        //     let mut f_by_x = f.clone();
        //     exp_by_x(&mut f_by_x, x);

        //     let mut f_by_2_x = f_by_x.clone();
        //     f_by_2_x.square();

        //     let mut f_by_6_x =  f_by_2_x.clone();
        //     f_by_6_x.square();
        //     f_by_6_x.square();
        //     f_by_2_x.conjugate();
        //     f_by_6_x.mul_assign(&f_by_2_x);

        //     let mut a = f_by_6_x.clone();
        //     exp_by_x(&mut a, x);
        //     let mut b = a.clone();
        //     exp_by_x(&mut b, x);

        //     let mut res = f_by_6_x.clone();
        //     res.mul_assign(&a);
        //     res.mul_assign(&b);
        //     f_by_x.conjugate();
        //     res.mul_assign(&f_by_x);
        //     f.conjugate();
        //     res.mul_assign(&f);
        //     f
        // };


        let (q_wit_x, q_wit_y) = bellman::CurveAffine::as_xy(&q_wit); 

        let p = AffinePoint::alloc(&mut cs, Some(p_wit), &circuit_params).unwrap();
        let q_x = Fp2::alloc(&mut cs, Some(*q_wit_x), &circuit_params.base_field_rns_params).unwrap();
        let q_y = Fp2::alloc(&mut cs, Some(*q_wit_y), &circuit_params.base_field_rns_params).unwrap();  
        let q_z = Fp2::one(&circuit_params.base_field_rns_params);
        let q = PreparedPoint::from_coordinates(q_x, q_y, q_z);
        
        let counter_start = cs.get_current_step_number();
        let wrapped_res = pairing_params.pairing(&mut cs, &p, &q, SAFE_VERSION).unwrap();
        let mut res = wrapped_res.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        let mut actual_pairing_res = Fp12::alloc(
            &mut cs, Some(res_wit), &circuit_params.base_field_rns_params
        ).unwrap();
        Fp12::enforce_equal(&mut cs, &mut res, &mut actual_pairing_res).unwrap();

        assert!(cs.is_satisfied()); 
    }
}




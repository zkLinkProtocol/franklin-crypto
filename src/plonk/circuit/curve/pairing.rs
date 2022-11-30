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

    pub fn frobenius_power_map<CS: ConstraintSystem<E>>(
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

    fn pairing<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        base_point: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        ext_point: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, G::Base, T>, SynthesisError>;
        
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

    // implementaiion of sparse multiplication by element c = [c0, 0, 0, c3, c4, 0]
    fn mul_by_sparse_034<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        full_elem: &Fp12<'a, E, G::Base, T>,
        sparse_elem: &Fp12<'a, E, G::Base, T>
    ) -> Result<Fp12<'a, E, G::Base, T>, SynthesisError> {
        let z_coordinates: Vec<_> = full_elem.get_base_field_coordinates().chunks(2).map(|ch| {
            Fp2::from_coordinates(ch[0].clone(), ch[1].clone())
        }).collect();
        let x_coordinates : Vec<Fp2<E, G::Base, <T::Ex6 as Extension6Params<G::Base>>::Ex2>> = {
            sparse_elem.get_base_field_coordinates().chunks(2).map(
                |ch| Fp2::from_coordinates(ch[0].clone(), ch[1].clone())
            ).collect()
        };
        for idx in [1, 2, 5].iter() {
            assert!(x_coordinates[*idx].is_constant());
            assert!(x_coordinates[*idx].get_value().unwrap().is_zero());
        }

        // we assume that non_residue = -1
        assert!(<T::Ex6 as Extension6Params<G::Base>>::Ex2::is_default_impl());

        // c0 = x0 * z0 - x3 * z5 - x4 * z4
        // c1 = x0 * z1 + x3 * z3 - x4 * z5 
        // c2 = x0 * z2 + x3 * z4 + x4 * z3
        // c3 = x0 * z3 + x3 * z0 - x4 * z2
        // c4 = x0 * z4 + x3 * z1 + x4 * z0
        // c5 = x0 * z5 + x3 * z2 + x4 * z1
        let mut comb = |idxs: [usize; 3], signs: [i64; 2]| -> Result<
            Fp2<'a, E, G::Base, <T::Ex6 as Extension6Params<G::Base>>::Ex2>, SynthesisError
        > {
            let tmp0 = x_coordinates[3].mul(cs, &z_coordinates[idxs[1]])?;
            let tmp1 = x_coordinates[4].mul(cs, &z_coordinates[idxs[2]])?;
            let mut chain = Fp2Chain::new();
            if signs[0] == 1 { chain.add_pos_term(&tmp0) } else { chain.add_neg_term(&tmp0) };
            if signs[1] == 1 { chain.add_pos_term(&tmp1) } else { chain.add_neg_term(&tmp1) };
            Fp2::mul_with_chain(cs, &x_coordinates[0], &z_coordinates[idxs[0]], chain)
        };

        let c0 = comb([0, 5, 4], [-1, -1])?;
        let c1 = comb([1, 3, 5], [1, -1])?;
        let c2 = comb([2, 4, 3], [1, 1])?;
        let c3 = comb([3, 0, 2], [1, -1])?;
        let c4 = comb([4, 1, 0], [1, 1])?;
        let c5 = comb([5, 2, 1], [1, 1])?;

        let fp6_x = Fp6::from_coordinates(c0, c1, c2);
        let fp6_y = Fp6::from_coordinates(c3, c4, c5);
        Ok(Fp12::from_coordinates(fp6_x, fp6_y))
    }

    fn miller_loop<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        p: &AffinePoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>,
        q: &PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>
    ) -> Result<
        (Fp12<'a, E, G::Base, T>, PreparedPoint<'a, E, G, <T::Ex6 as Extension6Params<G::Base>>::Ex2>), 
        SynthesisError
    > {
        let params = &p.circuit_params.base_field_rns_params;
        let mut f = Fp12::one(params);
        let mut t = q.clone();

        for bit in Self::get_miller_loop_scalar_decomposition().into_iter().rev() {
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


impl<E: Engine> PairingParams<E, <Bn256 as Engine>::G1Affine, Bn256Extension12Params> for Bn256PairingParams<E> {
    fn get_x() -> BigUint {
        BigUint::from_str("6518589491078791937").expect("should parse")
    }

    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize) {
        match self.hard_part_method {
            Bn256HardPartMethod::Devegili => Self::devegili_method(),
            Bn256HardPartMethod::FuentesCastaneda => Self::fuentes_castaneda_method(),
        }
    }

    fn get_miller_loop_scalar_decomposition() -> Vec<i64> {
        vec![
            0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
	        1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1
        ]
    }
    
    fn pairing<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        q: &PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, SynthesisError> {
        // based on "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves"
        // by Jean-Luc Beuchat et. al. (Algorithm 1)
        let (mut f, mut t) = <Self as PairingParams<E, _, _>>::miller_loop(cs, p, q)?;
        // Q1 <- Frob(Q); Q2 <- Frob^2(Q);
        // f <- f · l_{T ,Q1}(P), T = T + Q1
        // f <- f * l_{T, Q2}(O), T = T - Q2
        let q1 = q.frobenius_power_map(cs, 1)?;
        let mut q2 = q.frobenius_power_map(cs, 2)?;
        q2 = q2.negate(cs)?;
        let line_eval_1 = Self::add_and_eval(cs, &mut t, &q1, p)?;
        let line_eval_2 = Self::add_and_eval(cs, &mut t, &q2, p)?;
        f = Self::mul_by_sparse_034(cs, &f, &line_eval_1)?;
        f = Self::mul_by_sparse_034(cs, &f, &line_eval_1)?;
        let wrapped_f = Self::final_exp_easy_part(cs, &mut f, is_safe_version)?;
        self.final_exp_hard_part(cs, &wrapped_f, is_safe_version)
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
        let tmp4 = tmp3.scale(cs, 3)?;
        // 7. tmp6 := X + tmp4;
        let tmp6 = q.x.add(cs, &tmp4)?;
        // 8. tmp5 := tmp4^2
        let tmp5 = tmp4.square(cs)?;
        // 9.  X3 := tmp5 - 2tmp3
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
        // 15. tmp6 := tmp6^2 - tmp0 - tmp5 - 4 * tmp1
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&tmp0).add_neg_term(&tmp5).add_neg_term(&tmp1.scale(cs, 4)?);
        let tmp6 = tmp6.square_with_chain(cs, chain)?;
        // 16. tmp0 := tmp0 * yp (mul ny base Field)
        let tmp0 = tmp0.mul_by_base_field(cs, &p.y)?;
        // 17. line_function := [tmp0, 0, 0, tmp3, tmp6, 0]
        let zero = Fp2::zero(q.x.get_params()); 
        let fp6_x = Fp6::from_coordinates(tmp0, zero.clone(), zero.clone());
        let fp6_y = Fp6::from_coordinates(tmp3, tmp6, zero);
        Ok(Fp12::from_coordinates(fp6_x, fp6_y))
    }

    fn add_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        q: &mut PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>, 
        r: &PreparedPoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>
    ) -> Result<Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, SynthesisError> {
        // TODO: invetigate comparison between this approach and using formulas from projective curve crate
        // High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves" (alg. 27)
        // Q = (xq : yq : zq), R = (xr : yr : 1) and P = (xp, yp), T = Q + R = (xt: yt: zt)
        // 1) t2 = xq - xr
        let t2 = q.x.sub(cs, &x.r)?;
        // 2) t4 = 4 * t2^2
        let mut t4 = t2.square(cs)?;
        t4 = t4.scale(cs, 4)?;
        // 3) t5 = t4 * t2
        let t5 = t4.mul(cs, &t2);
        // 4) t6 = 2 * (yq - yr)
        let mut t6 = q.y.sub(cs, &r.y)?;
        t6 = t6.double(cs)?;
        // 5) t9 = t6 * xq
        let t9 = t6.mul(cs, &q.x)?;
        // 6) t7 = xr * t4
        let t7 = r.x.mul(cs, &t4)?;
        // 7) tx = t6^2 - t5 - 2 * t7
        let mut chain = Fp2::new();
        chain.add_neg_term(&t5).add_neg_term(&t7.double(cs)?);
        let tx = t6.square_with_chain(cs, chain)?;
        // 8) tz = t2^2 + 2 * t2 - t3
        let mut chain = Fp2::new();
        chain.add_neg_term(&t3).add_pos_term(&t2.double(cs)?);
        let tz = t2.square_with_chain(cs, chain)?;
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
        // 14) t9 = 2 * t9 - t10
        // 15) t10 = 2 * new_z * yp
        // 16) t6 = -t6
        // 17) t1 = 2 * t6 * xp
    } 
}




use super::*;
use crate::bellman::pairing::bn256::*;
use crate::bellman::pairing::bls12_381::*;
use crate::plonk::circuit::BigUint;
use crate::plonk::circuit::bigint::*;
use crate::bellman::SynthesisError;
use crate::bellman::ScalarEngine;
use crate::plonk::circuit::Engine;
use crate::bellman::GenericCurveAffine;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Field, PrimeField};
use crate::plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;
use crate::plonk::circuit::boolean::Boolean;
use rand::{Rng, SeedableRng};
use rand::chacha::ChaChaRng;
use bellman::bls12_381::fq::XI_TO_Q_MINUS_1_OVER_2_;

use crate::bellman::pairing::bn256::Fq12 as Bn256Fq12;

use crate::bellman::pairing::bls12_381::Fq12 as Bls12Fq12;

use std::str::FromStr;

#[derive(Clone, Copy, Debug)]
pub enum Ops {
    // first output, then inputs
    ExpByX(usize, usize), 
    Mul(usize, usize, usize),
    Square(usize, usize),
    Conj(usize, usize),
    Frob(usize, usize, usize), // the last parameter is power
    ExpByHalfOfX(usize, usize) // exist special chain for bls12 so we need this ops
}


pub struct MillerLoopResult<'a, E: Engine, F: PrimeField, G2, T12, T6, T2>
where T12: Extension12Params<F, Ex6 = T6>, T6: Extension6Params<F, Ex2 = T2>, T2: Extension2Params<F>, 
G2: GenericCurveAffine<Base = T2::Witness>
{
    pub fp12_acc: Fp12<'a, E, F, T12>, 
    pub twisted_point_acc: TwistedCurvePoint<'a, E, G2, F, T2>,
    pub twisted_point_init_doubled: TwistedCurvePoint<'a, E, G2, F, T2>
}

pub enum LineFunctionEvaluation<'a, E: Engine, F: PrimeField, T: Extension2Params<F>> {
    DTwist{
        c0: FieldElement<'a, E, F>,
        c3: Fp2<'a, E, F, T>,
        c4: Fp2<'a, E, F, T>,
    },
    MTwist{
        c0: Fp2<'a, E, F, T>,
        c1: Fp2<'a, E, F, T>,
        c4: FieldElement<'a, E, F>,
    }
}

impl<'a, E: Engine, F: PrimeField, T: Extension2Params<F>> LineFunctionEvaluation<'a, E, F, T> {

    fn construct<
        CS: ConstraintSystem<E>, G1: GenericCurveAffine<Base = F>, G2: GenericCurveAffine<Base = T::Witness>
    >(
        twist_type: &TwistType,
        cs: &mut CS,
        q: &TwistedCurvePoint<'a, E, G2, F, T>,
        p: &AffinePoint<'a, E, G1, T>,
        lambda: &Fp2<'a, E, F, T>, 
    ) -> Result<Self, SynthesisError> {

        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&q.y);       // y_Q
        let t1 = Fp2::mul_with_chain(cs, &lambda, &q.x, chain)?;   // lambda * x_Q - y_Q

        let mut t0 = lambda.mul_by_base_field(cs, &p.x)?;      // lambda * x_P
        t0 = t0.negate(cs)?;      //  - lambda * x_P

        match twist_type {
            TwistType::DTwist => {
                Ok(LineFunctionEvaluation::DTwist {
                    c0: p.y.clone(),
                    c3: t0,
                    c4: t1
                })
            }
            TwistType::MTwist =>{
                Ok(LineFunctionEvaluation::MTwist {
                    c0: t1,
                    c1: t0,
                    c4: p.y.clone()
                })
            }
        }
    }
}


pub trait PairingParams<
    E: Engine, F: PrimeField, G1, G2, T12, T6, T2
>  
where T12: Extension12Params<F, Ex6 = T6>, T6: Extension6Params<F, Ex2 = T2>, T2: Extension2Params<F>, 
G1: GenericCurveAffine<Base = F>, G2: GenericCurveAffine<Base = T2::Witness>
{
    fn get_type_twist(&self) -> TwistType;
    fn get_x() -> BigUint;
    fn get_x_ternary_decomposition() -> &'static [i64]; 
    fn get_half_x_ternary_decomposition() -> &'static [i64]; 
    fn get_miller_loop_scalar_decomposition() -> &'static [i8]; 
    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize);
    fn get_hard_part_generator() -> T12::Witness;
    fn g1_subgroup_check<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, p: &AffinePoint<'a, E, G1, T2>
    ) -> Result<Boolean, SynthesisError>;

    
    // require: Q \in E(Fq2) and P \in E(Fq),
    // ensure: T = 2Q and l_Q,Q(P) \in Fq12 , where l_Q,Q is tangent line to the curve at Q
    fn double_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        twist_type: &TwistType,
        q: &mut TwistedCurvePoint<'a, E, G2, F, T2>, 
        p: &AffinePoint<'a, E, G1, T2>,
    ) -> Result<LineFunctionEvaluation<'a, E, F, T2>, SynthesisError> {
        let (doubled_q, lambda) = q.double_and_return_slope(cs)?;
        *q = doubled_q;
        LineFunctionEvaluation::construct(twist_type, cs, q, p, &lambda)
    }

    // require: Q, R \in E(Fq2) and P \in E(Fp),
    // ensure: T = Q + R and l_R,Q(P) \in Fp12 , where l is a unique line function passing through R and Q
    fn add_and_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        twist_type: &TwistType,
        q: &mut TwistedCurvePoint<'a, E, G2, F, T2>, 
        r: &TwistedCurvePoint<'a, E, G2, F, T2>,
        p: &AffinePoint<'a, E, G1, T2>,
    ) -> Result<LineFunctionEvaluation<'a, E, F, T2>, SynthesisError> {
        let (new_q, lambda) = q.add_unequal_unchecked_and_return_slope(cs, r)?;
        *q = new_q;
        LineFunctionEvaluation::construct(twist_type, cs, q, p, &lambda)
    }

    fn final_exp_easy_part<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &mut Fp12<'a, E, F, T12>, is_safe_version: bool
    ) -> Result<(TorusWrapper<'a, E, F, T12>, Boolean), SynthesisError> {
        // easy part: result = f^((q^6-1)*(q^2+1))
        // we use that one-time torus compression cost can be absorbed directly in the easy part computation as follows:
        // let m = m0 + w * m1 \in Fp12 be the Miller loop result, then:
        // m^{p^6−1} = (m0 + w*m1)^{p^6−1} = (m0 + w*m1)^{p^6} / (m0 + w*m1) = (m0 − w*m1)/(m0 + w*m1) = 
        // = (−m0/m1 + w)/(−m0/m1 − w) = Dec(-m0/m1)
        // hence: Enc(m^{(p^6-1)(p^2+1)}) = Enc(Dec(-m0/m1)^{p^2+1}) = (-m0/m1)^{p^2+1} = [[(-m0/m1)^{p^2) * (-m0/m1)]]
        // where all multiplications and power-maps inside [[ ]] are treated as operations on T2
        let params = elem.get_params();

        // we need to implement custom conversion m = m0 + w * m1 \in Fp12 -> -m0/m1 \in T2
        // if m1 == 0 \them m actually belongs to \Fp6, and hence m^{p^6−1} = 1
        // in this case we replace m by generator of order d = hard_part_exp
        let (elem, is_exceptional) = if is_safe_version {
            let is_exceptional = Fp6::is_zero(&mut elem.c1, cs)?;
            let new_c1 = Fp6::conditionally_select(cs, &is_exceptional, &Fp6::one(params), &elem.c1)?;
            let elem = Fp12::from_coordinates(elem.c0.clone(), new_c1);
            (elem, is_exceptional)
        } else {
            (elem.clone(), Boolean::Constant(false))
        };
        
        // actual value of compressed element is (m0 − w*m1)/(m0 + w*m1)
        // the result of Miller loop belongs to Fp12* and hence is never zero, 
        // hence m0 and m1 can't be zero simultaneously
        let value = elem.get_value().map(|x| {
            let (c0, mut c1) = T12::convert_from_structured_witness(x);
            c1.negate();
            let mut res = T12::convert_to_structured_witness(c0, c1);
            let x_inv = x.inverse().unwrap();
            res.mul_assign(&x_inv);
            res
        });

        let mut encoding = Fp6::div(cs, &elem.c0, &elem.c1)?;
        encoding = encoding.negate(cs)?;
        let x = TorusWrapper::new(encoding, value);
        
        // now compute x^{p^2} * x
        let mut y = x.frobenius_power_map(cs, 2)?;
        let mut candidate = TorusWrapper::mul(cs, &mut y, &x, is_safe_version)?;
        let (res, enc_is_zero) = candidate.replace_by_constant_if_trivial(cs, Self::get_hard_part_generator())?;
        let is_trivial = Boolean::or(cs, &is_exceptional, &enc_is_zero)?;
        Ok((res, is_trivial))
    }

    fn final_exp_hard_part<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, elem: &TorusWrapper<'a, E, F, T12>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, F, T12>, SynthesisError> {
        let params = elem.get_params();
        let (ops_chain, num_of_variables) = self.get_hard_part_ops_chain();
        let x = Self::get_x();
        let x_half: BigUint = x.clone() >> 1;
        let x_decomposition = Self::get_x_ternary_decomposition();
        let half_of_x_decomposition = Self::get_half_x_ternary_decomposition();
        let mut scratchpad = vec![TorusWrapper::<'a, E, F, T12>::uninitialized(params); num_of_variables];
        scratchpad[0] = elem.clone();
        for (_is_first, is_last, op) in ops_chain.into_iter().identify_first_last() {
            let may_cause_exp = is_safe_version && is_last;
            match op {
                Ops::ExpByX(out_idx, in_idx) => {
                    scratchpad[out_idx] = TorusWrapper::pow(
                        &mut scratchpad[in_idx], cs, &x, &x_decomposition, may_cause_exp
                    )?;
                },
                Ops::ExpByHalfOfX(out_idx, in_idx) => {
                    scratchpad[out_idx] = TorusWrapper::pow(
                        &mut scratchpad[in_idx], cs, &x_half.clone(), &half_of_x_decomposition, may_cause_exp
                    )?;
                },
                Ops::Mul(out_idx, left_idx, right_idx) => {
                    scratchpad[out_idx] = TorusWrapper::mul(
                        cs, &scratchpad[left_idx], &scratchpad[right_idx], may_cause_exp 
                    )?;
                },
                Ops::Square(out_idx, in_idx) => {
                    scratchpad[out_idx] = scratchpad[in_idx].square(cs, may_cause_exp)?;
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

    fn convert_line_function_eval_into_fp12<'a>(x: LineFunctionEvaluation<'a, E, F, T2>) -> Fp12<'a, E, F, T12> {
        if let LineFunctionEvaluation::DTwist{ c0, c3, c4} = x {
            let zero = Fp2::zero(&c0.representation_params); 
            let fp6_x = Fp6::from_coordinates(Fp2::from(c0), zero.clone(), zero.clone());
            let fp6_y = Fp6::from_coordinates(c3, c4, zero);
            Fp12::from_coordinates(fp6_x, fp6_y)
        } else if let LineFunctionEvaluation::MTwist{ c0, c1, c4} = x {
            let zero = Fp2::zero(&c4.representation_params); 
            let fp6_x = Fp6::from_coordinates(c0, c1, zero.clone());
            let fp6_y = Fp6::from_coordinates(zero.clone(), Fp2::from(c4), zero.clone());
            Fp12::from_coordinates(fp6_x, fp6_y)
        } else {
            unreachable!()
        }
    }

    fn mul_by_sparse_01<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, full_elem: &Fp6<'a, E, F, T12::Ex6>, sparse_elem: &Fp6<'a, E, F, T12::Ex6>
    ) -> Result<Fp6<'a, E, F, T12::Ex6>, SynthesisError> {
        let (c0, c1, c2) = full_elem.get_coordinates();
        let (a, b, c) = sparse_elem.get_coordinates();
        assert!(c.is_constant());
        assert!(c.get_value().unwrap().is_zero());
        let alpha = T12::Ex6::non_residue();

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

    // implementaiion of sparse multiplication by element c = [c0, 0, 0, c3, c4, 0] and c = [c0, c1, 0, 0, c4, 0] second one is for bls12
    fn mul_by_line_function_eval<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        full_elem: &Fp12<'a, E, F, T12>,
        x: LineFunctionEvaluation<'a, E, F, T2>
    ) -> Result<Fp12<'a, E, F, T12>, SynthesisError> {
        match x {
            LineFunctionEvaluation::DTwist { c0, c3, c4 } => {
                let z: Vec<Fp2<E, F, <T12::Ex6 as Extension6Params<F>>::Ex2>> = {
                    full_elem.get_base_field_coordinates().chunks(2).map(|ch| {
                        Fp2::from_coordinates(ch[0].clone(), ch[1].clone())
                    }).collect()
                };
                let params = full_elem.get_params();
        
                let fp6_sparse_elem = Fp6::from_coordinates(c3.clone(), c4.clone(), Fp2::zero(params));
                let b = Self::mul_by_sparse_01(cs, &full_elem.c1, &fp6_sparse_elem)?;
        
                let tmp = Fp2::from(c0.clone()).add(cs, &c3)?;
                let fp6_sparse_elem = Fp6::from_coordinates(tmp, c4.clone(), Fp2::zero(params));
                let fp6_full_elem = full_elem.c0.add(cs, &full_elem.c1)?;
                let e = Self::mul_by_sparse_01(cs, &fp6_full_elem, &fp6_sparse_elem)?;
        
                let a0 = z[0].mul_by_base_field(cs, &c0)?;
                let a1 = z[1].mul_by_base_field(cs, &c0)?;
                let a2 = z[2].mul_by_base_field(cs, &c0)?;
                let a = Fp6::from_coordinates(a0, a1, a2);
                
                let mut chain = Fp6Chain::new();
                chain.add_pos_term(&e).add_neg_term(&a).add_neg_term(&b);
                let t1 = Fp6::collapse_chain(cs, chain)?;
            
                let mut t0 = Fp12::<'a, E, F, T12>::fp6_mul_subroutine(cs, &b)?;
                t0 = t0.add(cs, &a)?;
            
                let res = Fp12::from_coordinates(t0, t1);
                Ok(res)
            },
            LineFunctionEvaluation::MTwist { c0, c1, c4 } => {
                let params = full_elem.get_params();

                let x = Fp12::from_coordinates(
                    Fp6::from_coordinates(c0.clone(), c1.clone(), Fp2::zero(params)),
                    Fp6::from_coordinates(Fp2::zero(params), Fp2::from(c4.clone()), Fp2::zero(params))
                );


                Fp12::mul(cs, &x, &full_elem)
            }
        }
        
    }

    fn miller_loop_postprocess<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        twist_type: &TwistType,
        p: &AffinePoint<'a, E, G1, T2>,
        q: &TwistedCurvePoint<'a, E, G2, F, T2>,
        miller_loop_result: MillerLoopResult<'a, E, F, G2, T12, T6, T2>,
        is_safe_version: bool
    ) -> Result<(Fp12<'a, E, F, T12>, Boolean), SynthesisError>;

    fn miller_loop<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        twist_type: &TwistType,
        p: &AffinePoint<'a, E, G1, T2>,
        q: &TwistedCurvePoint<'a, E, G2, F, T2>
    ) -> Result<MillerLoopResult<'a, E, F, G2, T12, T6, T2>, SynthesisError> {
        // we should enforce that addition and doubling in Jacobian coordinates are exception free
        let params = &p.circuit_params.base_field_rns_params;
        let mut f = Fp12::one(params);
        let mut t = q.clone();
        let mut q_doubled = q.clone();

        let iter = Self::get_miller_loop_scalar_decomposition().into_iter().rev().skip(1).identify_first_last();
        for (is_first, _is_last, bit) in iter {
            let line_eval = Self::double_and_eval(cs, twist_type, &mut t, &p)?;
            if is_first {
                f = Self::convert_line_function_eval_into_fp12(line_eval);
                q_doubled = t.clone();
            } else {
                f = f.square(cs)?;
                f = Self::mul_by_line_function_eval(cs, &f, line_eval)?;
            }
           
            let mut to_add = q.clone();
            if *bit == -1 {
                to_add = to_add.negate(cs)?;
            }
            if *bit == 1 || *bit == -1 {
                let line_eval = Self::add_and_eval(cs, twist_type,&mut t, &to_add, &p)?;
                f = Self::mul_by_line_function_eval(cs, &f, line_eval)?;
            }

        }

        Ok(MillerLoopResult {
            fp12_acc: f, 
            twisted_point_acc: t,
            twisted_point_init_doubled: q_doubled
        })
    }

    fn pairing<'a, CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, 
        p: &mut AffinePoint<'a, E, G1, T2>,
        q: &mut TwistedCurvePoint<'a, E, G2, F, T2>,
        is_safe_version: bool
    ) -> Result<(TorusWrapper<'a, E, F, T12>, Boolean), SynthesisError> {
        let mut exception = Boolean::constant(false);
        if is_safe_version {
            let p_is_on_curve_exc = p.check_is_on_curve_and_replace(cs)?;
            let q_is_on_curve_exc = q.check_is_on_curve_and_replace(cs)?;
            let p_is_in_subgroup_exc = Self::g1_subgroup_check(cs, p)?;
            
            for new_exc in [p_is_on_curve_exc, q_is_on_curve_exc, p_is_in_subgroup_exc] {
                exception = Boolean::or(cs, &exception, &new_exc)?;
            }
        } 
        // based on "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves"
        // by Jean-Luc Beuchat et. al. (Algorithm 1)
        let miller_loop_res = Self::miller_loop(cs, &self.get_type_twist(), p, q)?;
        let (mut f, q_is_in_subgroup_exc) = Self::miller_loop_postprocess(
            cs, &self.get_type_twist(), &p, &q, miller_loop_res, is_safe_version
        )?;
        let (wrapped_f, is_trivial) = Self::final_exp_easy_part(cs, &mut f, is_safe_version)?;
        let candidate = self.final_exp_hard_part(cs, &wrapped_f, is_safe_version)?;
        
        let res = candidate.mask(cs, &is_trivial.not())?;
        exception = Boolean::or(cs, &exception, &q_is_in_subgroup_exc)?;

        Ok((res, exception))
    }
}


#[derive(Clone, Copy, Debug)]
pub enum TwistType{
    DTwist,
    MTwist
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Bn256HardPartMethod {
    Devegili,
    FuentesCastaneda,
    Naive
}


#[derive(Clone, Debug)]
pub struct Bn256PairingParams<E: Engine> {
    hard_part_method: Bn256HardPartMethod,
    twist: TwistType,
    marker: std::marker::PhantomData<E>
}

impl<E: Engine> Bn256PairingParams<E> {
    fn new(hard_part_method: Bn256HardPartMethod) -> Self {
        Bn256PairingParams {
            hard_part_method,
            twist: TwistType::DTwist, 
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
    // 1) fp = frob(f, 1)         8) fu2p = fu2^p               15) y6 = conj(fu3 * fu3p)       22) t0 = t1 * y1
    // 2) fp2 = frob(f, 2)        9) fu3p = fu3^p               16) y6 = y6^2 * y4 * y5         23) t1 = t1 * y0
    // 3) fp3 = frob(fp2, 1)     10) y2 = frob(fu2, 2)          17) t1 = y3 * y5 * y6           24) t0 = t0^2
    // 4) fu = f^x               11) y0 = fp * fp2 * fp3        18) y6 = y6 * y2                25) f = t0 * t1
    // 5) fu2 = fu^x             12) y1 = conj(f)               19) t1 = t1^2
    // 6) fu3 = fu2^x            13) y5 = conj(fu2)             20) t1 = t1 * y6
    // 7) y3 = conj(fu^p)        14) y4 = conj(fu * fu2p)       21) t1 = t1^2
    fn naive_method() -> (Vec<Ops>, usize) {
        let (f, fp, tmp, fp2, fp3, fu, fu2, fu3, y3, fu2p, fu3p, y2, y0, y1, y4, y5, y6, t0, t1) = (
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
        let ops_chain = vec![
            /*1*/ Ops::Frob(fp, f, 1), /*2*/ Ops::Frob(fp2, f, 2), /*3*/ Ops::Frob(fp3, fp2, 1), 
            /*4*/ Ops::ExpByX(fu, f), /*5*/ Ops::ExpByX(fu2, fu), /*6*/ Ops::ExpByX(fu3, fu2), 
            /*7*/ Ops::Frob(tmp, fu, 1), Ops::Conj(y3, tmp), /*8*/ Ops::Frob(fu2p, fu2, 1), 
            /*9*/ Ops::Frob(fu3p, fu3, 1), /*10*/ Ops::Frob(y2, fu2, 2), /*11*/ Ops::Mul(tmp, fp, fp2), 
            Ops::Mul(y0, tmp, fp3), /*12*/ Ops::Conj(y1, f), /*13*/ Ops::Conj(y5, fu2), /*14*/ Ops::Mul(tmp, fu, fu2p),
            Ops::Conj(y4, tmp), /*15*/ Ops::Mul(tmp, fu3, fu3p), Ops::Conj(y6, tmp), /*16*/ Ops::Square(tmp, y6), 
            Ops::Mul(tmp, tmp, y4), Ops::Mul(y6, tmp, y5), /*17*/ Ops::Mul(tmp, y3, y5), Ops::Mul(t1, tmp, y6), 
            /*18*/ Ops::Mul(y6, y2, y6), /*19*/ Ops::Square(t1, t1), /*20*/ Ops::Mul(t1, t1, y6), 
            /*21*/ Ops::Square(t1, t1), /*22*/ Ops::Mul(t0, t1, y1), /*23*/ Ops::Mul(t1, t1, y0), 
            /*24*/ Ops::Square(t0, t0), /*25*/ Ops::Mul(f, t0, t1)
        ];
        (ops_chain, 19)
    }
}


use std::sync::Once;
static INIT_HARD_PART_GEN: Once = Once::new();
static mut HARD_PART_GEN: Option<Bn256Fq12> = None;


impl<E: Engine> PairingParams<
    E, <Bn256 as Engine>::Fq, <Bn256 as Engine>::G1Affine, <Bn256 as Engine>::G2Affine, Bn256Extension12Params, 
    Bn256Extension6Params, Bn256Extension2Params
> for Bn256PairingParams<E> {
    fn get_type_twist(&self) -> TwistType{
        self.twist
    }
    fn get_x() -> BigUint {
        BigUint::from_str("4965661367192848881").expect("should parse")
    }

    fn get_x_ternary_decomposition() -> &'static [i64] {
        const ARR : [i64; 63] =  [
            1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 
            1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1
        ];
        &ARR
    }
    
    fn get_miller_loop_scalar_decomposition() -> &'static [i8] {
        &SIX_U_PLUS_2_NAF
    } 
    
    fn get_half_x_ternary_decomposition() -> &'static [i64] {
        const ARR : [i64; 62] =  [
            1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 
            1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0
        ];
        &ARR
    }


    fn get_hard_part_generator() -> Bn256Fq12 {
        unsafe {
            INIT_HARD_PART_GEN.call_once(|| {
                let mut rng = ChaChaRng::from_seed(&[42]);
                let mut found = false;
                let chains = [
                    Bn256PairingParams::<Bn256>::devegili_method(), 
                    Bn256PairingParams::<Bn256>::fuentes_castaneda_method(),
                    Bn256PairingParams::<Bn256>::naive_method()
                ];
                let x = Self::get_x();

                while !found {
                    let cand: Bn256Fq12 = rng.gen();
                    if cand == Bn256Fq12::one() {
                        continue;
                    }
                    for (ops_chain, num_of_variables) in chains.iter() {
                        let mut scratchpad = vec![Bn256Fq12::zero(); *num_of_variables];
                        scratchpad[0] = cand.clone();
                        for op in ops_chain.into_iter() {
                            let out_idx = match op {
                                Ops::ExpByX(out_idx, in_idx) => {
                                    scratchpad[*out_idx] = scratchpad[*in_idx].pow(x.to_u64_digits());
                                    out_idx
                                },
                                Ops::ExpByHalfOfX(out_idx, in_idx) => {
                                    unimplemented!("we don't need that")
                                },
                                Ops::Mul(out_idx, left_idx, right_idx) => {
                                    let mut tmp = scratchpad[*left_idx];
                                    tmp.mul_assign(&scratchpad[*right_idx]);
                                    scratchpad[*out_idx] = tmp;
                                    out_idx
                                },
                                Ops::Square(out_idx, in_idx) => {
                                    let mut tmp = scratchpad[*in_idx];
                                    tmp.square();
                                    scratchpad[*out_idx] = tmp;
                                    out_idx
                                },
                                Ops::Conj(out_idx, in_idx) => {
                                    let mut tmp = scratchpad[*in_idx];
                                    tmp.conjugate();
                                    scratchpad[*out_idx] = tmp;
                                    out_idx
                                },
                                Ops::Frob(out_idx, in_idx, power) => {
                                    let mut tmp = scratchpad[*in_idx];
                                    tmp.frobenius_map(*power); 
                                    scratchpad[*out_idx] = tmp;
                                    out_idx
                                },
                            };
                            
                            if scratchpad[*out_idx] == Bn256Fq12::one() {
                                continue;
                            }
                        }
                    }

                    found = true;
                    HARD_PART_GEN = Some(cand);
                };
            });
            HARD_PART_GEN.unwrap()
        }
    }

    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize) {
        match self.hard_part_method {
            Bn256HardPartMethod::Devegili => Self::devegili_method(),
            Bn256HardPartMethod::FuentesCastaneda => Self::fuentes_castaneda_method(),
            Bn256HardPartMethod::Naive => Self::naive_method()
        }
    }

    fn g1_subgroup_check<'a, CS: ConstraintSystem<E>>(
        _cs: &mut CS, _p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>
    ) -> Result<Boolean, SynthesisError> {
        Ok(Boolean::constant(false))
    }
    
    fn miller_loop_postprocess<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        twist_type: &TwistType,
        p: &AffinePoint<'a, E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>,
        q: &TwistedCurvePoint<'a, E, <Bn256 as Engine>::G2Affine, <Bn256 as Engine>::Fq, Bn256Extension2Params>,
        miller_loop_result: MillerLoopResult<
            'a, E, <Bn256 as Engine>::Fq, <Bn256 as Engine>::G2Affine, Bn256Extension12Params, 
            Bn256Extension6Params, Bn256Extension2Params
        >, 
        is_safe_version: bool,
    ) -> Result<(Fp12<'a, E, <Bn256 as Engine>::Fq, Bn256Extension12Params>, Boolean), SynthesisError> {
        let MillerLoopResult { 
            fp12_acc, twisted_point_acc, twisted_point_init_doubled 
        } = miller_loop_result;
        let mut acc = fp12_acc;
        let mut t = twisted_point_acc;
        let mut r_pt = t.clone();
        let params = q.x.get_params();

        // The twist isomorphism is (x', y') -> (xω², yω³). If we consider just
	    // x for a moment, then after applying the Frobenius, we have x̄ω^(2p)
	    // where x̄ is the conjugate of x. If we are going to apply the inverse
	    // isomorphism we need a value with a single coefficient of ω² so we
	    // rewrite this as x̄ω^(2p-2)ω². ξ⁶ = ω and, due to the construction of
	    // p, 2p-2 is a multiple of six. Therefore we can rewrite as
	    // x̄ξ^((p-1)/3)ω² and applying the inverse isomorphism eliminates the ω².
	    // A similar argument can be made for the y value.
        let mut q_frob = q.clone();
        q_frob.x.c1 = q_frob.x.c1.negate(cs)?;
        let cnst = <Bn256Extension12Params as Extension12Params<<Bn256 as Engine>::Fq>>::Ex6::FROBENIUS_COEFFS_C1[1];
        q_frob.x = q_frob.x.mul(cs, &Fp2::constant(cnst, params))?;
        q_frob.y.c1 = q_frob.y.c1.negate(cs)?;
        q_frob.y = q_frob.y.mul(cs, &Fp2::constant(XI_TO_Q_MINUS_1_OVER_2, params))?;
      
        let mut q2 = q.clone();
        let cnst = <Bn256Extension12Params as Extension12Params<<Bn256 as Engine>::Fq>>::Ex6::FROBENIUS_COEFFS_C1[2];
        q2.x = q2.x.mul(cs, &Fp2::constant(cnst, params))?;

        let line_eval_1 = Self::add_and_eval(cs, twist_type, &mut t, &q_frob, p)?;
        let line_eval_2 = Self::add_and_eval(cs, twist_type, &mut t, &q2, p)?;
        acc = Self::mul_by_line_function_eval(cs, &acc, line_eval_1)?;
        acc = Self::mul_by_line_function_eval(cs, &acc, line_eval_2)?;

        let q2_subgroup_exception = if is_safe_version {
            // subgroup check for BN256 curve is of the form: twisted_frob(Q) = [6*u^2]*Q
            r_pt = r_pt.sub_unequal_unchecked(cs, &twisted_point_init_doubled)?;
            let r_pt_negated = r_pt.negate(cs)?;
            let mut acc = r_pt.clone();
            for bit in Self::get_x_ternary_decomposition().into_iter().skip(1) {
                if *bit == 0 {
                    acc = acc.double(cs)?;
                } else {
                    let to_add = if *bit == 1 { &r_pt } else { &r_pt_negated };
                    acc = acc.double_and_add_unequal_unchecked(cs, to_add)?;  
                }
            }
            TwistedCurvePoint::equals(cs, &mut acc, &mut q_frob)?.not()
        } else {
            Boolean::constant(false)
        };

        Ok((acc, q2_subgroup_exception))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Bls12HardPartMethod {
    Simple,
    Naive
}
#[derive(Clone, Debug)]
pub struct Bls12PairingParams<E: Engine> {
    hard_part_method: Bls12HardPartMethod,
    twist: TwistType,
    marker: std::marker::PhantomData<E>
}
impl<E: Engine> Bls12PairingParams<E> {
    fn new(hard_part_method: Bls12HardPartMethod) -> Self {
        Bls12PairingParams {
            hard_part_method,
            twist: TwistType::MTwist, 
            marker: std::marker::PhantomData::<E>
        }
    }
    /* This final exp. hard part implemented in https://eprint.iacr.org/2022/1162.pdf
    Since, our x is negative but in our implementation we use positive x_decomposition so after every exp must be conjuctive. Bls12 have such specification
    0. f = conj(f)
    1. t0 = f^2                                         8. t2 = t1^x   t2 = conj(t2)             15. t1 = conj(t1)
    2. t1 = f^x  t1 = conj(t1)                          9. t1 = frob(t1)                         16. t1 = t1 * t2
    3. t2 = conj(f)                                     10. t1 = t1 * t2                         17. t1 = t1 * t0
    4. t1 = t1 * t2                                     11. f = f * t0                           18. f = f * t1
    5. t2 = t1^x   t2 = conj(t2)                        12. t0 = t1^x  t0 = conj(t0)                           
    6. t1 = conj(t1)                                    13. t2 = t0^x  t2 = conj(t2)
    7. t1 = t1 * t2                                     14. t0 = frob(t1, 2)

    */
    fn simple_chain()-> (Vec<Ops>, usize){
        let (f, t0, t1, t2) = (0, 1, 2, 3);


        let ops_chain = vec![
           /*0*/Ops::Conj(f, f), /*1*/ Ops::Square(t0, f), /*2*/ Ops::ExpByX(t1, f), Ops::Conj(t1, t1), /*3*/Ops::Conj(t2, f), /*4*/ Ops::Mul(t1, t1, t2),
           /*5*/ Ops::ExpByX(t2, t1), Ops::Conj(t2, t2), /*6*/ Ops::Conj(t1, t1), /*7*/Ops::Mul(t1, t1, t2), /*8*/ Ops::ExpByX(t2, t1), Ops::Conj(t2, t2), 
           /*9*/ Ops::Frob(t1, t1, 1), /*10*/Ops::Mul(t1, t1, t2), /*11*/Ops::Mul(f, f, t0), /*12*/ Ops::ExpByX(t0, t1), Ops::Conj(t0, t0),
           /*13*/ Ops::ExpByX(t2, t0), Ops::Conj(t2, t2), /*14*/ Ops::Frob(t0, t1, 2), /*15*/Ops::Conj(t1, t1), /*16*/Ops::Mul(t1, t1, t2),
           /*17*/Ops::Mul(t1, t1, t0), /*18*/Ops::Mul(f, f, t1)
        ];
        (ops_chain, 4)
    }

    /* Since, our x is negative but in our implementation we use positive x_decomposition so after every exp must be conjuctive. Bls12 have such specification
    0. f = conj(f)
    1. y0 = f^2                          6. y1 = conj(y1)                   11. y3 = y3*y1              16. y2 = y3^x    y2 = conj(y2)          21. y1 = y1*y2
    2. y1 = y0^x  y1 = conj(y1)          7. y1 = y1*y2                      12. y1 = conj(y1)           17. y2 = y2*y0
    3. y2 = (y1)^x/2  y2 = conj(y2)      8. y2 = y1^x   y2 = conj(y2)       13. y1 = frob(y1, 3)        18. y2 = y2*f
    4. y3 = conj(f)                      9. y3 = y2^x   y3 = conj(y3)       14. y2 = frob(y2, 2)        19. y1 = y1*y2
    5. y1 = y1*y3                        10. y1 = conj(y1)                  15. y1 = y1*y2              20. y2 = frob(y3)
    */
    fn naive_chain()-> (Vec<Ops>, usize){
        let (f, y0, y1, y2, y3) = (0, 1, 2, 3, 4);

        let ops_chain = vec![
            /*0*/Ops::Conj(f, f), /*1*/ Ops::Square(y0, f), /*2*/ Ops::ExpByX(y1, y0), Ops::Conj(y1, y1), /*3*/Ops::ExpByHalfOfX(y2, y1), Ops::Conj(y2, y2),
            /*4*/ Ops::Conj(y3, f), /*5*/ Ops::Mul(y1, y1, y3), /*6*/ Ops::Conj(y1, y1), /*7*/Ops::Mul(y1, y1, y2), /*8*/ Ops::ExpByX(y2, y1), Ops::Conj(y2, y2),
            /*9*/ Ops::ExpByX(y3, y2), Ops::Conj(y3, y3), /*10*/Ops::Conj(y1, y1), /*11*/Ops::Mul(y3, y3, y1), /*12*/ Ops::Conj(y1, y1),
           /*13*/ Ops::Frob(y1, y1, 3), /*14*/ Ops::Frob(y2, y2, 2), /*15*/Ops::Mul(y1, y1, y2), /*16*/ Ops::ExpByX(y2, y3), Ops::Conj(y2, y2),
           /*17*/Ops::Mul(y2, y2, y0), /*18*/Ops::Mul(y2, y2, f), /*19*/Ops::Mul(y1, y1, y2), /*20*/Ops::Frob(y2, y3, 1), /*21*/Ops::Mul(f, y1, y2)
        ];
        (ops_chain, 6)
    }


}


impl<E: Engine> PairingParams<
    E, <Bls12 as Engine>::Fq, <Bls12 as Engine>::G1Affine, <Bls12 as Engine>::G2Affine, Bls12Extension12Params, 
    BLS12Extension6Params, BLS12Extension2Params
> for Bls12PairingParams<E> {
    fn get_type_twist(&self) -> TwistType{
        self.twist
    }
    fn get_x() -> BigUint {
        // positive form, nature for is -15132376222941642752
        BigUint::from_str("15132376222941642752").expect("should parse")
    }
    fn get_x_ternary_decomposition() -> &'static [i64] {
        const ARR : [i64; 64] =  [
            1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        ];
        &ARR
    } 
    fn get_half_x_ternary_decomposition() -> &'static [i64] {
        const ARR : [i64; 63] =  [
            1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        ];
        &ARR
    }
    fn get_miller_loop_scalar_decomposition() -> &'static [i8] {
        const ARR : [i8; 64] =  [

            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
            0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1

        ]; 

        &ARR
    } 

    fn get_hard_part_generator() -> crate::bellman::pairing::bls12_381::Fq12 {
        crate::bellman::pairing::bls12_381::Fq12::one()
    }

    fn get_hard_part_ops_chain(&self) -> (Vec<Ops>, usize) {
        match self.hard_part_method {
            Bls12HardPartMethod::Simple => Self::simple_chain(),
            Bls12HardPartMethod::Naive => Self::naive_chain()
        }
    }

    fn g1_subgroup_check<'a, CS: ConstraintSystem<E>>(
        _cs: &mut CS, _p: &AffinePoint<'a, E, <Bls12 as Engine>::G1Affine, BLS12Extension2Params>
    ) -> Result<Boolean, SynthesisError> {
        Ok(Boolean::constant(false))
    }

    fn miller_loop_postprocess<'a, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        twist_type: &TwistType,
        p: &AffinePoint<'a, E, <Bls12 as Engine>::G1Affine, BLS12Extension2Params>,
        q: &TwistedCurvePoint<'a, E, <Bls12 as Engine>::G2Affine, <Bls12 as Engine>::Fq, BLS12Extension2Params>,
        miller_loop_result: MillerLoopResult<
            'a, E, <Bls12 as Engine>::Fq, <Bls12 as Engine>::G2Affine, Bls12Extension12Params, 
            BLS12Extension6Params, BLS12Extension2Params
        >, 
        is_safe_version: bool,
    ) -> Result<(Fp12<'a, E, <Bls12 as Engine>::Fq, Bls12Extension12Params>, Boolean), SynthesisError> {
        let MillerLoopResult { 
            fp12_acc, twisted_point_acc, twisted_point_init_doubled 
        } = miller_loop_result;
        let mut t = twisted_point_acc;
        let mut r_pt = t.clone();
        let params = q.x.get_params();


        // The twist isomorphism is (x', y') -> (xω², yω³). If we consider just
	    // x for a moment, then after applying the Frobenius, we have x̄ω^(2p)
	    // where x̄ is the conjugate of x. If we are going to apply the inverse
	    // isomorphism we need a value with a single coefficient of ω² so we
	    // rewrite this as x̄ω^(2p-2)ω². ξ⁶ = ω and, due to the construction of
	    // p, 2p-2 is a multiple of six. Therefore we can rewrite as
	    // x̄ξ^((p-1)/3)ω² and applying the inverse isomorphism eliminates the ω².
	    // A similar argument can be made for the y value.
        let mut q_frob = q.clone();
        q_frob.x.c1 = q_frob.x.c1.negate(cs)?;
        let cnst = <Bls12Extension12Params as Extension12Params<<Bls12 as Engine>::Fq>>::Ex6::FROBENIUS_COEFFS_C1[1];
        q_frob.x = q_frob.x.mul(cs, &Fp2::constant(cnst.inverse().unwrap(), params))?;
        q_frob.y.c1 = q_frob.y.c1.negate(cs)?;
        q_frob.y = q_frob.y.mul(cs, &Fp2::constant(XI_TO_Q_MINUS_1_OVER_2_.inverse().unwrap(), params))?;
      

        let q2_subgroup_exception = if is_safe_version {
            

            let mut r_pt_negated = r_pt.negate(cs)?;
            // println!("                      {:?}", r_pt_negated);
            // println!("                          {:?}", q_frob);
            TwistedCurvePoint::equals(cs, &mut r_pt_negated, &mut q_frob)?.not()
        } else {
            Boolean::constant(false)
        };

        Ok((fp12_acc , q2_subgroup_exception))
    }

}


#[cfg(test)]
mod test {
    use super::*;
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
    use bellman::bls12_381;
    use bellman::GenericCurveProjective;
    use rand::{XorShiftRng, SeedableRng, Rng};
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::CurveAffine;

    #[test]
    fn test_miller_loop_for_bn256_curve() {
        const LIMB_SIZE: usize = 72;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        use plonk::circuit::curve::Bn256HardPartMethod::Naive;
        let type_of_curve = Bn256PairingParams::<Bn256>::new(Naive);
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
        let q = TwistedCurvePoint::from_coordinates(q_x, q_y);
        
        let counter_start = cs.get_current_step_number();
        //let wrapped_pairing_res = pairing_params.pairing(&mut cs, &p, &q, SAFE_VERSION).unwrap();
        //let mut pairing_res = wrapped_pairing_res.decompress(&mut cs).unwrap();
        let partial_res = Bn256PairingParams::miller_loop(&mut cs, &type_of_curve.twist, &p, &q).unwrap();
        let (mut f, _exc) = Bn256PairingParams::miller_loop_postprocess(&mut cs, &type_of_curve.twist, &p, &q, partial_res, SAFE_VERSION).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        let mut actual_pairing_res = Fp12::alloc(
            &mut cs, Some(miller_loop_wit), &circuit_params.base_field_rns_params
        ).unwrap();
        Fp12::enforce_equal(&mut cs, &mut f, &mut actual_pairing_res).unwrap();

        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_miller_loop_for_bls12_curve() {
        const LIMB_SIZE: usize = 72;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bls12, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bls12::<Bls12, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let mut rng = rand::thread_rng();
        let p_wit: bls12_381::G1Affine = rng.gen();
        let q_wit: bls12_381::G2Affine  = rng.gen();
        let miller_loop_wit = Bls12::miller_loop(
            [(&(p_wit.prepare()), &(q_wit.prepare()))].iter(),
        );
        let (q_wit_x, q_wit_y) = bellman::CurveAffine::as_xy(&q_wit); 

        use plonk::circuit::curve::Bn256HardPartMethod::Naive;
        let type_of_curve = Bn256PairingParams::<Bn256>::new(Naive);
        let p = AffinePoint::alloc(&mut cs, Some(p_wit), &circuit_params).unwrap();
        let q_x = Fp2::alloc(&mut cs, Some(*q_wit_x), &circuit_params.base_field_rns_params).unwrap();
        let q_y = Fp2::alloc(&mut cs, Some(*q_wit_y), &circuit_params.base_field_rns_params).unwrap();  
        let q = TwistedCurvePoint::from_coordinates(q_x, q_y);
        
        let counter_start = cs.get_current_step_number();

        let f = Bls12PairingParams::miller_loop(&mut cs, &type_of_curve.twist, &p, &q).unwrap();
        let (mut f, _exc) = Bls12PairingParams::miller_loop_postprocess(&mut cs, &type_of_curve.twist, &p, &q, f, SAFE_VERSION).unwrap();
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
        let (mut wrapped, _) = Bn256PairingParams::final_exp_easy_part(&mut cs, &mut f, SAFE_VERSION).unwrap();
        wrapped = pairing_params.final_exp_hard_part(&mut cs, &wrapped, SAFE_VERSION).unwrap();
        let mut exp = wrapped.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        Fp12::enforce_equal(&mut cs, &mut exp, &mut actual_exp).unwrap();
        assert!(cs.is_satisfied()); 
    }
    #[test]
    fn test_final_exp_for_bls12_curve() {
        const LIMB_SIZE: usize = 72;
        const SAFE_VERSION: bool = true;

        let mut cs = TrivialAssembly::<
            Bls12, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bls12::<Bls12, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);
        let pairing_params = Bls12PairingParams::<Bls12>::new(Bls12HardPartMethod::Naive);

        //let params = generate_optimal_circuit_params_for_bn\let mut rng = rand::thread_rng();
        let mut rng = rand::thread_rng();
        let f_wit: <Bls12 as Engine>::Fqk = rng.gen();
        let exp_wit = Bls12::final_exponentiation(&f_wit);

        let mut f = Fp12::alloc(&mut cs, Some(f_wit), &circuit_params.base_field_rns_params).unwrap();
        let mut actual_exp = Fp12::alloc(&mut cs, exp_wit, &circuit_params.base_field_rns_params).unwrap();
        
        let counter_start = cs.get_current_step_number();
        let (mut wrapped, _) = Bls12PairingParams::final_exp_easy_part(&mut cs, &mut f, SAFE_VERSION).unwrap();
        wrapped = pairing_params.final_exp_hard_part(&mut cs, &wrapped, SAFE_VERSION).unwrap();
        let mut exp = wrapped.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        Fp12::enforce_equal(&mut cs, &mut exp, &mut actual_exp).unwrap();
        assert!(cs.is_satisfied()); 
    }


    fn test_pairing_for_bn256_curve_impl(
        g1_is_const: bool, g2_is_const: bool, limb_size: usize, is_safe_version: bool, 
        hard_part_exp_method: Bn256HardPartMethod
    ) {
        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, limb_size, limb_size);
        let pairing_params = Bn256PairingParams::<Bn256>::new(hard_part_exp_method);

        let mut rng = rand::thread_rng();
        let p_wit: <Bn256 as Engine>::G1Affine = rng.gen();
        let q_wit: <Bn256 as Engine>::G2Affine = rng.gen();
        let mut res_wit = Bn256::pairing(p_wit, q_wit);

        if hard_part_exp_method == Bn256HardPartMethod::FuentesCastaneda {
            // for Fuentes Castaneda we should additionally raise the result to the power
            // m = 2x * (6*x^2 + 3 * x + 1)
            let mut lhs = BigUint::from(BN_U);
            lhs = lhs * 2u64;
            let mut rhs = BigUint::from(BN_U);
            rhs = rhs.clone() * rhs.clone() * 6u64 + rhs.clone() * 3u64 + 1u64;
            let x = lhs * rhs;
            res_wit = res_wit.pow(&x.to_u64_digits());
        }

        let (q_wit_x, q_wit_y) = bellman::CurveAffine::as_xy(&q_wit); 
        let mut p = if g1_is_const {
            AffinePoint::constant(p_wit, &circuit_params)
        } else {
            AffinePoint::alloc(&mut cs, Some(p_wit), &circuit_params).unwrap()
        };
        
        let mut q = if g2_is_const {
            TwistedCurvePoint::constant(q_wit, &circuit_params.base_field_rns_params)
        } else {
            let q_x = Fp2::alloc(&mut cs, Some(*q_wit_x), &circuit_params.base_field_rns_params).unwrap();
            let q_y = Fp2::alloc(&mut cs, Some(*q_wit_y), &circuit_params.base_field_rns_params).unwrap();  
            TwistedCurvePoint::from_coordinates(q_x, q_y)       
        };
        
        let counter_start = cs.get_current_step_number();
        let (wrapped_res, any_exception) = pairing_params.pairing(
            &mut cs, &mut p, &mut q, is_safe_version
        ).unwrap();
        let mut res = wrapped_res.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        
        let total_num_of_gates = counter_end - counter_start;
        let is_const_test = g1_is_const && g2_is_const;
        if is_const_test {
            assert_eq!(total_num_of_gates, 0);
        } else {
            println!("num of gates: {}", total_num_of_gates);
        }
        
        let mut actual_pairing_res = Fp12::alloc(
            &mut cs, Some(res_wit), &circuit_params.base_field_rns_params
        ).unwrap();
        Fp12::enforce_equal(&mut cs, &mut res, &mut actual_pairing_res).unwrap();
        Boolean::enforce_equal(&mut cs, &any_exception, &Boolean::Constant(false)).unwrap();

        assert!(cs.is_satisfied()); 
    }

    fn test_pairing_for_bls12_curve_impl(
        g1_is_const: bool, g2_is_const: bool, limb_size: usize, is_safe_version: bool, 
        hard_part_exp_method: Bls12HardPartMethod
    ) {
        // init cs and params
        let mut cs = TrivialAssembly::<
            Bls12, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bls12::<Bls12, _>(&mut cs, limb_size, limb_size);
        let pairing_params = Bls12PairingParams::<Bls12>::new(hard_part_exp_method);

        // generte points for pairing
        let mut rng = rand::thread_rng();
        let p_wit: <Bls12 as Engine>::G1Affine = rng.gen();
        let q_wit: <Bls12 as Engine>::G2Affine = rng.gen();

        // Compute pairing out of circuit
        let mut res_wit = Bls12::pairing(p_wit, q_wit);

        // Compute pairing in circuit
        let (q_wit_x, q_wit_y) = bellman::CurveAffine::as_xy(&q_wit); 
        let mut p = if g1_is_const {
            AffinePoint::constant(p_wit, &circuit_params)
        } else {
            AffinePoint::alloc(&mut cs, Some(p_wit), &circuit_params).unwrap()
        };
        
        let mut q = if g2_is_const {
            TwistedCurvePoint::constant(q_wit, &circuit_params.base_field_rns_params)
        } else {
            let q_x = Fp2::alloc(&mut cs, Some(*q_wit_x), &circuit_params.base_field_rns_params).unwrap();
            let q_y = Fp2::alloc(&mut cs, Some(*q_wit_y), &circuit_params.base_field_rns_params).unwrap();  
            TwistedCurvePoint::from_coordinates(q_x, q_y)       
        };
        
        let counter_start = cs.get_current_step_number();
        let (wrapped_res, any_exception) = pairing_params.pairing(
            &mut cs, &mut p, &mut q, is_safe_version
        ).unwrap();
        let mut res = wrapped_res.decompress(&mut cs).unwrap();
        let counter_end = cs.get_current_step_number();
        
        let total_num_of_gates = counter_end - counter_start;
        let is_const_test = g1_is_const && g2_is_const;
        if is_const_test {
            assert_eq!(total_num_of_gates, 0);
        } else {
            println!("num of gates: {}", total_num_of_gates);
        }


        // Check results
        let mut actual_pairing_res = Fp12::alloc(
            &mut cs, Some(res_wit), &circuit_params.base_field_rns_params
        ).unwrap();

        Fp12::enforce_equal(&mut cs, &mut res, &mut actual_pairing_res).unwrap();
        Boolean::enforce_equal(&mut cs, &any_exception, &Boolean::Constant(false)).unwrap();

        assert!(cs.is_satisfied()); 
    }
    
    // Naive: num of gates: 1151684
    #[test]
    fn test_pairing_for_bn256_curve_general() {
        test_pairing_for_bn256_curve_impl(false, false, 72, true, Bn256HardPartMethod::Naive)
    }

    #[test]
    fn test_pairing_for_bn256_curve_for_recursion() {
        test_pairing_for_bn256_curve_impl(false, true, 72, false, Bn256HardPartMethod::Naive)
    }

    #[test]
    fn const_propagation_test_for_pairing_for_bn256_curve() {
        test_pairing_for_bn256_curve_impl(true, true, 72, true, Bn256HardPartMethod::Naive)
    }

    // Naive: num of gates: 1852970
    // Simple: num of gates: 1848957
    #[test]
    fn test_pairing_for_bls12_curve_general() {
        test_pairing_for_bls12_curve_impl(false, false, 72, true, Bls12HardPartMethod::Simple)
    }
    #[test]
    fn test_pairing_for_bls12_curve_for_recursion() {
        test_pairing_for_bls12_curve_impl(false, true, 72, false, Bls12HardPartMethod::Naive)
    }

    #[test]
    fn const_propagation_test_for_pairing_for_bls12_curve() {
        test_pairing_for_bls12_curve_impl(true, true, 72, true, Bls12HardPartMethod::Naive)
    }





}




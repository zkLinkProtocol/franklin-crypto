use std::mem::uninitialized;

use super::*;
use crate::plonk::circuit::BigUint;


enum Ops {
    // first output, then inputs
    ExpByX(u64, u64), 
    Mul(u64, u64, u64),
    Square(u64, u64),
    Conv(u64, u64),
    Frob(u64, u64, u64) // the last parameter is power
}


pub trait PairingParams<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> {
    const X: BigUint;
    const NUM_OF_VARS_IN_OPS_CHAIN: usize;
    const HARD_PART_OPS_CHAIN : [Ops];

    fn final_exp_easy_part<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &mut Fp12<'a, E, F, T>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, F, T>, SynthesisError> {
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
            TorusWrapper { encoding, is_negative:  Boolean::Constant(true), is_exceptional}
        } else {
            // the result of Miller loop belongs to Fp12* and hence is never zero, 
            // hence m0 and m1 can't be zero simultaneously
            let encoding = Fp6::div(cs, &elem.c0, &elem.c1)?;
            TorusWrapper { encoding, is_negative: Boolean::Constant(true), is_exceptional: Boolean::constant(false) }
        };

        // now compute x^{p^2} * x
        let mut y = x.frobenius_power_map(cs, 2)?;
        TorusWrapper::mul(cs, &y, &x, is_safe_version)
    }

    fn final_exp_hard_part<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &TorusWrapper<'a, E, F, T>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, F, T>, SynthesisError> {
        let mut scratchpad = [TorusWrapper::<'a, E, F, T>::uninitialized(); Self::NUM_OF_VARS_IN_OPS_CHAIN];
        scratchpad[0] = elem.clone();
        for op in Self::HARD_PART_OPS_CHAIN.iter() {
            match op {
                Ops::ExpByX(u64, u64) => 
                OPs::Mul(u64, u64, u64) =>
                OPs::Square(u64, u64) =>
                OPs::Conv(u64, u64) => 
                OPs::Frob(u64, u64, u64) => 
            }
        };
        
    }
}




#[derive(Clone, Debug)]
pub struct Bn256PairingParams<'a, E> {}
impl PairingParams<'a, E, Bn256Fq, T: Extension12Params<F>> for Bn256PairingParams {
    // let x be parameter parametrizing particular curve in Bn256 family of curves
    // there are two competing agorithms for computing hard part of final exponentiation fot Bn256 family of curves
    // the first one is Devegili method which takes 3exp by x, 11 squaring, 14 muls
    // the second one is Fuentes-Castaneda methid which takes 3exp by x, 4 square, 10 muls and 3 Frobenius powers
    // we implement both of them and will select the most efficient later
    pub fn devegili_method<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &TorusWrapper<'a, E, F, T>, is_safe_version: bool
    ) -> Result<TorusWrapper<'a, E, F, T>, SynthesisError> {
        // 1) a = f^x         7) a = conv(a)       13) t1 = t1^9       19) t0 = frob(f, 2)     25) t0 = t0^x
        // 2) b = a^2         8) b = frob(a)       14) a = t1 * a      20) b = b * t0          26) t0 = t0 * b
        // 3) a = b * f^2     9) b = a * b         15) t1 = f^4        21) t0 = b^x            27) a = t0 * a
        // 4) a = a^2         10) a = a * b        16) a = a * t1      22) t1 = t0^2           28) t0 = frob(f, 3)
        // 5) a = a * b       11) t0 = frob(f)     17) t0 = t0^2       23) t0 = t1^2           29) f = t0 * a
        // 6) a = a * f       12) t1 = t0 * f      18) b = b * t0      24) t0 = t0 * t1
        let {f, a, b} = {0, 1, 2};
        let a = 1;
        let b = 2;
        let ops_arr = [
            /*1*/ Ops::ExpByX(a, f), /*2*/ Ops::Square(b, a), Ops::sqaure(tmp, f), /*3*/ Ops::Mul(a, b, tmp), 
            /*4*/ Ops::Square(a, a), /*5*/ Ops::Mul(a, a, b),  /*6*/ Ops::Mul(a, a, f), /*7*/ Ops::Conv(a, a),
            /*8*/ Ops::Frob(b, a, 1), /*9*/ Ops::Mul(b, b, q)
        ]
       
        // This is Fuentes-Castanead method:
        // 1) a = f^x          5) t = b^x                        9) t = t^2                 13) f = f * frob(t, 3)
        // 2) a = a^2          6) f = f * frob(conv(f), 3)       10) t = t^x                14) f = f * frob(t)
        // 3) b = a^2          7) f = f * t                      11) b = b * t              15) f = f * b
        // 4) b = a * b        8) b = b * t                      12) t = b * conv(a)        16) f = f * frob(b, 2)
    }
}
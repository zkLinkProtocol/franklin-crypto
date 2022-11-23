use super::*;
use super::fp12::*;
use super::fp6::*;


// Let k be positve number (usually taken to be the embedding degree of the curve), 
// p - odd prime number, and q = p^(k/2), F_q^2 = F_q[w] / (w^2 - \gamma), N - is norm function of F_q^2 over F_q
// Let G_q,2 = {m \in F_q^2 : m^{q+1} = 1} = {m = m_0 + \gamma * m_1 \in F_q^2: N(m) = m_0^2 - \gamma * m_1^2} 
// there is a map of G_q,2 / {+1} -> algebraic Torus T_2 defined by:

// compress: 
// m -> (1 + m_0) / m1 if m != {+1, -1}
// -1 -> 0

// decompress:
// g -> (g + w)/(g - w)

// arithmetic in comressed form:
// multiply(g1, g2) = (g1 * g2 + \gamma) / (g1 + g2) (not defined for m = -1 i.e. g = 0)
// inverse(g) = -g (not defined for m = -1 i.e. g = 0)
// square(g) = 1/2 (g + \gamma / g) (not defined for m = -1 i.e. g = 0)
// Frob_power_map(g, i) = g^{p^i} / \gamma^({p^i-1}/2) 

// this module implements exception-free wrapper for G_6,2 which could handle all the values including {-1, +1}
// note, that +1 is encoded as [0; false; true] and -1 is encoded as [0; true; true]
// for all other elements have encodings of the form: [elem; is_negative; false]
// TODO: probably better to make it more generic and work for any field in the towes and not only for Fp12
pub struct TorusWrapper<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> {
    elem: Fp6<'a, E, F, T::Ex6>,
    is_negative: Boolean, // if true the wrapper encodes element -x instead of x
    is_exceptional: Boolean // true for encodings of {+1, -1}
}

impl<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> TorusWrapper<'a, E, F, T> {
    pub fn compress<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &Fp12<'a, E, F, T>, is_safe_version: bool
    ) -> Result<Self, SynthesisError> {
        let res = if is_safe_version {
            // conversion is a bit expensive, but we are okay to pay this one-time-cost
            let is_exceptional = elem.c1.is_zero(cs)?;
            let m0_is_one = 
            // m -> (1 + m_0) / (m1 + is_exceptional) works for all values including
        } else {
            elem.c1.enforce_not_zero();
        };

        Ok(res)
    }

    pub fn decompress<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &Self, bool: is_safe_version
    ) -> Result<Fp12<'a, E, F, T>, SynthesisError> {

    }

    pub fn mul<CS: ConstraintSystem<E>>(
        cs: &mut CS, left: &Self, right: &Self, is_safe_version: bool
    ) -> Result<Self, SynthesisError> {

    }

    pub fn inverse<CS>(&self, cs: &mut CS, is_safe_version: bool) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E> {

    } 

    pub fn square<CS>(&self, cs: &mut CS, is_safe_version: bool) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E> {

    }
    
    pub fn frobenius_power_map<CS>(&self, cs: &mut CS, is_safe_version: bool) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E> {

    } 
}
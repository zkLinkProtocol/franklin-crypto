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
// note, that +1 is encoded as [0; true; true] and -1 is encoded as [0; false; true]
// for all other elements have encodings of the form: [elem; is_negative; false]
// TODO: probably better to make it more generic and work for any field in the towes and not only for Fp12
pub struct TorusWrapper<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> {
    encoding: Fp6<'a, E, F, T::Ex6>,
    is_negative: Boolean, // if true the wrapper encodes element -x instead of x
    is_exceptional: Boolean // true for encodings of {+1, -1}
}

impl<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> TorusWrapper<'a, E, F, T> {
    pub fn compress<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &mut Fp12<'a, E, F, T>, is_safe_version: bool
    ) -> Result<Self, SynthesisError> {
        let params = elem.get_params();
        let res = if is_safe_version {
            // conversion is a bit expensive, but we are okay to pay this one-time-cost
            let is_exceptional = Fp6::is_zero(&mut elem.c1, cs)?;
            let c0_is_one = Fp6::equals(cs, &mut elem.c1, &mut Fp6::one(params))?;
            let c0_is_one_as_fp6 = Fp6::from_boolean(&c0_is_one, params);

            // m -> (1 + c0 - 2 * c0_is_one) / (c1 + is_exceptional) works for all values including {+1, -1}
            let mut num = Fp6Chain::new();
            num.add_pos_term(&Fp6::one(params)).add_pos_term(&elem.c0).add_neg_term(&c0_is_one_as_fp6.double(cs)?);
            let denom = elem.c1.add(cs, &Fp6::from_boolean(&is_exceptional, params))?;
            let encoding = Fp6::div_with_chain(cs, num, &denom)?;

            Self { encoding, is_negative: c0_is_one, is_exceptional}
        } else {
            // m -> (1 + m_0) / m1 = g is constrained as g * m1 = 1 + m0;
            // if m = -1, then m1 = 0, 1 + m0 = 0 and hence g would be unconstrained variable: g * 0 = 0
            // we want to exclude this case ad hence we explicitely prove that there is no exception, i.e. m1 != 0 
            Fp6::enforce_not_equal(cs, &mut elem.c1, &mut Fp6::zero(params))?;
            let tmp = elem.c0.add(cs, &Fp6::one(params))?;
            let encoding = Fp6::div(cs, &tmp, &elem.c0)?;
            
            Self { encoding, is_negative: Boolean::constant(false), is_exceptional: Boolean::constant(false)}
        };

        Ok(res)
    }

    pub fn decompress<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Fp12<'a, E, F, T>, SynthesisError> 
    {
        let params = self.encoding.get_params();
        let fp_6_one = Fp6::one(params);
        let fp_6_minus_one = fp_6_one.negate(cs)?;
        // g -> (g + w)/(g - w)
        let mut numerator = Fp12::from_coordinates(self.encoding.clone(), fp_6_one);
        let mut denomerator = Fp12::from_coordinates(self.encoding.clone(), fp_6_minus_one);
        let candidate = Fp12::div(cs, &mut numerator, &mut denomerator)?;
        candidate.conditionally_negate(cs, &self.is_negative)
    }

    pub fn inverse(&self) -> Self {
        Self { 
            encoding: self.encoding.clone(), 
            is_negative: self.is_negative.not(), 
            is_exceptional: self.is_exceptional
        }
    }

    fn compute_gamma() -> <T::Ex6 as Extension6Params<F>>::Witness {
        let fp2_zero = <<T::Ex6 as Extension6Params<F>>::Ex2 as Extension2Params<F>>::Witness::zero();
        let fp2_one = <<T::Ex6 as Extension6Params<F>>::Ex2 as Extension2Params<F>>::Witness::one();
        T::Ex6::convert_to_structured_witness(fp2_zero, fp2_one, fp2_zero)
    }

    pub fn mul<CS: ConstraintSystem<E>>(
        cs: &mut CS, left: &Self, right: &Self, is_safe_version: bool
    ) -> Result<Self, SynthesisError> {
        let params = left.encoding.get_params();
        let gamma = Self::compute_gamma();
        let res = if is_safe_version {
            // modified formula looks like (here flag = modify_formula_flag):
            // g = (g1 * g2 + !flag * \gamma) / (g1 + g2 + flag)
            let modify_formula_flag = Boolean::and(cs, &left.is_exceptional, &right.is_exceptional)?;
            let masked_gamma = Fp6::conditional_constant(gamma, &modify_formula_flag, params);
            let flag_as_fe = Fp6::from_boolean(&modify_formula_flag, params);
            
            let mut chain = Fp6Chain::new();
            chain.add_pos_term(&masked_gamma);
            let numerator = Fp6::mul_with_chain(cs, &left.encoding, &right.encoding, chain)?;
            
            let mut chain = Fp6Chain::new();
            chain.add_pos_term(&left.encoding).add_pos_term(&right.encoding).add_pos_term(&flag_as_fe);
            let denominator = Fp6::collapse_chain(cs, chain)?;
            let mut encoding = Fp6::div(cs, &numerator, &denominator)?;

            let is_negative = Boolean::xor(cs, &left.is_negative, &right.is_negative)?;
            let is_exceptional = Fp6::is_zero(&mut encoding, cs)?;
            Self { encoding, is_negative, is_exceptional }
        }
        else {
            // g = (g1 * g2 + \gamma) / (g1 + g2)
            // assume that are in the exceptional case: g2 = -g1
            // we are going to enforce relation of the form: g * 0 = g1 * g2 + \gamma
            // unless g1 * g2 + \gamma == 0 g would be never underconstrained
            // if g1 * g2 + \gamma = \gamma - g1^2 = 0 and hence g1 is the root of polynomial X^2 - \gamma = 0,
            // and hence this poly is not irreducible - contradiction with F_q^2 = F_q[w] / (w^2 - \gamma)
            // This means, we are completely safe here and no additional checks are requierd
            let numerator = Fp6::mul_with_chain(cs, &left.encoding, &right.encoding)?;
            let denominator = left.encoding.add(cs, &right.encoding)?;
            let encoding = Fp6::div(cs, &numerator, &denominator)?;
            let is_negative = Boolean::xor(cs, &left.is_negative, &right.is_negative)?;
            let is_exceptional = Boolean::constant(false);
            Self { encoding, is_negative, is_exceptional }
        };

        Ok(res)
    }

    pub fn square<CS>(&self, cs: &mut CS, is_safe_version: bool) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E> {
        let params = self.encoding.get_params();
        let gamma = Self::compute_gamma();
        let res = if is_safe_version {
            // modified formula looks like (here flag = modify_formula_flag):
            // res = 1/2 (g + [(flag *\gamma) / (g + 1)])
            let modify_formula_flag = Boolean::and(cs, &left.is_exceptional, &right.is_exceptional)?;
        } else {
            // res = 1/2 (g + \gamma / g);
            // first we calculate x = \gamma / g and then calculate res = 1/2 (g + x) 
            let x = Fp6::div(cs, )
        }
    }
}
    
//     pub fn frobenius_power_map<CS>(&self, cs: &mut CS, is_safe_version: bool) -> Result<Self, SynthesisError>
//     where CS: ConstraintSystem<E> {

//     } 
// }
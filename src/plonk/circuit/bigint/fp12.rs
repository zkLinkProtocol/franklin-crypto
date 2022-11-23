use super::*;
use std::ops::Index;
use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq6 as Bn256Fq6;


pub trait Extension12Params<F:PrimeField>: Clone {
    type Ex6: Extension6Params<F>;
    type Witness: Field;
    const NON_RESIDUE: (u64, u64, u64);
  
    fn non_residue() -> (u64,u64, u64) { Self::NON_RESIDUE.clone() }
    fn convert_to_structured_witness(
        c0: <Self::Ex6 as Extension6Params<F>>::Witness, 
        c1: <Self::Ex6 as Extension6Params<F>>::Witness, 
    ) -> Self::Witness; 
    fn convert_from_structured_witness(wit: Self::Witness) -> (
        <Self::Ex6 as Extension6Params<F>>::Witness, <Self::Ex6 as Extension6Params<F>>::Witness
    );
}

#[derive(Clone, Debug)]
pub struct Bn256Extension12Params {}
impl Extension12Params<Bn256Fq> for Bn256Extension12Params 
{
    type Ex6 = Bn256Extension6Params;
    type Witness = crate::bellman::pairing::bn256::Fq12;
    const NON_RESIDUE: (u64, u64, u64) = (1, 0, 1);

    fn convert_to_structured_witness(c0: Bn256Fq6, c1: Bn256Fq6) -> Self::Witness 
    {
        Self::Witness { c0, c1}
    }

    fn convert_from_structured_witness(x: Self::Witness) -> (Bn256Fq6, Bn256Fq6) {
        (x.c0, x.c1)
    }
}


#[derive(Clone)]
pub struct Fp12<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> {
    pub c0: Fp6<'a, E, F, T::Ex6>,
    pub c1: Fp6<'a, E, F, T::Ex6>,
    _marker: std::marker::PhantomData<T>
}
 
impl<'a, E:Engine, F:PrimeField, T:   Extension12Params<F>>std::fmt::Display for Fp12<'a, E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp12({} + {} * w)", self.c0, self.c1)
    }
}

impl<'a, E:Engine, F:PrimeField, T:   Extension12Params<F>> std::fmt::Debug for Fp12<'a, E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp12({} + {} * w)", self.c0, self.c1)
    }
}

impl<'a, E:Engine, F:PrimeField, T:  Extension12Params<F>> Index<usize> for Fp12<'a, E, F, T> {
    type Output = Fp6<'a, E, F, T::Ex6>;

    fn index(&self, idx: usize) -> &Self::Output {
        match idx {
            0 => &self.c0,
            1 => &self.c1,
            _ => panic!("Index should be 0 or 1"),
        }
    }
}

impl<'a, E:Engine, F:PrimeField, T:   Extension12Params<F> > From<Fp6<'a, E, F, T::Ex6>> for Fp12<'a, E, F, T>
{
    fn from(x: Fp6<'a, E, F, T::Ex6>) -> Self {
        let params = x.c0.c0.representation_params;
        Fp12::<E, F, T> {
            c0: x,
            c1: Fp6::<E, F, T::Ex6>::zero(params),
            _marker: std::marker::PhantomData::<T>
        }
    }    
}


impl<'a, E:Engine, F:PrimeField, T:  Extension12Params<F> > Fp12<'a, E, F, T> {
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<T::Witness>, params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (c0_wit, c1_wit) = wit.map(|x| T::convert_from_structured_witness(x)).unzip();
        let c0 = Fp6::alloc(cs, c0_wit, params)?;
        let c1 = Fp6::alloc(cs, c1_wit, params)?;
        Ok(Fp12{ c0, c1, _marker: std::marker::PhantomData::<T>})
    }

    pub fn from_coordinates(c0: Fp6<'a, E, F, T::Ex6>, c1: Fp6<'a, E, F, T::Ex6>) -> Self {
        Fp12 { c0, c1,  _marker: std::marker::PhantomData::<T> }
    }
  
    pub fn get_value(&self) -> Option<T::Witness> {
        self.c0.get_value().zip(self.c1.get_value()).map(|(c0, c1)| T::convert_to_structured_witness(c0, c1))
    }
  
    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let first_coordinate_check = Fp6::equals(cs, &mut this.c0, &mut other.c0)?;
        let second_coordinate_check = Fp6::equals(cs, &mut this.c1, &mut other.c1)?;
        Boolean::and(cs, &first_coordinate_check, &second_coordinate_check)
    }

    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp6::enforce_equal(cs, &mut this.c0, &mut other.c0)?;
        Fp6::enforce_equal(cs, &mut this.c1, &mut other.c1)     
    }
    
    pub fn enforce_not_equal<CS>(cs: &mut CS, this: Self, other: Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let selector_wit = this.get_value().zip(other.get_value()).map(|(left, right)| {
            let (c0, c1) = T::convert_from_structured_witness(left);
            let (d0, d1) = T::convert_from_structured_witness(right);
            c1 != d1
        });
        let selector = Boolean::Is(AllocatedBit::alloc(cs, selector_wit)?);
        let mut a = Fp6::conditionally_select(cs, &selector, &this.c1, &this.c0)?;
        let mut b = Fp6::conditionally_select(cs, &selector, &other.c1, &other.c0)?;
        Fp6::enforce_not_equal(cs, &mut a, &mut b)
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let c0_is_zero = Fp6::is_zero(&mut self.c0, cs)?; 
        let c1_is_zero = Fp6::is_zero(&mut self.c1, cs)?;
        Boolean::and(cs, &c0_is_zero, &c1_is_zero) 
    }
     
    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {    
        self.c0.normalize_coordinates(cs)?;
        self.c1.normalize_coordinates(cs)
    }

    pub fn zero(params: &'a RnsParameters<E, F>) -> Self {
        Self::from_coordinates(Fp6::zero(params), Fp6::zero(params))
    }

    pub fn one(params: &'a RnsParameters<E, F>) -> Self {
        Self::from_coordinates(Fp6::one(params), Fp6::zero(params))
    }
    
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.double(cs)?;
        let new_c1 = self.c1.double(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.negate(cs)?;
        let new_c1 = self.c1.negate(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.add(cs, &other.c0)?;
        let new_c1 = self.c1.add(cs, &other.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.sub(cs, &other.c0)?;
        let new_c1 = self.c1.sub(cs, &other.c1)?;  
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn fp6_mul_subroutine<CS: ConstraintSystem<E>>(
        cs: &mut CS, element: &Fp6<'a, E, F, T::Ex6>
    ) -> Result<Fp6<'a, E, F, T::Ex6>, SynthesisError> {
        // we have the following tower of extensions:
        // F_p -> u^2 - \beta -> F_p2 -> t^3 - \alpha -> F_p6 -> w^2 - t -> Fp12
        // assume we want to multipy two elements of Fp12:
        // x = x0 + w * x1; y = y0 + w * y1, then:
        // x * y = (x0 * y0 + w^2 * x1 * y1) + w * (x0 * y1 + x1 * y0)
        // so we need to implement the primitive of multiplying x \in Fp6 by w^2 = t
        // x \in Fp6 can be written in the form: x = c0 + c1 * t + c2 * t^2
        // hence x * t = c2 * \alpha + c0 * t + c1 * t^2
        // and this is the result computed by this helper function
        let alpha = T::Ex6::non_residue();       
        let new_c0 = element.c2.mul_by_small_constant(cs, alpha)?;
        let result = Fp6::from_coordinates( new_c0,  element.c0.clone(), element.c1.clone());
        Ok(result)
    }

    #[track_caller]
    pub fn mul<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        //Same as quadratic extension
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + t * v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        let v0 = Fp6::mul(cs, &first.c0, &second.c0)?; 
        let v1 = Fp6::mul(cs, &first.c1, &second.c1)?;
        let v1_mul_t = Self::fp6_mul_subroutine(cs, &v1)?; 
        let new_c0 = v0.add(cs, &v1)?; 
        let a01 = first.c0.add(cs, &first.c1)?;
        let b01 = second.c0.add(cs, &second.c1)?;
        let a01_mul_b01 = Fp6::mul(cs, &a01, &b01)?;  
        let v01 = v0.add(cs, &v1)?;   
        let new_c1 = a01_mul_b01.sub(cs, &v01)?; 
        Ok(Self::from_coordinates(new_c0, new_c1))
    }
    
    #[track_caller]
    pub fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // input: a = a0 + u * a1; output: a^2
        // v = a0 * a1
        // 1) c1 = 2 * v
        // 2) c0 = (a0 - a1)(a0 - \beta * a1) + v + \beta * v
        let v = Fp6::mul(cs, &self.c0, &self.c1)?;
        let c1 = v.double(cs)?;
        let a0_minus_a1 = self.c0.sub(cs, &self.c1)?;
        let x = Self::fp6_mul_subroutine(cs, &self.c1)?;
        let a0_minus_x = a0_minus_a1.sub(cs, &x)?;
        let y = Fp6::mul(cs, &a0_minus_a1, &a0_minus_x)?;
        let beta_v = Self::fp6_mul_subroutine(cs, &v)?;
        let mut c0 = y.add(cs, &v)?;
        c0 = c0.add(cs, &beta_v)?;
        Ok(Self::from_coordinates(c0, c1))
    }

    #[track_caller]
    pub fn div<CS>(cs: &mut CS, num: &mut Self, denom: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let params = num.c0.c0.c0.representation_params;
        let res_wit = match (num.get_value(), denom.get_value()) {
            (Some(num), Some(denom)) => {
                let denom_inv = denom.inverse().unwrap();
                let mut res = num;
                res.mul_assign(&denom_inv);
                Some(res)
            },
            _ => None
        };
        
        let res = Self::alloc(cs, res_wit, params)?;
        
        // TODO: this could be optimized even further
        let mut num_actual = Self::mul(cs, &res, &denom)?;
        Self::enforce_equal(cs, &mut num_actual, num)?;
        Ok(res)
    }

    pub fn inverse<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num = Self::one(self.c0.c0.c0.representation_params);
        Self::div(cs, &mut num, self)
    }

    pub fn frobenius_power_map<CS: ConstraintSystem<E> >(
        &self, cs: &mut CS, power:usize
    )-> Result<Self, SynthesisError> {
        match power{
            1 | 2 | 3 | 6  => {},
            _ => {
                unreachable!("can not reach power {}", power);
            }
        }
        let params = self.c0.c0.c0.representation_params;
        let mut frob_c1 = vec![];
        for i in 0..12 {
            let mut r1 = Fp2::constant(<T::Ex6 as Extension6Params<F>>::FROBENIUS_COEFFS_FQ12_C1[i], params);
            frob_c1.push(r1);
        }
        let new_c0 = self.c0.frobenius_power_map(cs, power)?;    
        let c_1 = self.c1.frobenius_power_map(cs, power)?;
        let result_c1_0 = c_1.c0.mul(cs, &frob_c1[power % 12] )?;
        let result_c1_1 = c_1.c1.mul(cs, &frob_c1[power % 12] )?;
        let result_c1_2 = c_1.c2.mul(cs, &frob_c1[power % 12] )?;
        let new_c1= Fp6::from_coordinates(result_c1_0, result_c1_1, result_c1_2);
        
        Ok(Self::from_coordinates(new_c0, new_c1))  
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq,Fq2, Fq6, Fq12, Bn256, Fr, G1, G1Affine};
    use bellman::bn256::fq;
    use bellman::compact_bn256::FROBENIUS_COEFF_FQ6_C1;
    use plonk::circuit::Width4WithCustomGates;
    use bellman::plonk::better_better_cs::gates::{selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self};
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;

    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
    use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
    use crate::bellman::plonk::better_better_cs::verifier::verify;

    #[test]
    fn test_inverse_fp12() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, Fq>::new_optimal(&mut cs, 64usize);
        type T=Bn256Extension12Params;

        let mut rng = rand::thread_rng();
        // let  p: Fq12 = rng.gen();
        let p = Fq12::one();
        let mut p_f12 = Fp12::<Bn256, Fq, T>::alloc(&mut cs, Some(p), &params).unwrap();

        let mut p_f12_inverse = p_f12.inverse(&mut cs).unwrap();
        println!("{}", p_f12_inverse);

        let mut pin=p;
            //pin.square();
        pin.inverse().unwrap();
        let mut pin_f12 = Fp12::<Bn256, Fq, T>::alloc(&mut cs, Some(pin), &params).unwrap();
        println!("{}", pin_f12);

        //Fp12::<Bn256, Fq, T>::enforce_equal(&mut cs, &mut p_f12_inverse,&mut pin_f12).unwrap();    

    }
}

    
     

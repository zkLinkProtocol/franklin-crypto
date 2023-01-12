use super::*;
use std::ops::Index;
use num_traits::ToPrimitive;
use plonk::circuit::SomeArithmetizable;
use plonk::circuit::bigint::traits::*;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq2 as Bn256Fq2;

use crate::bellman::pairing::bls12_381::Fq as Bls12Fq;
use crate::bellman::pairing::bls12_381::Fq2 as Bls12Fq2;

use super::super::curve::secp256k1::fq::Fq as SecpFq;
use super::super::curve::secp256k1::fq2::Fq2 as SecpFq2;


pub trait Extension2Params<F: PrimeField>: Clone {
    type Witness: Field;
    // by default non-residue is -1
    fn non_residue() -> F {
        let mut res = F::one();
        res.negate();
        res
    }
    // if non_residue is equal to -1 than multiplication formulas can are simplified
    fn do_mul_by_negation() -> bool {
        let mut tmp = Self::non_residue();
        tmp.add_assign(&F::one());
        tmp.is_zero() 
    }

    // default impl is consistent only with non-residue == -1
    fn is_default_impl() -> bool { true }

    fn convert_to_structured_witness(c0: F, c1: F) -> Self::Witness;
    fn convert_from_structured_witness(val: Self::Witness) -> (F, F);
}

#[derive(Clone)]
pub struct Bn256Extension2Params {}
impl Extension2Params<Bn256Fq> for Bn256Extension2Params {
    type Witness = Bn256Fq2;
    fn convert_to_structured_witness(c0: Bn256Fq, c1: Bn256Fq) -> Bn256Fq2 {
        Bn256Fq2 { c0, c1 }
    }
    fn convert_from_structured_witness(val: Self::Witness) -> (Bn256Fq, Bn256Fq) {
        (val.c0, val.c1)
    }
}

#[derive(Clone)]
pub struct BLS12Extension2Params {}
impl Extension2Params<Bls12Fq> for BLS12Extension2Params {
    type Witness = Bls12Fq2;
    fn convert_to_structured_witness(c0: Bls12Fq, c1: Bls12Fq) -> Bls12Fq2 {
        Bls12Fq2 { c0, c1 }
    }
    fn convert_from_structured_witness(val: Self::Witness) -> (Bls12Fq, Bls12Fq) {
        (val.c0, val.c1)
    }
}

#[derive(Clone)]
pub struct Secp256K1Extension2Params {}
impl Extension2Params<SecpFq> for Secp256K1Extension2Params {
    type Witness = SecpFq2;
    fn convert_to_structured_witness(c0: SecpFq, c1: SecpFq) -> SecpFq2 {
        SecpFq2 { c0, c1 }
    }
    fn convert_from_structured_witness(val: Self::Witness) -> (SecpFq, SecpFq) {
        (val.c0, val.c1)
    }
}


#[derive(Clone)]
pub struct Fp2<E: Engine, F: PrimeField, T: Extension2Params<F>> {
    pub c0: FieldElement<E, F>,
    pub c1: FieldElement<E, F>,
    wit: Option<T::Witness>,
    _marker: std::marker::PhantomData<T>
}
 
impl<E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Display for Fp2<E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
    }
}

impl<E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Debug for Fp2<E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
    }
}

impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>> Index<usize> for Fp2<E, F, T> {
    type Output = FieldElement<E, F>;

    fn index(&self, idx: usize) -> &Self::Output {
        match idx {
            0 => &self.c0,
            1 => &self.c1,
            _ => panic!("Index should be 0 or 1"),
        }
    }
}

impl<E: Engine, F: PrimeField, T: Extension2Params<F>> CircuitFieldExt<E, T::Witness> for Fp2<E, F, T>
{
    type BaseField = F;
    type BaseCircuitField = FieldElement<E, F>;
}


impl<E:Engine, F:PrimeField, T: Extension2Params<F>> From<FieldElement<E, F>> for Fp2<E, F, T>
{
    fn from(x: FieldElement<E, F>) -> Self {
        let params = x.get_rns_params();
        let witness = x.get_field_value().map(|fr| T::convert_to_structured_witness(fr, F::zero()));
        Fp2::<E, F, T> {
            c0: x,
            c1: <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params),
            wit: witness,
            _marker: std::marker::PhantomData::<T>
        }
    }    
}


impl<E:Engine, F:PrimeField, T: Extension2Params<F>> CoreCircuitField<E, T::Witness> for Fp2<E, F, T> {
    fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.scale(cs, factor)?;
        let new_c1 = self.c1.scale(cs, factor)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<T::Witness>, params: Arc<RnsParameters<E>>
    ) -> Result<Self, SynthesisError> {
        let (c0_wit, c1_wit) = wit.map(|x| T::convert_from_structured_witness(x)).unzip();
        let c0 = FieldElement::alloc(cs, c0_wit, params.clone())?;
        let c1 = FieldElement::alloc(cs, c1_wit, params)?;
        Ok(Fp2{ c0, c1, wit, _marker: std::marker::PhantomData::<T>})
    } 
   
    fn constant(value: T::Witness, params: Arc<RnsParameters<E>>) -> Self {
        let (c0, c1) = T::convert_from_structured_witness(value);
        Self::from_coordinates(FieldElement::constant(c0, params.clone()), FieldElement::constant(c1, params))
    }

    fn zero(params: Arc<RnsParameters<E>>) -> Self {
        Self::from_coordinates(
            <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params.clone()), 
            <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params)
        )
    }

    fn one(params: Arc<RnsParameters<E>>) -> Self {
        Self::from_coordinates(
            <FieldElement<E, F> as CoreCircuitField<E, F>>::one(params.clone()), 
            <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params)
        )
    }
        
    fn get_value(&self) -> Option<T::Witness> {
        self.wit
    }

    fn get_rns_params(&self) -> Arc<RnsParameters<E>> {
        self.c0.get_rns_params()
    }

    fn is_constant(&self) -> bool {
        self.c0.is_constant() && self.c1.is_constant()
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let new_c0 = FieldElement::conditionally_select(cs, flag, &first.c0, &second.c0)?;
        let new_c1 = FieldElement::conditionally_select(cs, flag, &first.c1, &second.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn normalize<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {    
        self.c0.normalize(cs)?;
        self.c1.normalize(cs)
    }
  
    fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.double(cs)?;
        let new_c1 = self.c1.double(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }
      
    fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.negate(cs)?;
        let new_c1 = self.c1.negate(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let new_c0 = self.c0.conditionally_negate(cs, flag)?;
        let new_c1 = self.c1.conditionally_negate(cs, flag)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }
    
    fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.add(cs, &other.c0)?;
        let new_c1 = self.c1.add(cs, &other.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.sub(cs, &other.c0)?;
        let new_c1 = self.c1.sub(cs, &other.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let c0_is_zero = <FieldElement<E, F> as CoreCircuitField<E, F>>::is_zero(&mut self.c0, cs)?; 
        let c1_is_zero = <FieldElement<E, F> as CoreCircuitField<E, F>>::is_zero(&mut self.c1, cs)?;
        Boolean::and(cs, &c0_is_zero, &c1_is_zero) 
    }

    fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let first_coordinate_check = FieldElement::equals(cs, &mut this.c0, &mut other.c0)?;
        let second_coordinate_check = FieldElement::equals(cs, &mut this.c1, &mut other.c1)?;
        Boolean::and(cs, &first_coordinate_check, &second_coordinate_check)
    }

    fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        FieldElement::enforce_equal(cs, &mut this.c0, &mut other.c0)?;
        FieldElement::enforce_equal(cs, &mut this.c1, &mut other.c1)
    }
    
    fn enforce_not_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // if x = c0 + u * c1 is not equal y = d0 + u * d1 then at least one of c0 != d0 or c1 != d1 should hold
        let selector_wit = this.get_value_as_coordinates().zip(other.get_value_as_coordinates()).map(
            |((_c0, c1), (_d0, d1))| c1 != d1
        );
        let selector = Boolean::Is(AllocatedBit::alloc(cs, selector_wit)?);
        let mut a = FieldElement::conditionally_select(cs, &selector, &this.c1, &this.c0)?;
        let mut b = FieldElement::conditionally_select(cs, &selector, &other.c1, &other.c0)?;
        FieldElement::enforce_not_equal(cs, &mut a, &mut b)
    }
       
    fn collapse_chain<CS>(cs: &mut CS, chain: FieldElementsChain<E, T::Witness, Self>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let subchain = chain.get_coordinate_subchain(0);
        let c0 = FieldElement::collapse_chain(cs, subchain)?;
        let subchain = chain.get_coordinate_subchain(1);
        let c1 = FieldElement::collapse_chain(cs, subchain)?;

        Ok(Self::from_coordinates(c0, c1))
    }

    fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, T::Witness, Self> 
    ) -> Result<(), SynthesisError> {
        for i in 0..2 {
            FieldElement::enforce_chain_is_zero(cs, chain.get_coordinate_subchain(i))?;
        }
        Ok(())
    }

    fn from_boolean(flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let c0 = FieldElement::from_boolean(flag, params.clone());
        let c1 = <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params);
        Self::from_coordinates(c0, c1)
    }

    fn conditional_constant(value: T::Witness, flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let (c0, c1) = T::convert_from_structured_witness(value);
        let c0 = FieldElement::conditional_constant(c0, flag, params.clone());
        let c1 = FieldElement::conditional_constant(c1, flag, params);
        Self::from_coordinates(c0, c1)
    }
}


impl<E:Engine, F:PrimeField, T: Extension2Params<F>>  Fp2<E, F, T> {
    pub fn get_base_field_coordinates(&self) -> Vec<FieldElement<E, F>> {
        vec![self.c0.clone(), self.c1.clone()]
    }

    pub fn alloc_from_coordinates<CS: ConstraintSystem<E>>(
        cs: &mut CS, c0_wit: Option<F>, c1_wit: Option<F>, params: Arc<RnsParameters<E>>
    ) -> Result<Self, SynthesisError> {
        let c0 = FieldElement::alloc(cs, c0_wit, params.clone())?;
        let c1 = FieldElement::alloc(cs, c1_wit, params)?;
        let wit = match (c0_wit, c1_wit) {
            (Some(c0), Some(c1)) => Some(T::convert_to_structured_witness(c0, c1)),
            _ => None,
        };
        Ok(Fp2{ c0, c1, wit, _marker: std::marker::PhantomData::<T>})
    }

    pub fn from_coordinates(c0: FieldElement<E, F>, c1: FieldElement<E, F>) -> Self {
        let wit = match (c0.get_field_value(), c1.get_field_value()) {
            (Some(c0), Some(c1)) => Some(T::convert_to_structured_witness(c0, c1)),
            _ => None,
        };
        Fp2 { c0, c1, wit, _marker: std::marker::PhantomData::<T> }
    }

    pub fn from_base_field(x: FieldElement<E, F>) -> Self {
        let params = x.get_rns_params();
        Fp2::from_coordinates(x, <FieldElement<E, F> as CoreCircuitField<E, F>>::zero(params))
    }

    pub fn get_value_as_coordinates(&self) -> Option<(F, F)> {
       self.c0.get_field_value().zip(self.c1.get_field_value()) 
    }
  
    pub fn constant_from_coordinates(c0: F, c1: F, params: Arc<RnsParameters<E>>) -> Self {
        Self::from_coordinates(FieldElement::constant(c0, params.clone()), FieldElement::constant(c1, params))
    }
  
    #[track_caller]
    pub fn mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: (u64, u64), chain: FieldElementsChain<E, T::Witness, Self>
    ) -> Result<Self, SynthesisError> {
        // we assume that non_residue = -1
        assert!(T::is_default_impl());
        let (s0, s1) = scalar;
        // if our small constant is (s0, s1) then:
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0 = a0 * s0
        // 2) v1 = a1 * b1 = a1 * s1
        // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * s0 - a1 * s1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 = a0 * (s0 + s1) + a1 * (s0 + s1) - a0 * s0 - a1 * s1
        // hence: c1 = a0 * s1 + a1 * s0

        let mut subchain = chain.get_coordinate_subchain(0); 
        subchain.add_pos_term(&self.c0.scale(cs, s0)?);
        subchain.add_neg_term(&self.c1.scale(cs, s1)?);
        let c0 = FieldElement::collapse_chain(cs, subchain)?;
        
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_pos_term(&self.c0.scale(cs, s1)?);
        subchain.add_pos_term(&self.c1.scale(cs, s0)?);
        let c1 = FieldElement::collapse_chain(cs, subchain)?;
        
        Ok(Self::from_coordinates(c0, c1))
    }

    pub fn mul_by_small_constant<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: (u64, u64)
    ) -> Result<Self, SynthesisError> {
        let chain = FieldElementsChain::<E, T::Witness, Self>::new();
        self.mul_by_small_constant_with_chain(cs, scalar, chain)
    }

    #[track_caller]
    pub fn constraint_mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &Self, scalar: (u64, u64), chain: FieldElementsChain<E, T::Witness, Self>
    ) -> Result<(), SynthesisError> {
        assert!(T::is_default_impl());
        let (s0, s1) = scalar;
        // if our small constant is (s0, s1) then:
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0 = a0 * s0
        // 2) v1 = a1 * b1 = a1 * s1
        // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * s0 - a1 * s1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 = a0 * (s0 + s1) + a1 * (s0 + s1) - a0 * s0 - a1 * s1
        // hence: c1 = a0 * s1 + a1 * s0

        let mut subchain = chain.get_coordinate_subchain(0); 
        subchain.add_pos_term(&elem.c0.scale(cs, s0)?);
        subchain.add_neg_term(&elem.c1.scale(cs, s1)?);
        FieldElement::enforce_chain_is_zero(cs, subchain)?;
        
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_pos_term(&elem.c0.scale(cs, s1)?);
        subchain.add_pos_term(&elem.c1.scale(cs, s0)?);
        FieldElement::enforce_chain_is_zero(cs, subchain)
    }

    
    pub fn mul_by_base_field<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, base_field_var: &FieldElement<E, F>
    ) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.mul_by(cs, base_field_var)?;
        let new_c1 = self.c1.mul_by(cs, base_field_var)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }
}


impl<E:Engine, F:PrimeField, T: Extension2Params<F>> CircuitField<E, T::Witness> for Fp2<E, F, T> {
    #[track_caller]
    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, T::Witness, Self> 
    ) -> Result<(), SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + \beta * v1 = v0 - v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        
        // we assume that non_residue = -1
        assert!(T::is_default_impl());

        let v0 = first.c0.mul_by(cs, &second.c0)?;
        let v1 = first.c1.mul_by(cs, &second.c1)?;
       
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0);
        subchain.add_neg_term(&v1);
        FieldElement::collapse_chain(cs, subchain)?;
        //FieldElement::constraint_fma(cs, &FieldElement::zero(params), &FieldElement::zero(params), subchain)?;

        let a = first.c0.add(cs, &first.c1)?;
        let b = second.c0.add(cs, &second.c1)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0);
        subchain.add_neg_term(&v1);
        FieldElement::constraint_fma(cs, &a, &b, subchain)?;
        Ok(())
    }

    fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, T::Witness, Self>
    ) -> Result<Self, SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * b0 - v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        // NB: v0 = c0 + v1 - chain0, c1 = a * b - v0 - v1 + chain1 = a * b - c0 - 2 * v1 + chain0 + chain1

        // we assume that non_residue = -1
        assert!(T::is_default_impl());
        
        let v1 = first.c1.mul_by(cs, &second.c1)?;
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_neg_term(&v1);
        let c0 = FieldElement::mul_with_chain(cs, &first.c0, &second.c0, subchain)?;

        let a = first.c0.add(cs, &first.c1)?;
        let b = second.c0.add(cs, &second.c1)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&c0);
        let x = v1.double(cs)?;
        subchain.add_neg_term(&x);
        for elem in chain.get_coordinate_subchain(0).elems_to_add.iter() {
            subchain.add_pos_term(elem);
        }
        for elem in chain.get_coordinate_subchain(0).elems_to_sub.iter() {
            subchain.add_neg_term(elem);
        }
        let c1 = FieldElement::mul_with_chain(cs, &a, &b, subchain)?;
        Ok(Self::from_coordinates(c0, c1))
    }
 
    fn square_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, chain: FieldElementsChain<E, T::Witness, Self>
    ) -> Result<Self, SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.17
        // input: a = a0 + u * a1; output: a^2
        // 1) c1 = 2 * a0 * a1
        // 2) c0 = (a0 - a1)(a0 + a1)
        
        // we assume that non_residue = -1
        assert!(T::is_default_impl());

        let tmp = self.c0.double(cs)?;
        let subchain = chain.get_coordinate_subchain(1);
        let c1 = FieldElement::mul_with_chain(cs, &tmp, &self.c1, subchain)?;

        let x = self.c0.sub(cs, &self.c1)?;
        let y = self.c0.add(cs, &self.c1)?;
        let subchain = chain.get_coordinate_subchain(0);
        let c0 = FieldElement::mul_with_chain(cs, &x, &y, subchain)?;

        Ok(Self::from_coordinates(c0, c1))
    }

    fn div_with_chain<CS>(cs: &mut CS, chain: FieldElementsChain<E, T::Witness, Self>, den: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // we assume that non_residue = -1
        assert!(T::is_default_impl());
        
        let params = den.get_rns_params();
        let wit = match (chain.get_value(), den.get_value()) {
            (Some(num), Some(den)) => {
                let mut res = den.inverse().expect("den should be nonzero");
                res.mul_assign(&num);
                Some(res)
            },
            _ => None,
        };

        let all_constants = den.is_constant() && chain.is_constant();
        if all_constants {
            let res = Self::constant(wit.unwrap(), params);
            Ok(res)
        }
        else {
            let res = Self::alloc(cs, wit, params)?;
            let chain = chain.negate();
            Self::constraint_fma(cs, &res, &den, chain)?;
            Ok(res)
        }
    }

    fn frobenius_power_map<CS>(&self, cs: &mut CS, power: usize)-> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        if power % 2 == 0 {
            return Ok(self.clone())
        } 
        else {
            assert!(T::is_default_impl());
            let new_c1 = self.c1.negate(cs)?;
            let new_c0 = self.c0.clone();   
            
            let res = Self::from_coordinates(new_c0, new_c1);
            let actual_value = self.get_value().map(|x| {
                let mut tmp = x;
                tmp.frobenius_map(power);
                tmp
            });
            assert_eq!(res.get_value(), actual_value);

            return Ok(res)
        }
    }
}

    




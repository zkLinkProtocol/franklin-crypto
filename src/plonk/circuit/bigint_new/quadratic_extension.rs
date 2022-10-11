use super::*;
use std::ops::Index;
use plonk::circuit::SomeArithmetizable;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bls12_381::Fq as Bls12Fq;
use super::super::curve_new::secp256k1::fq::Fq as SecpFq;


pub trait Extension2Params<F: PrimeField>: Clone {
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
}

#[derive(Clone, Debug)]
pub struct Bn256Extension2Params {}
impl Extension2Params<Bn256Fq> for Bn256Extension2Params {}

#[derive(Clone)]
pub struct BLS12Extension2Params {}
impl Extension2Params<Bls12Fq> for BLS12Extension2Params {}

#[derive(Clone)]
pub struct Secp256K1Extension2Params {}
impl Extension2Params<SecpFq> for Secp256K1Extension2Params {}


#[derive(Clone)]
pub struct Fp2<'a, E: Engine, F: PrimeField, T: Extension2Params<F>> {
    pub c0: FieldElement<'a, E, F>,
    pub c1: FieldElement<'a, E, F>,
    _marker: std::marker::PhantomData<T>
}
 
impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Display for Fp2<'a, E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
    }
}

impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Debug for Fp2<'a, E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
    }
}

impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>> Index<usize> for Fp2<'a, E, F, T> {
    type Output = FieldElement<'a, E, F>;

    fn index(&self, idx: usize) -> &Self::Output {
        match idx {
            0 => &self.c0,
            1 => &self.c1,
            _ => panic!("Index should be 0 or 1"),
        }
    }
}

impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>> From<FieldElement<'a, E, F>> for Fp2<'a, E, F, T>
{
    fn from(x: FieldElement<'a, E, F>) -> Self {
        let params = x.representation_params;
        Fp2::<E, F, T> {
            c0: x,
            c1: FieldElement::<E, F>::zero(params),
            _marker: std::marker::PhantomData::<T>
        }
    }    
}

pub struct Fp2Chain<'a, E: Engine, F: PrimeField, T: Extension2Params<F>> {
    pub elems_to_add: Vec<Fp2<'a, E, F, T>>,
    pub elems_to_sub: Vec<Fp2<'a, E, F, T>> 
}

impl<'a, E: Engine, F: PrimeField, T: Extension2Params<F>> Fp2Chain<'a, E, F, T> {
    pub fn new() -> Self {
        Fp2Chain::<E, F, T> {
            elems_to_add: vec![],
            elems_to_sub: vec![] 
        }
    }
    
    pub fn add_pos_term(&mut self, elem: &Fp2<'a, E, F, T>) -> &mut Self {
        self.elems_to_add.push(elem.clone());
        self
    } 

    pub fn add_neg_term(&mut self, elem: &Fp2<'a, E, F, T>) -> &mut Self {
        self.elems_to_sub.push(elem.clone());
        self
    }

    pub fn is_constant(&self) -> bool {
        self.elems_to_add.iter().chain(self.elems_to_sub.iter()).all(|x| x.is_constant())
    }

    pub fn get_field_value(&self) -> (Option<F>, Option<F>) {
        let (pos_c0, pos_c1) = self.elems_to_add.iter().fold((Some(F::zero()), Some(F::zero())), |acc, x| {
            (acc.0.add(&x.c0.get_field_value()), acc.1.add(&x.c1.get_field_value()))
        });
        let (neg_c0, neg_c1) = self.elems_to_sub.iter().fold((Some(F::zero()), Some(F::zero())), |acc, x| {
            (acc.0.add(&x.c0.get_field_value()), acc.1.add(&x.c1.get_field_value()))
        });
        
        (pos_c0.sub(&neg_c0), pos_c1.sub(&neg_c1))
    }

    pub fn get_coordinate_subchain(&self, i: usize) -> FieldElementsChain<'a, E, F> {
        let elems_to_add = self.elems_to_add.iter().map(|x| x[i].clone()).collect();
        let elems_to_sub = self.elems_to_sub.iter().map(|x| x[i].clone()).collect();
        FieldElementsChain::<E, F> {
            elems_to_add,
            elems_to_sub
        }
    }

    pub fn negate(self) -> Self {
        let Fp2Chain { elems_to_add, elems_to_sub } = self;
        Fp2Chain {
            elems_to_add: elems_to_sub,
            elems_to_sub: elems_to_add
        }
    }  
}


impl<'a, E:Engine, F:PrimeField, T: Extension2Params<F>>  Fp2<'a, E, F, T> {
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, c0_wit: Option<F>, c1_wit: Option<F>, params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let c0 = FieldElement::alloc(cs, c0_wit, params)?;
        let c1 = FieldElement::alloc(cs, c1_wit, params)?;
        Ok(Fp2{ c0, c1, _marker: std::marker::PhantomData::<T>})
    } 

    pub fn from_coordinates(c0: FieldElement<'a, E, F>, c1: FieldElement<'a, E, F>) -> Self {
        Fp2 { c0, c1, _marker: std::marker::PhantomData::<T> }
    }

    pub fn from_base_field(x: FieldElement<'a, E, F>) -> Self {
        let params = x.representation_params;
        Fp2::from_coordinates(x, FieldElement::zero(params))
    }

    pub fn get_value(&self) -> Option<(F, F)> {
       self.c0.get_field_value().zip(self.c1.get_field_value()) 
    } 

    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let first_coordinate_check = FieldElement::equals(cs, &mut this.c0, &mut other.c0)?;
        let second_coordinate_check = FieldElement::equals(cs, &mut this.c1, &mut other.c1)?;
        Boolean::and(cs, &first_coordinate_check, &second_coordinate_check)
    }

    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        FieldElement::enforce_equal(cs, &mut this.c0, &mut other.c0)?;
        FieldElement::enforce_equal(cs, &mut this.c1, &mut other.c1)
    }
    
    pub fn enforce_not_equal<CS>(cs: &mut CS, this: Self, other: Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // if x = c0 + u * c1 is not equal y = d0 + u * d1 then at least one of c0 != d0 or c1 != d1 should hold
        let selector_wit = this.get_value().zip(other.get_value()).map(|((_c0, c1), (_d0, d1))| c1 != d1);
        let selector = Boolean::Is(AllocatedBit::alloc(cs, selector_wit)?);
        let mut a = FieldElement::conditionally_select(cs, &selector, &this.c1, &this.c0)?;
        let mut b = FieldElement::conditionally_select(cs, &selector, &other.c1, &other.c0)?;
        FieldElement::enforce_not_equal(cs, &mut a, &mut b)
    }
     
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let new_c0 = FieldElement::conditionally_select(cs, flag, &first.c0, &second.c0)?;
        let new_c1 = FieldElement::conditionally_select(cs, flag, &first.c1, &second.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
    }

    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {    
        self.c0.normalize(cs)?;
        self.c1.normalize(cs)
    }
    
    pub fn zero(params: &'a RnsParameters<E, F>) -> Self {
        Self::from_coordinates(FieldElement::zero(params), FieldElement::zero(params))
    }

    pub fn one(params: &'a RnsParameters<E, F>) -> Self {
        Self::from_coordinates(FieldElement::one(params), FieldElement::zero(params))
    }
      
    pub fn constant(c0: F, c1: F, params: &'a RnsParameters<E, F>) -> Self {
        Self::from_coordinates(FieldElement::constant(c0, params), FieldElement::constant(c1, params))
    }

    pub fn is_constant(&self) -> bool {
        self.c0.is_constant() && self.c1.is_constant()
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

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let new_c0 = self.c0.conditionally_negate(cs, flag)?;
        let new_c1 = self.c1.conditionally_negate(cs, flag)?;
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

    pub fn mul<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        Self::mul_with_chain(cs, &self, &other, Fp2Chain::new())
    }

    pub fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        self.square_with_chain(cs, Fp2Chain::new())
    }

    pub fn div<CS: ConstraintSystem<E>>(&self, cs: &mut CS, den: &Self) -> Result<Self, SynthesisError> {
        let mut num_chain = Fp2Chain::new();
        num_chain.add_pos_term(self);
        Self::div_with_chain(cs, num_chain, den)
    }

    #[track_caller]
    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: Fp2Chain<'a, E, F, T>
    ) -> Result<(), SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + \beta * v1 = v0 - v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        
        // we assume that non_residue = -1
        assert!(T::is_default_impl());

        let params = first.c0.representation_params;
        let v0 = first.c0.mul(cs, &second.c0)?;
        let v1 = first.c1.mul(cs, &second.c1)?;
       
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0);
        subchain.add_neg_term(&v1);
        FieldElement::constraint_fma(cs, &FieldElement::zero(params), &FieldElement::zero(params), subchain)?;

        let a = first.c0.add(cs, &first.c1)?;
        let b = second.c0.add(cs, &second.c1)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0);
        subchain.add_neg_term(&v1);
        FieldElement::constraint_fma(cs, &a, &b, subchain)
    }

    pub fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: Fp2Chain<'a, E, F, T>
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
        
        let v1 = first.c1.mul(cs, &second.c1)?;
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
 
    pub fn square_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, chain: Fp2Chain<'a, E, F, T>
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

    pub fn inverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num_chain = Fp2Chain::new();
        num_chain.add_pos_term(&Self::one(&self.c0.representation_params));
        Self::div_with_chain(cs, num_chain, self)
    }
    
    pub fn div_with_chain<CS>(cs: &mut CS, chain: Fp2Chain<'a, E, F, T>, den: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // we assume that non_residue = -1
        assert!(T::is_default_impl());
        
        let params = &den.c0.representation_params;
        // we do chain/den = result mod p, where we assume that den != 0
        let (c0, c1) = den.get_value().unwrap_or((F::one(), F::zero()));
        assert!(!(c0.is_zero() && c1.is_zero()));

        // (a0 + u * a1) / (b0 + u * b1) = (a0 + u * a1) * (b0 - u * b1) / (b0^2 - \beta * b1^2) = 
        // = [1/(b0^2 - \beta * b1^2)] * [(a0 * b0 - \beta a1 * b1) + u * (a1 * b0 - a0 * b1)]
        let (numerator_c0_wit, numerator_c1_wit)  = chain.get_field_value();
        let (den_c0_wit, den_c1_wit) = (den.c0.get_field_value(), den.c1.get_field_value());
        let (res_c0_wit, res_c1_wit) = match (numerator_c0_wit, numerator_c1_wit, den_c0_wit, den_c1_wit) {
            (Some(a0), Some(a1), Some(b0), Some(b1)) => {
                let beta = T::non_residue();
                let mut b0_squared = b0;
                b0_squared.square();
                let mut b1_squared = b1;
                b1_squared.square();
                let mut norm = b1_squared;
                norm.mul_assign(&beta);
                norm.negate();
                norm.add_assign(&b0_squared);
                let norm_inv = norm.inverse().unwrap();

                let mut c0 = a0;
                c0.mul_assign(&b0);
                let mut tmp = a1;
                tmp.mul_assign(&b1);
                tmp.mul_assign(&beta);
                c0.sub_assign(&tmp); 
                c0.mul_assign(&norm_inv);

                let mut c1 = a1;
                c1.mul_assign(&b0);
                let mut tmp = a0;
                tmp.mul_assign(&b1);
                c1.sub_assign(&tmp);
                c1.mul_assign(&norm_inv);
                
                (Some(c0), Some(c1))
            },
            _ => (None, None),
        };

        let all_constants = den.is_constant() && chain.is_constant();
        if all_constants {
            let res = Self::constant(res_c0_wit.unwrap(), res_c1_wit.unwrap(), params);
            Ok(res)
        }
        else {
            let res = Self::alloc(cs, res_c0_wit, res_c1_wit, params)?;
            let chain = chain.negate();
            Self::constraint_fma(cs, &res, &den, chain)?;
            Ok(res)
        }
    }
}



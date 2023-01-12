use smallvec::SmallVec;

use super::*;
use crate::plonk::circuit::SomeArithmetizable;
use std::{ops::Index, convert::TryInto};
use self::fp::RnsParameters;

pub const MAX_EXT_DEGREE: usize = 3;


pub struct FieldElementsChain<E: Engine, F: Field, T> {
    pub elems_to_add: Vec<T>,
    pub elems_to_sub: Vec<T>,
    pub engine_marker: std::marker::PhantomData<E>,
    pub field_marker: std::marker::PhantomData<F>
}

impl<E: Engine, F: Field, T: CoreCircuitField<E, F>> FieldElementsChain<E, F, T> {
    pub fn new() -> Self {
        FieldElementsChain::<E, F, T> {
            elems_to_add: vec![],
            elems_to_sub: vec![],
            engine_marker: std::marker::PhantomData::<E>,
            field_marker: std::marker::PhantomData::<F>
        }
    }

    pub fn fin(x: &mut Self) -> Self {
        std::mem::replace(x, Self::new())
    } 
    
    pub fn add_pos_term(&mut self, elem: &T) -> &mut Self {
        self.elems_to_add.push(elem.clone());
        self
    } 

    pub fn add_neg_term(&mut self, elem: &T) -> &mut Self {
        self.elems_to_sub.push(elem.clone());
        self
    }

    pub fn is_constant(&self) -> bool {
        self.elems_to_add.iter().chain(self.elems_to_sub.iter()).all(|x| x.is_constant())
    }

    pub fn get_value(&self) -> Option<F> {
        let pos_total_sum = self.elems_to_add.iter().fold(
            Some(F::zero()), |acc, x| acc.add(&x.get_value())
        );
        let neg_total_sum = self.elems_to_sub.iter().fold(
            Some(F::zero()), |acc, x| acc.add(&x.get_value())
        );
        pos_total_sum.sub(&neg_total_sum)
    }

    pub fn negate(self) -> Self {
        let FieldElementsChain { elems_to_add, elems_to_sub, .. } = self;
        FieldElementsChain {
            elems_to_add: elems_to_sub,
            elems_to_sub: elems_to_add,
            engine_marker: std::marker::PhantomData::<E>,
            field_marker: std::marker::PhantomData::<F>
        }
    } 

    pub fn len(&self) -> usize {
        self.elems_to_add.len() + self.elems_to_sub.len()
    }

    pub fn get_rns_params(&self) -> Arc<RnsParameters<E>> {
        assert!(self.len() > 0);
        self.elems_to_add.get(0).unwrap_or_else(|| &self.elems_to_sub[0]).get_rns_params()
    }
}


impl<E: Engine, F: Field, T: CircuitFieldExt<E, F>> FieldElementsChain<E, F, T>  
{
    pub fn get_coordinate_subchain(&self, i: usize) -> FieldElementsChain<E, T::BaseField, T::BaseCircuitField> 
    {
        let elems_to_add = self.elems_to_add.iter().map(|x| x[i].clone()).collect();
        let elems_to_sub = self.elems_to_sub.iter().map(|x| x[i].clone()).collect();
        FieldElementsChain {
            elems_to_add,
            elems_to_sub,
            engine_marker: std::marker::PhantomData::<E>,
            field_marker: std::marker::PhantomData::<T::BaseField>
        }
    }
}

pub trait CoreCircuitField<E: Engine, F: Field> : Sized + Clone {
    fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<F>, params: Arc<RnsParameters<E>>
    ) -> Result<Self, SynthesisError>;   
   
    fn constant(v: F, params: Arc<RnsParameters<E>>) -> Self; 

    fn zero(params: Arc<RnsParameters<E>>) -> Self; 

    fn one(params: Arc<RnsParameters<E>>) -> Self; 

    fn get_value(&self) -> Option<F>; 

    fn get_rns_params(&self) -> Arc<RnsParameters<E>>;

    fn is_constant(&self) -> bool;

    fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError>; 
    
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError>;  
   
    fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::zero(self.get_rns_params()).sub(cs, self)
    }

    fn conditionally_negate<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, flag: &Boolean
    ) -> Result<Self, SynthesisError>; 
    
    fn normalize<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>; 
    
    fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>;

    fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>; 
   
    fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError>; 

    fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        self.scale(cs, 2u64)
    }

    fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>;
        
    fn enforce_not_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>;
        
    fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>;
       
    fn collapse_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError>;

    fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, F, Self>, 
    ) -> Result<(), SynthesisError>;

    fn from_boolean(flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self;

    fn conditional_constant(value: F, flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self;
}

pub trait CircuitField<E: Engine, F: Field> : CoreCircuitField<E, F> 
{
    fn mul<CS: ConstraintSystem<E>>(cs: &mut CS, this: &Self, other: &Self) -> Result<Self, SynthesisError> {
        Self::mul_with_chain(cs, &this, &other, FieldElementsChain::new())
    }

    fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, this: &Self, other: &Self, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError>;

    fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        self.square_with_chain(cs, FieldElementsChain::new())
    }

    fn square_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError>;  

    fn div<CS: ConstraintSystem<E>>(&self, cs: &mut CS, den: &Self) -> Result<Self, SynthesisError> {
        let mut num_chain = FieldElementsChain::new();
        num_chain.add_pos_term(self);
        Self::div_with_chain(cs, num_chain, den)
    }

    fn inverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num_chain = FieldElementsChain::new();
        num_chain.add_pos_term(&Self::one(self.get_rns_params()));
        Self::div_with_chain(cs, num_chain, self)
    }

    fn div_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, F, Self>, den: &Self
    ) -> Result<Self, SynthesisError>; 

    fn frobenius_power_map<CS>(&self, cs: &mut CS, power: usize)-> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E>;

    fn mul_by<CS: ConstraintSystem<E>>(&self, cs: &mut CS, elem: &Self) -> Result<Self, SynthesisError> {
        Self::mul(cs, self, elem)
    }

    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self, chain: FieldElementsChain<E, F, Self>
    ) -> Result<(), SynthesisError>;
}


pub trait CircuitFieldExt<E: Engine, F: Field> : Clone + Index<usize, Output = Self::BaseCircuitField>
{
    type BaseField: Field;
    type BaseCircuitField: CircuitField<E, Self::BaseField>;
}


use smallvec::SmallVec;

use super::*;
use crate::plonk::circuit::SomeArithmetizable;
use std::{ops::Index, convert::TryInto};
use self::fp::RnsParameters;

pub const MAX_EXT_DEGREE: usize = 3;


pub struct FieldElementsChain<E: Engine, F: Field, T> {
    pub elems_to_add: Vec<T>,
    pub elems_to_sub: Vec<T>,
    engine_marker: std::marker::PhantomData<E>,
    field_marker: std::marker::PhantomData<F>
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


impl<E: Engine, F: ExtField, T: CircuitFieldExt<E, F>> FieldElementsChain<E, F, T>  
{
    pub fn get_coordinate_subchain(&self, i: usize) -> FieldElementsChain<E, F::BaseField, T::BaseCircuitField> 
    {
        let elems_to_add = self.elems_to_add.iter().map(|x| x[i].clone()).collect();
        let elems_to_sub = self.elems_to_sub.iter().map(|x| x[i].clone()).collect();
        FieldElementsChain {
            elems_to_add,
            elems_to_sub,
            engine_marker: std::marker::PhantomData::<E>,
            field_marker: std::marker::PhantomData::<F::BaseField>
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


pub trait ExtField: Field + Index<usize, Output = Self::BaseField> {
    type BaseField: Field;

    fn get_ext_degree() -> usize;
    fn get_non_residue() -> Self::BaseField;
    fn from_coordinates(coordinates: SmallVec<[Self::BaseField; MAX_EXT_DEGREE]>) -> Self;
    fn into_coordinates(self) -> SmallVec<[Self::BaseField; MAX_EXT_DEGREE]>;
}

pub trait CircuitFieldExt<E: Engine, F: ExtField> : Clone + Index<usize, Output = Self::BaseCircuitField>
{
    type BaseCircuitField: CircuitField<E, F::BaseField>;
    
    fn from_coordinates(coordinates: SmallVec<[Self::BaseCircuitField; MAX_EXT_DEGREE]>) -> Self;

    fn from_base_field(x: Self::BaseCircuitField) -> Self {
        let params = x.get_rns_params();
        let zero = <Self::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates = SmallVec::new();
        coordinates.push(x);
        coordinates.extend(std::iter::repeat(zero).take(F::get_ext_degree()-1)); 
         
        Self::from_coordinates(coordinates)
    }

    fn mul_by_base_field<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, base_field_var: &Self::BaseCircuitField
    ) -> Result<Self, SynthesisError> {
        let mut coordinates = SmallVec::new();
        for idx in 0..F::get_ext_degree() {
            let elem = <Self::BaseCircuitField as CircuitField<E, _>>::mul(cs, &self[idx], base_field_var)?;
            coordinates.push(elem);
        }

        Ok(Self::from_coordinates(coordinates))
    }
}


#[macro_export]
macro_rules! construct_ext_circuit_field {
    ($struct_name:ident, $base_name: ident, $type1: ty, $bound1: ident, $degree: expr) => {
        #[derive(Clone)]
        pub struct $struct_name<E: Engine, F: ExtField>
        where $type1: $bound1
        {
            coordinates: [$base_name<E, F::BaseField>; $degree],
            witness: Option<F>,
        }

        impl<E: Engine, F: ExtField> Index<usize> for $struct_name<E, F> 
        where $type1: $bound1
        {
            type Output = $base_name<E, F::BaseField>;

            fn index(&self, idx: usize) -> &Self::Output {
                assert!(idx < $degree);
                &self.coordinates[idx]
            }
        }

        impl<E: Engine, F: ExtField> CircuitFieldExt<E, F> for $struct_name<E, F>
        where $type1: $bound1 
        {
            type BaseCircuitField = $base_name<E, F::BaseField>;
    
            fn from_coordinates(as_vec: SmallVec<[Self::BaseCircuitField; MAX_EXT_DEGREE]>) -> Self {
                let coordinates = std::array::from_fn(|i| as_vec[i].clone());
                let coordinates_wit : Option<SmallVec<_>> =coordinates.iter().map(|x| x.get_value()).collect();
                let witness = coordinates_wit.map(|arr| F::from_coordinates(arr));

                Self { coordinates, witness }
            }
        }

        impl<E: Engine, F: ExtField> CoreCircuitField<E, F> for $struct_name<E, F> 
        where $type1: $bound1
        {
            fn alloc<CS: ConstraintSystem<E>>(
                cs: &mut CS, wit: Option<F>, params: Arc<RnsParameters<E>>
            ) -> Result<Self, SynthesisError> {
                let get_coordinate_wit = |idx: usize| wit.map(|x| x[idx]);
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(<Self as CircuitFieldExt<E, F>>::BaseCircuitField::alloc(
                        cs, get_coordinate_wit(idx), params.clone()
                    )?);
                }

                Ok(Self::from_coordinates(coordinates))
            }  
   
            fn constant(value: F, params: Arc<RnsParameters<E>>) -> Self {
                let arr = F::into_coordinates(value);
                let coordinates = SmallVec::from_iter(arr.into_iter().map(|x| {
                    <Self as CircuitFieldExt<E, F>>::BaseCircuitField::constant(x, params.clone())
                }));
                Self::from_coordinates(coordinates) 
            }

            fn zero(params: Arc<RnsParameters<E>>) -> Self {
                Self::from_base_field(
                    <<Self as CircuitFieldExt<E, F>>::BaseCircuitField as CoreCircuitField<E, _>>::zero(params)
                )
            }

            fn one(params: Arc<RnsParameters<E>>) -> Self {
                Self::from_base_field(
                    <<Self as CircuitFieldExt<E, F>>::BaseCircuitField as CoreCircuitField<E, _>>::one(params)
                )
            }

            fn get_value(&self) -> Option<F> {
                self.witness
            }

            fn get_rns_params(&self) -> Arc<RnsParameters<E>> {
                self[0].get_rns_params()
            }

            fn is_constant(&self) -> bool {
                self.coordinates.iter().all(|x| x.is_constant())
            }

            fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
                let flags = self.coordinates.iter_mut().map(|x| {
                    CoreCircuitField::is_zero(x, cs)
                }).collect::<Result<Vec<Boolean>, SynthesisError>>()?;
                let mut is_zero = flags[0];
                for partial_flag in flags.iter().skip(1) {
                    is_zero = Boolean::and(cs, &is_zero, partial_flag)?
                }

                Ok(is_zero)
            }
    
            fn conditionally_select<CS: ConstraintSystem<E>>(
                cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
            ) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(<Self as CircuitFieldExt<E, F>>::BaseCircuitField::conditionally_select(
                        cs, flag, &first[idx], &second[idx]
                    )?);
                };

                Ok(Self::from_coordinates(coordinates))
            }  
   
            fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(<Self as CircuitFieldExt<E, F>>::BaseCircuitField::negate(&self[idx], cs)?);
                };
                
                Ok(Self::from_coordinates(coordinates))
            }

            fn conditionally_negate<CS: ConstraintSystem<E>>(
                &self, cs: &mut CS, flag: &Boolean
            ) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(<Self as CircuitFieldExt<E, F>>::BaseCircuitField::conditionally_negate(
                        &self[idx], cs, flag
                    )?);
                };
                
                Ok(Self::from_coordinates(coordinates))
            }
    
            fn normalize<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
                self.coordinates.iter_mut().map(|x| x.normalize(cs)).collect::<Result<Vec<_>, _>>().map(|_x| ())
            }
            
            fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(self[idx].add(cs, &other[idx])?);
                };

                Ok(Self::from_coordinates(coordinates))
            }

            fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(self[idx].sub(cs, &other[idx])?);
                };

                Ok(Self::from_coordinates(coordinates))
            }
   
            fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    coordinates.push(
                        <Self as CircuitFieldExt<E, F>>::BaseCircuitField::scale(&self[idx], cs, factor)?
                    );
                };
                
                Ok(Self::from_coordinates(coordinates))
            }

            fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
            where CS: ConstraintSystem<E> {
                this.coordinates.iter_mut().zip(other.coordinates.iter_mut()).map(|(x, y)| {
                    <Self as CircuitFieldExt<E, F>>::BaseCircuitField::enforce_equal(cs, x, y)
                }).collect::<Result<Vec<_>, _>>().map(|_x| ())
            }
        
            fn enforce_not_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
            where CS: ConstraintSystem<E> {
                // if a = a0 + a1 * v + a2 * v^2 + .. + a_n * v^n is not equal to 
                // b = b0 + b1 * v + b2 * v^2 + ... + b_n * v^n 
                // then at least for one i in [0; n]  a_i != b_i should hold
                // we start by finding the index i (based on witnesses)
                let certificate_index = match (this.get_value(), other.get_value()) {
                    (Some(a), Some(b)) => {
                        let a_coordinates = F::into_coordinates(a);
                        let b_coordinates = F::into_coordinates(b);
                        let mut idx = 0;
                        for (x, y) in a_coordinates.iter().zip(b_coordinates.iter()) {
                            if x != y {
                                break;
                            }
                            idx += 1;
                        }
                        assert!(idx < F::get_ext_degree());
                        Some(idx)
                    },
                    _ => None,
                };

                let mut a_certificate = this[0].clone();
                let mut b_certificate = other[0].clone();
                let iter = this.coordinates.iter().zip(other.coordinates.iter()).enumerate().skip(1); 
                for (idx, (next_a, next_b)) in iter
                {
                    let selector_wit = certificate_index.map(|cert_idx| idx <= cert_idx);
                    let selector = Boolean::Is(AllocatedBit::alloc(cs, selector_wit)?);
                    a_certificate = <Self as CircuitFieldExt<E, F>>::BaseCircuitField::conditionally_select(
                        cs, &selector, &next_a, &a_certificate
                    )?;
                    b_certificate = <Self as CircuitFieldExt<E, F>>::BaseCircuitField::conditionally_select(
                        cs, &selector, &next_b, &b_certificate
                    )?;
                }
                <Self as CircuitFieldExt<E, F>>::BaseCircuitField::enforce_not_equal(
                    cs, &mut a_certificate, &mut b_certificate
                )
            }
        
            fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
            where CS: ConstraintSystem<E> {
                let flags = this.coordinates.iter_mut().zip(other.coordinates.iter_mut()).map(|(x, y)| {
                    <Self as CircuitFieldExt<E, F>>::BaseCircuitField::equals(cs, x, y)
                }).collect::<Result<Vec<_>, _>>()?;

                let mut equals = flags[0];
                for partial_flag in flags.iter().skip(1) {
                    equals = Boolean::and(cs, &equals, partial_flag)?
                }

                Ok(equals)
            }
       
            fn collapse_chain<CS: ConstraintSystem<E>>(
                cs: &mut CS, chain: FieldElementsChain<E, F, Self>
            ) -> Result<Self, SynthesisError> {
                let mut coordinates = SmallVec::new();
                for idx in 0..F::get_ext_degree() {
                    let subchain = chain.get_coordinate_subchain(idx);
                    coordinates.push(
                        <Self as CircuitFieldExt<E, F>>::BaseCircuitField::collapse_chain(cs, subchain)?
                    );
                };
                
                Ok(Self::from_coordinates(coordinates))
            }

            fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
                cs: &mut CS, chain: FieldElementsChain<E, F, Self>, 
            ) -> Result<(), SynthesisError> {
                for i in 0..F::get_ext_degree() {
                    <Self as CircuitFieldExt<E, F>>::BaseCircuitField::enforce_chain_is_zero(
                        cs, chain.get_coordinate_subchain(i)
                    )?;
                }

                Ok(())
            }

            fn from_boolean(flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
                let x = <Self as CircuitFieldExt<E, F>>::BaseCircuitField::from_boolean(flag, params);
                Self::from_base_field(x)
            }

            fn conditional_constant(value: F, flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
                let arr = F::into_coordinates(value);
                let coordinates = SmallVec::from_iter(arr.into_iter().map(|x| {
                    <Self as CircuitFieldExt<E, F>>::BaseCircuitField::conditional_constant(x, flag, params.clone())
                }));
                Self::from_coordinates(coordinates)
            }
        }
    }
}
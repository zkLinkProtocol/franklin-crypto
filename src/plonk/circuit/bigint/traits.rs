use super::*;
use crate::plonk::circuit::SomeArithmetizable;
use std::{ops::Index, convert::TryInto};


pub struct FieldElementsChain<E: Engine, F: Field, T: CoreCircuitField<E, F>> {
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


impl<E, F, const N: usize, T> FieldElementsChain<E, F, ExtField<E, F, N, T>>  
where E: Engine, F: Field, T: FieldExtensionParams<E, F, N> {
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


pub trait FieldExtensionParams<E: Engine, F: Field, const N: usize> : Clone {
    type BaseField: Field;
    type BaseCircuitField: CircuitField<E, Self::BaseField>;
    
    fn convert_to_structured_witness(arr: [Self::BaseField; N]) -> F;
    fn convert_from_structured_witness(val: F) -> [Self::BaseField; N];
}


#[derive(Clone)]
pub struct ExtField<E: Engine, F: Field, const N: usize, T: FieldExtensionParams<E, F, N>> {
    coordinates: [T::BaseCircuitField; N],
    wit: Option<F>,
    _marker: std::marker::PhantomData<T>
}

impl<E, F, const N: usize, T> Index<usize> for ExtField<E, F, N, T>
where E:Engine, F:Field, T: FieldExtensionParams<E, F, N>
{
    type Output = T::BaseCircuitField;
    fn index(&self, idx: usize) -> &Self::Output {
        &self.coordinates[idx]
    }
}

impl<E: Engine, F: Field, const N: usize, T: FieldExtensionParams<E, F, N>> ExtField<E, F, N, T> {
    pub fn from_coordinates(coordinates: [T::BaseCircuitField; N]) -> Self {
        let wit = coordinates.iter().map(|x| x.get_value()).collect::<Option<Vec<_>>>().map(|arr| {
            T::convert_to_structured_witness(arr.try_into().unwrap())
        });   
        
        ExtField {
            coordinates,
            wit,
            _marker: std::marker::PhantomData::<T>
        }
    }

    pub fn from_base_field(x: T::BaseCircuitField) -> Self {
        let params = x.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_i: usize| zero.clone());
        coordinates[0] = x;
        Self::from_coordinates(coordinates)
    }

    pub fn mul_by_base_field<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, base_field_var: &T::BaseCircuitField
    ) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_i: usize| zero.clone());

        for idx in 0..N {
            coordinates[idx] = {
                <T::BaseCircuitField as CircuitField<E, _>>::mul(cs, &self[idx], base_field_var)?
            };
        }
       
        Ok(Self::from_coordinates(coordinates))
    }
    
}

impl<E, F, const N: usize, T> CoreCircuitField<E, F> for ExtField<E, F, N, T>
where E:Engine, F:Field, T: FieldExtensionParams<E, F, N>
{
    fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<F>, params: Arc<RnsParameters<E>>
    ) -> Result<Self, SynthesisError> {
        let raw_wit = wit.map(|x| T::convert_from_structured_witness(x));
        let get_coordinate_wit = |idx: usize| raw_wit.map(|arr| arr[idx].clone());

        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params.clone());
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = T::BaseCircuitField::alloc(cs, get_coordinate_wit(idx), params.clone())?;
        } 
        
        Ok(ExtField {
            coordinates,
            wit,
            _marker: std::marker::PhantomData::<T>
        })
    }  
   
    fn constant(value: F, params: Arc<RnsParameters<E>>) -> Self {
        let arr = T::convert_from_structured_witness(value);
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params.clone());
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = T::BaseCircuitField::constant(arr[idx], params.clone());
        } 
        
        ExtField {
            coordinates,
            wit: Some(value),
            _marker: std::marker::PhantomData::<T>
        }
    }

    fn zero(params: Arc<RnsParameters<E>>) -> Self {
        Self::from_base_field(<T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params))
    }

    fn one(params: Arc<RnsParameters<E>>) -> Self {
        Self::from_base_field(<T::BaseCircuitField as CoreCircuitField<E, _>>::one(params))
    }

    fn get_value(&self) -> Option<F> {
        self.wit
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
        let params = first.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = T::BaseCircuitField::conditionally_select(cs, flag, &first[idx], &second[idx])?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }  
   
    fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = self[idx].negate(cs)?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }

    fn conditionally_negate<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, flag: &Boolean
    ) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = self[idx].conditionally_negate(cs, flag)?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }
    
    fn normalize<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.coordinates.iter_mut().map(|x| x.normalize(cs)).collect::<Result<Vec<_>, _>>().map(|_x| ())
    }
    
    fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = self[idx].add(cs, &other[idx])?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }

    fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = self[idx].sub(cs, &other[idx])?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }
   
    fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError> {
        let params = self.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = self[idx].scale(cs, factor)?;
        } 
        Ok(Self::from_coordinates(coordinates))
    }

    fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E> {
        this.coordinates.iter_mut().zip(other.coordinates.iter_mut()).map(|(x, y)| {
            T::BaseCircuitField::enforce_equal(cs, x, y)
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
                let a_coordinates = T::convert_from_structured_witness(a);
                let b_coordinates = T::convert_from_structured_witness(b);
                let mut idx = 0;
                for (x, y) in a_coordinates.iter().zip(b_coordinates.iter()) {
                    if x != y {
                        break;
                    }
                    idx += 1;
                }
                assert!(idx < N);
                Some(idx)
            },
            _ => None,
        };

        let mut a_certificate = this[0].clone();
        let mut b_certificate = other[0].clone();
        for (idx, (next_a, next_b)) in this.coordinates.iter().zip(other.coordinates.iter()).enumerate().skip(1) 
        {
            let selector_wit = certificate_index.map(|cert_idx| idx <= cert_idx);
            let selector = Boolean::Is(AllocatedBit::alloc(cs, selector_wit)?);
            a_certificate = T::BaseCircuitField::conditionally_select(cs, &selector, &next_a, &a_certificate)?;
            b_certificate = T::BaseCircuitField::conditionally_select(cs, &selector, &next_b, &b_certificate)?;
        }
        T::BaseCircuitField::enforce_not_equal(cs, &mut a_certificate, &mut b_certificate)
    }
        
    fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let flags = this.coordinates.iter_mut().zip(other.coordinates.iter_mut()).map(|(x, y)| {
            T::BaseCircuitField::equals(cs, x, y)
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
        let params = chain.get_rns_params();
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params);
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
       
        for i in 0..N {
            let subchain = chain.get_coordinate_subchain(i);
            coordinates[i] = T::BaseCircuitField::collapse_chain(cs, subchain)?;
        }
        
        Ok(Self::from_coordinates(coordinates))
    }

    fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, F, Self>, 
    ) -> Result<(), SynthesisError> {
        for i in 0..N {
            T::BaseCircuitField::enforce_chain_is_zero(cs, chain.get_coordinate_subchain(i))?;
        }

        Ok(())
    }

    fn from_boolean(flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let x = T::BaseCircuitField::from_boolean(flag, params);
        Self::from_base_field(x)
    }

    fn conditional_constant(value: F, flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let arr = T::convert_from_structured_witness(value);
        let zero = <T::BaseCircuitField as CoreCircuitField<E, _>>::zero(params.clone());
        let mut coordinates: [T::BaseCircuitField; N] = array_init::array_init(|_idx: usize| zero.clone());
        for idx in 0..N {
            coordinates[idx] = T::BaseCircuitField::conditional_constant(arr[idx], flag, params.clone());
        } 
        Self::from_coordinates(coordinates)
    }
}
  
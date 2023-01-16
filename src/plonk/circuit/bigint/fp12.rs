use super::*;
use std::ops::Index;
use crate::plonk::circuit::SomeArithmetizable;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq6 as Bn256Fq6;


pub trait Extension12Params<F:PrimeField>: Clone {
    type Ex6: Extension6Params<F>;
    type Witness: Field;
  
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

    fn convert_to_structured_witness(c0: Bn256Fq6, c1: Bn256Fq6) -> Self::Witness 
    {
        Self::Witness { c0, c1}
    }

    fn convert_from_structured_witness(x: Self::Witness) -> (Bn256Fq6, Bn256Fq6) {
        (x.c0, x.c1)
    }
}


pub struct Fp12Chain<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> {
    pub elems_to_add: Vec<Fp12<'a, E, F, T>>,
    pub elems_to_sub: Vec<Fp12<'a, E, F, T>> 
}

impl<'a, E: Engine, F: PrimeField, T: Extension12Params<F>> Fp12Chain<'a, E, F, T> {
    pub fn new() -> Self {
        Fp12Chain::<E, F, T> {
            elems_to_add: vec![],
            elems_to_sub: vec![] 
        }
    }
    
    pub fn add_pos_term(&mut self, elem: &Fp12<'a, E, F, T>) -> &mut Self {
        self.elems_to_add.push(elem.clone());
        self
    } 

    pub fn add_neg_term(&mut self, elem: &Fp12<'a, E, F, T>) -> &mut Self {
        self.elems_to_sub.push(elem.clone());
        self
    }

    pub fn is_constant(&self) -> bool {
        self.elems_to_add.iter().chain(self.elems_to_sub.iter()).all(|x| x.is_constant())
    }

    pub fn get_value(&self) -> Option<T::Witness> {
        let pos = self.elems_to_add.iter().fold(Some(T::Witness::zero()), |acc, x| acc.add(&x.get_value()));
        let neg = self.elems_to_sub.iter().fold(Some(T::Witness::zero()), |acc, x| acc.add(&x.get_value()));
        pos.sub(&neg)
    }

    pub fn get_coordinate_subchain(&self, i: usize) -> Fp6Chain<'a, E, F, T::Ex6> {
        let elems_to_add = self.elems_to_add.iter().map(|x| x[i].clone()).collect();
        let elems_to_sub = self.elems_to_sub.iter().map(|x| x[i].clone()).collect();
        Fp6Chain::<E, F, T::Ex6> {
            elems_to_add,
            elems_to_sub
        }
    }

    pub fn negate(self) -> Self {
        let Fp12Chain { elems_to_add, elems_to_sub } = self;
        Fp12Chain {
            elems_to_add: elems_to_sub,
            elems_to_sub: elems_to_add
        }
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
    pub fn get_base_field_coordinates(&self) -> Vec<FieldElement<'a, E, F>> {
        (0..2).map(|i| self[i].get_base_field_coordinates()).flatten().collect()
    }

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

    pub fn constant(value: T::Witness, params: &'a RnsParameters<E, F>) -> Self {
        let x = T::convert_from_structured_witness(value);
        Self::from_coordinates(
            Fp6::constant(x.0, params), Fp6::constant(x.1, params)
        )
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let new_c0 = Fp6::conditionally_select(cs, flag, &first.c0, &second.c0)?;
        let new_c1 = Fp6::conditionally_select(cs, flag, &first.c1, &second.c1)?;
        Ok(Self::from_coordinates(new_c0, new_c1))
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
            let (_c0, c1) = T::convert_from_structured_witness(left);
            let (_d0, d1) = T::convert_from_structured_witness(right);
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

    pub fn is_constant(&self) -> bool {
        self.c0.is_constant() && self.c1.is_constant()
    }
     
    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {    
        self.c0.normalize_coordinates(cs)?;
        self.c1.normalize_coordinates(cs)
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

    pub fn fp6_mul_subroutine<CS: ConstraintSystem<E>>(
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

    pub fn mul<CS: ConstraintSystem<E>>(cs: &mut CS, first: &Self, second: &Self) -> Result<Self, SynthesisError> 
    {
        Self::mul_with_chain(cs, first, second, Fp12Chain::new())
    }

    #[track_caller]
    pub fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: Fp12Chain<'a, E, F, T>
    ) -> Result<Self, SynthesisError> {
        //Same as quadratic extension
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + t * v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        let v0 = Fp6::mul(cs, &first.c0, &second.c0)?; 
        let v1 = Fp6::mul(cs, &first.c1, &second.c1)?;
        let v1_mul_t = Self::fp6_mul_subroutine(cs, &v1)?; 
        
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0).add_pos_term(&v1_mul_t);
        let new_c0 = Fp6::collapse_chain(cs, subchain)?;
        
        let a01 = first.c0.add(cs, &first.c1)?;
        let b01 = second.c0.add(cs, &second.c1)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0).add_neg_term(&v1);
        let new_c1 = Fp6::mul_with_chain(cs, &a01, &b01, subchain)?;
        
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
        let a0_minus_x = self.c0.sub(cs, &x)?;
        let y = Fp6::mul(cs, &a0_minus_a1, &a0_minus_x)?;
        let beta_v = Self::fp6_mul_subroutine(cs, &v)?;
        let mut c0 = y.add(cs, &v)?;
        c0 = c0.add(cs, &beta_v)?;
        
        let res = Self::from_coordinates(c0, c1);
        let mut tmp = self.get_value().unwrap();
        tmp.square();
        assert_eq!(res.get_value().unwrap(), tmp);
        Ok(res)
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
        
        let res = if num.is_constant() && denom.is_constant() {
            Self::constant(res_wit.unwrap(), params)
        } else {
            Self::alloc(cs, res_wit, params)?
        };
        
        // TODO: this could be optimized even further
        let mut num_actual = Self::mul(cs, &res, &denom)?;
        Self::enforce_equal(cs, &mut num_actual, num)?;
        Ok(res)
    }

    pub fn inverse<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num = Self::one(self.c0.c0.c0.representation_params);
        Self::div(cs, &mut num, self)
    }

    pub fn frobenius_power_map<CS: ConstraintSystem<E>>(
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
            let r1 = Fp2::constant(<T::Ex6 as Extension6Params<F>>::FROBENIUS_COEFFS_FQ12_C1[i], params);
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

    pub fn collapse_chain<CS>(cs: &mut CS, chain: Fp12Chain<'a, E, F, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let subchain = chain.get_coordinate_subchain(0);
        let c0 = Fp6::collapse_chain(cs, subchain)?;
        let subchain = chain.get_coordinate_subchain(1);
        let c1 = Fp6::collapse_chain(cs, subchain)?;
        Ok(Self::from_coordinates(c0, c1))
    }

    pub fn from_boolean(flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
        let c0 = Fp6::from_boolean(flag, params);
        let c1 = Fp6::zero(params);
        Self::from_coordinates(c0, c1)
    }

    pub fn conditional_constant(value: T::Witness, flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
        let (c0, c1) = T::convert_from_structured_witness(value);
        let c0 = Fp6::conditional_constant(c0, flag, params);
        let c1 = Fp6::conditional_constant(c1, flag, params);
        Self::from_coordinates(c0, c1)
    }

    pub fn get_params(&self) -> &'a RnsParameters<E, F> {
        self.c0.c0.c0.representation_params
    }
}
use super::*;
use super::traits::CoreCircuitField;
use std::ops::Index;
use crate::plonk::circuit::SomeArithmetizable;
use crate::plonk::circuit::bigint::traits::*;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq2 as Bn256Fq2;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ6_C1 as BN256_FROBENIUS_COEFF_FQ6_C1;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ6_C2 as BN256_FROBENIUS_COEFF_FQ6_C2;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ12_C1 as BN256_FROBENIUS_COEFF_FQ12_C1;

use crate::bellman::pairing::bls12_381::Fq as Bls12Fq;
use crate::bellman::pairing::bls12_381::Fq2 as Bls12Fq2;

use super::super::curve::secp256k1::fq::Fq as SecpFq;
use super::super::curve::secp256k1::fq2::Fq2 as SecpFq2;

pub trait Extension6Params<F:PrimeField>: Clone {
    type Ex2: Extension2Params<F>;
    type Witness: Field;

    const NON_RESIDUE: (u64, u64);
    const FROBENIUS_COEFFS_C1: [<Self::Ex2 as Extension2Params<F>>::Witness; 6];
    const FROBENIUS_COEFFS_C2: [<Self::Ex2 as Extension2Params<F>>::Witness; 6];
    const FROBENIUS_COEFFS_FQ12_C1:  [<Self::Ex2 as Extension2Params<F>>::Witness; 12];
  
    fn non_residue() -> (u64,u64) { Self::NON_RESIDUE.clone() }
    fn convert_to_structured_witness(
        c0: <Self::Ex2 as Extension2Params<F>>::Witness, 
        c1: <Self::Ex2 as Extension2Params<F>>::Witness, 
        c2: <Self::Ex2 as Extension2Params<F>>::Witness
    ) -> Self::Witness; 
    fn convert_from_structured_witness(wit: Self::Witness) -> [<Self::Ex2 as Extension2Params<F>>::Witness; 3];
}

#[derive(Clone)]
pub struct Bn256Extension6Params {}
impl Extension6Params<Bn256Fq> for Bn256Extension6Params {
    type Ex2 = Bn256Extension2Params;
    type Witness = crate::bellman::pairing::bn256::Fq6;

    const NON_RESIDUE: (u64, u64) = (9, 1);
    const FROBENIUS_COEFFS_C1: [Bn256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C1;
    const FROBENIUS_COEFFS_C2: [Bn256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C2;
    const FROBENIUS_COEFFS_FQ12_C1: [Bn256Fq2; 12] = BN256_FROBENIUS_COEFF_FQ12_C1;
   
    fn convert_to_structured_witness(c0: Bn256Fq2, c1: Bn256Fq2, c2: Bn256Fq2) -> Self::Witness 
    {
        Self::Witness { c0, c1, c2 }
    }

    fn convert_from_structured_witness(x: Self::Witness) -> [Bn256Fq2; 3] {
        [x.c0, x.c1, x.c2]
    }
}


#[derive(Clone)]
pub struct Fp6<E: Engine, F: PrimeField, T: Extension6Params<F>> {
    pub c0: Fp2<E, F, T::Ex2>,
    pub c1: Fp2<E, F, T::Ex2>,
    pub c2: Fp2<E, F, T::Ex2>,
    _marker: std::marker::PhantomData<T>
}
 
impl<E:Engine, F:PrimeField, T: Extension6Params<F>>std::fmt::Display for Fp6<E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp6({} + {} * v+ {} * v^2)", self.c0, self.c1, self.c2)
    }
}

impl<E:Engine, F:PrimeField, T: Extension6Params<F>> std::fmt::Debug for Fp6<E, F, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp6({} + {} * v + {} * v^2)", self.c0, self.c1, self.c2)
    }
}

impl<E:Engine, F:PrimeField, T: Extension6Params<F>> Index<usize> for Fp6<E, F, T> {
    type Output = Fp2<E, F, T::Ex2>;

    fn index(&self, idx: usize) -> &Self::Output {
        match idx {
            0 => &self.c0,
            1 => &self.c1,
            2 => &self.c2,
            _ => panic!("Index should be 0, 1 or 2"),
        }
    }
}

impl<E:Engine, F:PrimeField, T: Extension6Params<F> > From<Fp2<E, F, T::Ex2>> for Fp6<E, F, T>
{
    fn from(x: Fp2<E, F, T::Ex2>) -> Self {
        let params = x.c0.get_rns_params();
        let zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::zero(params);
        Fp6 {
            c0: x,
            c1: zero.clone(),
            c2: zero,
            _marker: std::marker::PhantomData::<T>
        }
    }    
}


pub struct Fp6Chain<E: Engine, F: PrimeField, T: Extension6Params<F>> {
    pub elems_to_add: Vec<Fp6<E, F, T>>,
    pub elems_to_sub: Vec<Fp6<E, F, T>> 
}

impl<E: Engine, F: PrimeField, T: Extension6Params<F>> Fp6Chain<E, F, T> {
    pub fn new() -> Self {
        Fp6Chain::<E, F, T> {
            elems_to_add: vec![],
            elems_to_sub: vec![] 
        }
    }
    
    pub fn add_pos_term(&mut self, elem: &Fp6<E, F, T>) -> &mut Self {
        self.elems_to_add.push(elem.clone());
        self
    } 

    pub fn add_neg_term(&mut self, elem: &Fp6<E, F, T>) -> &mut Self {
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

    pub fn get_coordinate_subchain(&self, i: usize) -> FieldElementsChain<E, <T::Ex2 as Extension2Params<F>>::Witness, Fp2<E, F, T::Ex2>> {
        let elems_to_add = self.elems_to_add.iter().map(|x| x[i].clone()).collect();
        let elems_to_sub = self.elems_to_sub.iter().map(|x| x[i].clone()).collect();
        FieldElementsChain {
            elems_to_add,
            elems_to_sub,
            engine_marker: std::marker::PhantomData::<E>,
            field_marker: std::marker::PhantomData::<<T::Ex2 as Extension2Params<F>>::Witness>
        }
    }

    pub fn negate(self) -> Self {
        let Fp6Chain { elems_to_add, elems_to_sub } = self;
        Fp6Chain {
            elems_to_add: elems_to_sub,
            elems_to_sub: elems_to_add
        }
    }  
}


impl<E:Engine, F:PrimeField, T: Extension6Params<F>> Fp6<E, F, T> {
    pub fn get_base_field_coordinates(&self) -> Vec<FieldElement<E, F>> {
        (0..3).map(|i| self[i].get_base_field_coordinates()).flatten().collect()
    }

    pub fn get_coordinates(&self) -> (Fp2<E, F, T::Ex2>, Fp2<E, F, T::Ex2>, Fp2<E, F, T::Ex2>) {
        (self.c0.clone(), self.c1.clone(), self.c2.clone())
    }

    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<T::Witness>, params: Arc<RnsParameters<E>>
    ) -> Result<Self, SynthesisError> {
        let (c0_wit, c1_wit, c2_wit) = if let Some(wit) = wit {
            let [c0, c1, c2] = T::convert_from_structured_witness(wit);
            (Some(c0), Some(c1), Some(c2))
        } else {
            (None, None, None)
        };
        let c0 = Fp2::alloc(cs, c0_wit, params.clone())?;
        let c1 = Fp2::alloc(cs, c1_wit, params.clone())?;
        let c2 = Fp2::alloc(cs, c2_wit, params)?;

        Ok(Fp6{ c0, c1, c2, _marker: std::marker::PhantomData::<T>})
    } 

    pub fn from_coordinates(
        c0: Fp2<E, F, T::Ex2>, c1: Fp2<E, F, T::Ex2>, c2: Fp2<E, F, T::Ex2>
    ) -> Self {
        Fp6 { c0, c1, c2, _marker: std::marker::PhantomData::<T> }
    }

    pub fn get_value(&self) -> Option<T::Witness> {
        self.c0.get_value().zip(self.c1.get_value()).zip(self.c2.get_value()).map(
            |((c0, c1), c2)| T::convert_to_structured_witness(c0, c1, c2)
        )      
    }
  
    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let first_coordinate_check = Fp2::equals(cs, &mut this.c0, &mut other.c0)?;
        let second_coordinate_check = Fp2::equals(cs, &mut this.c1, &mut other.c1)?; 
        let third_coordinate_check = Fp2::equals(cs, &mut this.c2, &mut other.c2)?;
        let parital = Boolean::and(cs, &first_coordinate_check, &second_coordinate_check)?;
        Boolean::and(cs, &parital, &third_coordinate_check)
    }

    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp2::enforce_equal(cs, &mut this.c0, &mut other.c0)?;
        Fp2::enforce_equal(cs, &mut this.c1, &mut other.c1)?;
        Fp2::enforce_equal(cs, &mut this.c2, &mut other.c2)
    }
    
    pub fn enforce_not_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // if a = a0 +a1 * v+ a2 * v^2 is not equal b = b0 + b1 * v+ b2 * v^2 then at least one of 
        // a0 != b0 or a1 != b1 or a2 != b2 should hold
        let (first_sel_wit, second_sel_wit) = if this.get_value().is_some() && other.get_value().is_some() {
            let first = this[1].get_value().unwrap() != other[1].get_value().unwrap();
            let second = this[2].get_value().unwrap() != other[2].get_value().unwrap();
            (Some(first), Some(second))
        } else {
            (None, None)
        };
        let first_selector = Boolean::Is(AllocatedBit::alloc(cs, first_sel_wit)?);
        let second_selector = Boolean::Is(AllocatedBit::alloc(cs, second_sel_wit)?);
        
        let mut a = Fp2::conditionally_select(cs, &first_selector, &this.c1, &this.c0)?;
        a = Fp2::conditionally_select(cs, &second_selector, &this.c2, &a)?;
        let mut b = Fp2::conditionally_select(cs, &first_selector, &other.c1, &other.c0)?;
        b = Fp2::conditionally_select(cs, &second_selector, &other.c2, &b)?;
        Fp2::enforce_not_equal(cs, &mut a, &mut b)
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let c0_is_zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::is_zero(&mut self.c0, cs)?; 
        let c1_is_zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::is_zero(&mut self.c1, cs)?;
        let c2_is_zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::is_zero(&mut self.c2, cs)?;
        let parital_res = Boolean::and(cs, &c0_is_zero, &c1_is_zero)?;
        Boolean::and(cs, &parital_res, &c2_is_zero) 
    }
     
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let new_c0 = Fp2::conditionally_select(cs, flag, &first.c0, &second.c0)?;
        let new_c1 = Fp2::conditionally_select(cs, flag, &first.c1, &second.c1)?;
        let new_c2 = Fp2::conditionally_select(cs, flag, &first.c2, &second.c2)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }

    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {    
        self.c0.normalize(cs)?;
        self.c1.normalize(cs)?;
        self.c2.normalize(cs)
    }
    
    pub fn zero(params: Arc<RnsParameters<E>>) -> Self {
        let zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::zero(params); 
        Self::from_coordinates(zero.clone(), zero.clone(), zero)
    }

    pub fn one(params: Arc<RnsParameters<E>>) -> Self {
        let zero = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::zero(params.clone()); 
        let one = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::one(params); 
        Self::from_coordinates(one, zero.clone(), zero)
    }
      
    pub fn constant(value: T::Witness, params: Arc<RnsParameters<E>>) -> Self {
        let x = T::convert_from_structured_witness(value);
        Self::from_coordinates(
            Fp2::constant(x[0], params.clone()), Fp2::constant(x[1], params.clone()), Fp2::constant(x[2], params)
        )
    }

    pub fn is_constant(&self) -> bool {
        self.c0.is_constant() && self.c1.is_constant() && self.c2.is_constant()
    }
    
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.double(cs)?;
        let new_c1 = self.c1.double(cs)?;
        let new_c2 = self.c2.double(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.negate(cs)?;
        let new_c1 = self.c1.negate(cs)?;
        let new_c2 = self.c2.negate(cs)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let new_c0 = self.c0.conditionally_negate(cs, flag)?;
        let new_c1 = self.c1.conditionally_negate(cs, flag)?;
        let new_c2 = self.c2.conditionally_negate(cs, flag)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }
    
    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.add(cs, &other.c0)?;
        let new_c1 = self.c1.add(cs, &other.c1)?;
        let new_c2 = self.c2.add(cs, &other.c2)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let new_c0 = self.c0.sub(cs, &other.c0)?;
        let new_c1 = self.c1.sub(cs, &other.c1)?;
        let new_c2 = self.c2.sub(cs, &other.c2)?;
        Ok(Self::from_coordinates(new_c0, new_c1, new_c2))
    }

    pub fn mul<CS: ConstraintSystem<E>>(cs: &mut CS, first: &Self, second: &Self) -> Result<Self, SynthesisError> 
    {
        Self::mul_with_chain(cs, first, second, Fp6Chain::new())
    }

    #[track_caller]
    pub fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: Fp6Chain<E, F, T>
    ) -> Result<Self, SynthesisError> 
    {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.21
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) v2 = a2 * b2
        // 4) c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        // 5) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        // 6) c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let v0 = first.c0.mul_by(cs, &second.c0)?;  
        let v1 = first.c1.mul_by(cs, &second.c1)?; 
        let v2 = first.c2.mul_by(cs, &second.c2)?;
        let tempa01 = first.c0.add(cs, &first.c1)?;  //tempaij=ai+aj
        let tempa12 = first.c1.add(cs, &first.c2)?;  
        let tempa02 = first.c0.add(cs, &first.c2)?; 
        let tempb01 = second.c0.add(cs, &second.c1)?; //tempbij=bi+bj
        let tempb12 = second.c1.add(cs, &second.c2)?;  
        let tempb02 = second.c0.add(cs, &second.c2)?;
        let alpha = T::non_residue();

        // c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        let mut sub_chain = FieldElementsChain::new();
        sub_chain.add_neg_term(&v1).add_neg_term(&v2);
        let mut c0 = Fp2::mul_with_chain(cs, &tempa12, &tempb12, sub_chain)?;
        let mut sub_chain = chain.get_coordinate_subchain(0);
        sub_chain.add_pos_term(&v0);
        c0 = c0.mul_by_small_constant_with_chain(cs, alpha, sub_chain)?;
        
        // c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        let scaled_v2 = v2.mul_by_small_constant(cs, alpha)?;
        let mut sub_chain = chain.get_coordinate_subchain(1);
        sub_chain.add_neg_term(&v0).add_neg_term(&v1).add_pos_term(&scaled_v2);
        let c1 = Fp2::mul_with_chain(cs, &tempa01, &tempb01, sub_chain)?;
           
        // c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let mut sub_chain = chain.get_coordinate_subchain(2);
        sub_chain.add_neg_term(&v0).add_neg_term(&v2).add_pos_term(&v1);
        let c2 = Fp2::mul_with_chain(cs, &tempa02, &tempb02, sub_chain)?;

        let res = Self::from_coordinates(c0, c1, c2);
        Ok(res)
    }

    #[track_caller]
    pub fn constraints_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: Fp6Chain<E, F, T>
    ) -> Result<(), SynthesisError> 
    {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.21
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) v2 = a2 * b2
        // 4) c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        // 5) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        // 6) c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let v0 = first.c0.mul_by(cs, &second.c0)?;  
        let v1 = first.c1.mul_by(cs, &second.c1)?; 
        let v2 = first.c2.mul_by(cs, &second.c2)?;
        let tempa01 = first.c0.add(cs, &first.c1)?;  //tempaij=ai+aj
        let tempa12 = first.c1.add(cs, &first.c2)?;  
        let tempa02 = first.c0.add(cs, &first.c2)?; 
        let tempb01 = second.c0.add(cs, &second.c1)?; //tempbij=bi+bj
        let tempb12 = second.c1.add(cs, &second.c2)?;  
        let tempb02 = second.c0.add(cs, &second.c2)?;
        let alpha = T::non_residue();

        // c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        let mut subchain = FieldElementsChain::new();
        subchain.add_neg_term(&v1).add_neg_term(&v2);
        let c0 = Fp2::mul_with_chain(cs, &tempa12, &tempb12, subchain)?;
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0);
        Fp2::constraint_mul_by_small_constant_with_chain(cs, &c0, alpha, subchain)?;
        
        // c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        let scaled_v2 = v2.mul_by_small_constant(cs, alpha)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0).add_neg_term(&v1).add_pos_term(&scaled_v2);
        Fp2::constraint_fma(cs,  &tempa01, &tempb01, subchain)?;
           
        // c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let mut subchain = chain.get_coordinate_subchain(2);
        subchain.add_neg_term(&v0).add_neg_term(&v2).add_pos_term(&v1);
        Fp2::constraint_fma(cs, &tempa02, &tempb02, subchain)
    }
 
    pub fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.22
        // 1) v0 = 2 * a1 * a2
        // 2) v1 = a0^2
        // 3) c0 = \alpha * v0 + v1
        // 4) v2 = 2 * a0 * a1;
        // 5) v3 = a2^2
        // 6) c1 = \alpha * v2 + v3 
        // 7) v4 = a0 - a1 + q2
        // 8) c2 = v4^2 + v2 - v3 + v0 - v1
        let alpha = T::non_residue();
        let a1_scaled = self.c1.double(cs)?;
        let v0 = a1_scaled.mul_by(cs, &self.c2)?;
        let v1 = self.c0.square(cs)?;
        let v2 = a1_scaled.mul_by(cs, &self.c0)?;
        let v3 = self.c2.square(cs)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&self.c0).add_neg_term(&self.c1).add_pos_term(&self.c2);
        let v4 = Fp2::collapse_chain(cs, chain)?;
        
        // c0 = \alpha * v0 + v1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v1);
        let c0 = v0.mul_by_small_constant_with_chain(cs, alpha, chain)?;

        // c1 = \alpha * v2 + v3 
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v3);
        let c1 = v2.mul_by_small_constant_with_chain(cs, alpha, chain)?;

        // c2 = v4^2 + v2 - v3 + v0 - v1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v2).add_neg_term(&v3).add_pos_term(&v0).add_neg_term(&v1);
        let c2 = v4.square_with_chain(cs, chain)?;
       
        Ok(Self::from_coordinates(c0, c1, c2))
    }

    pub fn inverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num = Self::one(self.get_params());
        Self::div(cs, &mut num, self)
    }

    pub fn div<CS: ConstraintSystem<E>>(cs: &mut CS, num: &Self, denom: &Self) -> Result<Self, SynthesisError> {
        let mut chain = Fp6Chain::new();
        chain.add_pos_term(num);
        Self::div_with_chain(cs, chain, denom)
    }

    pub fn div_with_chain<CS: ConstraintSystem<E> >(
        cs: &mut CS, num: Fp6Chain<E, F, T>, denom: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let params = denom.get_params();
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
            let res = Self::alloc(cs, res_wit, params)?;
            let chain = num.negate();
            Self::constraints_fma(cs, &res, denom, chain)?;
            res
        };

        Ok(res)
    }

    pub fn frobenius_power_map<CS>(&self, cs: &mut CS, power:usize)-> Result<Self,SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match power % 6 {
            0 | 1 | 2 | 3 => {},
            _ => {
                unreachable!("can not reach power {}", power);// May be change to option and none?
            }
        }

        let params= self.get_params();
        let frob_c1 = Fp2::constant(T::FROBENIUS_COEFFS_C1[power % 6], params.clone());
        let frob_c2 =  Fp2::constant(T::FROBENIUS_COEFFS_C2[power % 6], params.clone());

        let new_c0 = self.c0.frobenius_power_map(cs, power)?;
        let mut new_c1 = self.c1.frobenius_power_map(cs, power)?;
        let mut new_c2 = self.c2.frobenius_power_map(cs, power)?;
        new_c1 = new_c1.mul_by(cs, &frob_c1)?;
        new_c2 = new_c2.mul_by(cs, &frob_c2)?;
        
        let res = Self::from_coordinates(new_c0, new_c1, new_c2);
        let actual_value = self.get_value().map(|x| {
            let mut tmp = x;
            tmp.frobenius_map(power);
            tmp
        });
        assert_eq!(res.get_value(), actual_value);

        // TODO: get rid of this
        self.get_value().map(|x| {
            let mut tmp = x;
            tmp.frobenius_map(2);
            tmp.frobenius_map(1);
            let mut qr = x;
            qr.frobenius_map(3);
            assert_eq!(tmp, qr);

            qr
        });

        Ok(res)
    }

    pub fn collapse_chain<CS>(cs: &mut CS, chain: Fp6Chain<E, F, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let mut coeffs = Vec::with_capacity(3); 
        for i in 0..3 {
            let subchain = chain.get_coordinate_subchain(i);
            coeffs.push(Fp2::collapse_chain(cs, subchain)?);
        }
        Ok(Self::from_coordinates(coeffs[0].clone(), coeffs[1].clone(), coeffs[2].clone()))
    }

    pub fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: Fp6Chain<E, F, T>, 
    ) -> Result<(), SynthesisError> {
        for i in 0..3 {
            Fp2::enforce_chain_is_zero(cs, chain.get_coordinate_subchain(i))?;
        }
        Ok(())
    }

    pub fn from_boolean(flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let c0 = Fp2::from_boolean(flag, params.clone());
        let c1 = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::zero(params.clone());
        let c2 = <Fp2::<E, F, T::Ex2> as CoreCircuitField<E, <T::Ex2 as Extension2Params<F>>::Witness>>::zero(params);
        Self::from_coordinates(c0, c1, c2)
    }

    pub fn conditional_constant(value: T::Witness, flag: &Boolean, params: Arc<RnsParameters<E>>) -> Self {
        let c_arr = T::convert_from_structured_witness(value);
        let c0 = Fp2::conditional_constant(c_arr[0], flag, params.clone());
        let c1 = Fp2::conditional_constant(c_arr[1], flag, params.clone());
        let c2 = Fp2::conditional_constant(c_arr[2], flag, params);
        Self::from_coordinates(c0, c1, c2)
    }

    pub fn get_params(&self) -> Arc<RnsParameters<E>> {
        self.c0.get_rns_params().clone()
    }
}



  
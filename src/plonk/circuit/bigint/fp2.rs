use super::*;
use super::traits::CircuitField;
use std::ops::Index;
use num_traits::ToPrimitive;
use plonk::circuit::SomeArithmetizable;
use plonk::circuit::bigint::traits::*;
use paste::paste;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq2 as Bn256Fq2;

use crate::bellman::pairing::bls12_381::Fq as Bls12Fq;
use crate::bellman::pairing::bls12_381::Fq2 as Bls12Fq2;

use super::super::curve::secp256k1::fq::Fq as SecpFq;
use super::super::curve::secp256k1::fq2::Fq2 as SecpFq2;


const EXT_DEGREE: usize = 2;
pub trait Extension2Params<E: Engine, F: Field>: FieldExtensionParams<E, F, EXT_DEGREE> {
    // default impl is consistent only with non-residue == -1
    fn is_default_impl() -> bool { true }
}


macro_rules! construct_ext2_params {
    ($curve_name:ident) => {
        paste! {
            #[derive(Clone)]
            pub struct [<$curve_name Extension2Params>] {}

            impl<E> FieldExtensionParams<E,[<$curve_name Fq2>], EXT_DEGREE> for [<$curve_name Extension2Params>] 
            where E: Engine
            {
                type BaseField = [<$curve_name Fq>];
                type BaseCircuitField = FieldElement<E, Self::BaseField>;
                
                fn convert_to_structured_witness(arr: [Self::BaseField; EXT_DEGREE]) -> [<$curve_name Fq2>] {
                    [<$curve_name Fq2>]{ c0: arr[0], c1: arr[1] }
                }

                fn convert_from_structured_witness(val: [<$curve_name Fq2>]) -> [Self::BaseField; EXT_DEGREE] {
                    [val.c0, val.c1]
                }
            }
        }
    }
}

construct_ext2_params!(Bn256);
construct_ext2_params!(Bls12);
construct_ext2_params!(Secp);

// #[derive(Clone)]
// pub struct BLS12Extension2Params {}
// impl<E: Engine> Extension2Params<E, Bls12Fq, EXT_DEGREE> for BLS12Extension2Params {
//     type BaseField =  Bls12Fq2;
//     type BaseCircuitField = FieldElement<E, Bn256Fq>;
//     fn convert_to_structured_witness(c0: Bls12Fq, c1: Bls12Fq) -> Bls12Fq2 {
//         Bls12Fq2 { c0, c1 }
//     }
//     fn convert_from_structured_witness(val: Self::Witness) -> (Bls12Fq, Bls12Fq) {
//         (val.c0, val.c1)
//     }
// }

// #[derive(Clone)]
// pub struct Secp256K1Extension2Params {}
// impl Extension2Params<SecpFq> for Secp256K1Extension2Params {
//     type Witness = SecpFq2;
//     fn convert_to_structured_witness(c0: SecpFq, c1: SecpFq) -> SecpFq2 {
//         SecpFq2 { c0, c1 }
//     }
//     fn convert_from_structured_witness(val: Self::Witness) -> (SecpFq, SecpFq) {
//         (val.c0, val.c1)
//     }
// }


// #[derive(Clone)]
// pub struct Fp2<E: Engine, F: PrimeField, T: Extension2Params<F>> {
//     pub c0: FieldElement<E, F>,
//     pub c1: FieldElement<E, F>,
//     wit: Option<T::Witness>,
//     _marker: std::marker::PhantomData<T>
// }
 
// impl<E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Display for Fp2<E, F, T> {
//     #[inline(always)]
//     fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
//         write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
//     }
// }

// impl<E:Engine, F:PrimeField, T: Extension2Params<F>> std::fmt::Debug for Fp2<E, F, T> {
//     #[inline(always)]
//     fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
//         write!(f, "Fp2({} + {} * u)", self.c0, self.c1)
//     }
// }

// impl<E:Engine, F:PrimeField, T: Extension2Params<F>> Index<usize> for Fp2<E, F, T> {
//     type Output = FieldElement<E, F>;

//     fn index(&self, idx: usize) -> &Self::Output {
//         match idx {
//             0 => &self.c0,
//             1 => &self.c1,
//             _ => panic!("Index should be 0 or 1"),
//         }
//     }
// }

// impl<E:Engine, F:PrimeField, T: Extension2Params<F>> From<FieldElement<E, F>> for Fp2<E, F, T>
// {
//     fn from(x: FieldElement<E, F>) -> Self {
//         let params = x.get_rns_params();
//         let witness = x.get_field_value().map(|fr| T::convert_to_structured_witness(fr, F::zero()));
//         Fp2::<E, F, T> {
//             c0: x,
//             c1: <FieldElement::<E, F> as CircuitField<E, F>>::zero(params),
//             wit: witness,
//             _marker: std::marker::PhantomData::<T>
//         }
//     }    
// }


// impl<E:Engine, F:PrimeField, T: Extension2Params<F>>  Fp2<E, F, T> {
//     pub fn get_base_field_coordinates(&self) -> Vec<FieldElement<E, F>> {
//         vec![self.c0.clone(), self.c1.clone()]
//     }

//     pub fn alloc_from_coordinates<CS: ConstraintSystem<E>>(
//         cs: &mut CS, c0_wit: Option<F>, c1_wit: Option<F>, params: Arc<RnsParameters<E>>
//     ) -> Result<Self, SynthesisError> {
//         let c0 = FieldElement::alloc(cs, c0_wit, params)?;
//         let c1 = FieldElement::alloc(cs, c1_wit, params)?;
//         let wit = match (c0_wit, c1_wit) {
//             (Some(c0), Some(c1)) => Some(T::convert_to_structured_witness(c0, c1)),
//             _ => None,
//         };
//         Ok(Fp2{ c0, c1, wit, _marker: std::marker::PhantomData::<T>})
//     }
    
//     pub fn from_coordinates(c0: FieldElement<E, F>, c1: FieldElement<E, F>) -> Self {
//         let wit = match (c0.get_field_value(), c1.get_field_value()) {
//             (Some(c0), Some(c1)) => Some(T::convert_to_structured_witness(c0, c1)),
//             _ => None,
//         };
//         Fp2 { c0, c1, wit, _marker: std::marker::PhantomData::<T> }
//     }

//     pub fn from_base_field(x: FieldElement<E, F>) -> Self {
//         let params = x.get_rns_params();
//         Fp2::from_coordinates(x, <FieldElement as CircuitField<E, F>>::zero(params))
//     }

//     pub fn get_value_as_coordinates(&self) -> Option<(F, F)> {
//        self.c0.get_field_value().zip(self.c1.get_field_value()) 
//     }
    
//     pub fn constant_from_coordinates(c0: F, c1: F, params: Arc<RnsParameters<E>>) -> Self {
//         Self::from_coordinates(FieldElement::constant(c0, params), FieldElement::constant(c1, params))
//     }

//     fn debug_check_value_coherency(&self) -> () {
//         let (c0_var, c1_var) = self.get_value_as_coordinates().unzip();
//         let (c0_actual, c1_actual) = self.wit.map(|x| T::convert_from_structured_witness(x)).unzip();
//         assert_eq!(c0_var, c0_actual);
//         assert_eq!(c1_var, c1_actual);
//     }
   
//     #[track_caller]
//     pub fn constraint_fma<CS: ConstraintSystem<E>>(
//         cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, T::Witness, Self>
//     ) -> Result<(), SynthesisError> {
//         // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
//         // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
//         // 1) v0 = a0 * b0
//         // 2) v1 = a1 * b1
//         // 3) c0 = v0 + \beta * v1 = v0 - v1
//         // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        
//         // we assume that non_residue = -1
//         assert!(T::is_default_impl());

//         let params = first.get_rns_params();
//         let v0 = first.c0.mul(cs, &second.c0)?;
//         let v1 = first.c1.mul(cs, &second.c1)?;
       
//         let mut subchain = chain.get_coordinate_subchain(0);
//         subchain.add_pos_term(&v0);
//         subchain.add_neg_term(&v1);
//         FieldElement::collapse_chain(cs, subchain)?;
//         //FieldElement::constraint_fma(cs, &FieldElement::zero(params), &FieldElement::zero(params), subchain)?;

//         let a = first.c0.add(cs, &first.c1)?;
//         let b = second.c0.add(cs, &second.c1)?;
//         let mut subchain = chain.get_coordinate_subchain(1);
//         subchain.add_neg_term(&v0);
//         subchain.add_neg_term(&v1);
//         FieldElement::constraint_fma(cs, &a, &b, subchain)?;
//         Ok(())
//     }

//     pub fn mul_with_chain<CS: ConstraintSystem<E>>(
//         cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, T::Witness, Self>
//     ) -> Result<Self, SynthesisError> {
//         // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
//         // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
//         // 1) v0 = a0 * b0
//         // 2) v1 = a1 * b1
//         // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * b0 - v1
//         // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
//         // NB: v0 = c0 + v1 - chain0, c1 = a * b - v0 - v1 + chain1 = a * b - c0 - 2 * v1 + chain0 + chain1

//         // we assume that non_residue = -1
//         assert!(T::is_default_impl());
        
//         let v1 = first.c1.mul(cs, &second.c1)?;
//         let mut subchain = chain.get_coordinate_subchain(0);
//         subchain.add_neg_term(&v1);
//         let c0 = FieldElement::mul_with_chain(cs, &first.c0, &second.c0, subchain)?;

//         let a = first.c0.add(cs, &first.c1)?;
//         let b = second.c0.add(cs, &second.c1)?;
//         let mut subchain = chain.get_coordinate_subchain(1);
//         subchain.add_neg_term(&c0);
//         let x = v1.double(cs)?;
//         subchain.add_neg_term(&x);
//         for elem in chain.get_coordinate_subchain(0).elems_to_add.iter() {
//             subchain.add_pos_term(elem);
//         }
//         for elem in chain.get_coordinate_subchain(0).elems_to_sub.iter() {
//             subchain.add_neg_term(elem);
//         }
//         let c1 = FieldElement::mul_with_chain(cs, &a, &b, subchain)?;
//         Ok(Self::from_coordinates(c0, c1))
//     }
 
//     pub fn square_with_chain<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, chain: FieldElementsChain<E, T::Witness, Self>
//     ) -> Result<Self, SynthesisError> {
//         // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.17
//         // input: a = a0 + u * a1; output: a^2
//         // 1) c1 = 2 * a0 * a1
//         // 2) c0 = (a0 - a1)(a0 + a1)
        
//         // we assume that non_residue = -1
//         assert!(T::is_default_impl());

//         let tmp = self.c0.double(cs)?;
//         let subchain = chain.get_coordinate_subchain(1);
//         let c1 = FieldElement::mul_with_chain(cs, &tmp, &self.c1, subchain)?;

//         let x = self.c0.sub(cs, &self.c1)?;
//         let y = self.c0.add(cs, &self.c1)?;
//         let subchain = chain.get_coordinate_subchain(0);
//         let c0 = FieldElement::mul_with_chain(cs, &x, &y, subchain)?;

//         Ok(Self::from_coordinates(c0, c1))
//     }

//     pub fn inverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
//         let mut num_chain = Fp2Chain::new();
//         num_chain.add_pos_term(&Self::one(&self.c0.representation_params));
//         Self::div_with_chain(cs, num_chain, self)
//     }

//     pub fn div_with_chain<CS>(cs: &mut CS, chain: Fp2Chain<'a, E, F, T>, den: &Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         // we assume that non_residue = -1
//         assert!(T::is_default_impl());
        
//         let params = &den.c0.representation_params;
//         // we do chain/den = result mod p, where we assume that den != 0
//         let (c0, c1) = den.get_value_as_coordinates().unwrap_or((F::one(), F::zero()));
//         assert!(!(c0.is_zero() && c1.is_zero()));

//         // (a0 + u * a1) / (b0 + u * b1) = (a0 + u * a1) * (b0 - u * b1) / (b0^2 - \beta * b1^2) = 
//         // = [1/(b0^2 - \beta * b1^2)] * [(a0 * b0 - \beta a1 * b1) + u * (a1 * b0 - a0 * b1)]
//         let (numerator_c0_wit, numerator_c1_wit)  = chain.get_field_value_as_coordinates();
//         let (den_c0_wit, den_c1_wit) = (den.c0.get_field_value(), den.c1.get_field_value());
//         let (res_c0_wit, res_c1_wit) = match (numerator_c0_wit, numerator_c1_wit, den_c0_wit, den_c1_wit) {
//             (Some(a0), Some(a1), Some(b0), Some(b1)) => {
//                 let beta = T::non_residue();
//                 let mut b0_squared = b0;
//                 b0_squared.square();
//                 let mut b1_squared = b1;
//                 b1_squared.square();
//                 let mut norm = b1_squared;
//                 norm.mul_assign(&beta);
//                 norm.negate();
//                 norm.add_assign(&b0_squared);
//                 let norm_inv = norm.inverse().unwrap();

//                 let mut c0 = a0;
//                 c0.mul_assign(&b0);
//                 let mut tmp = a1;
//                 tmp.mul_assign(&b1);
//                 tmp.mul_assign(&beta);
//                 c0.sub_assign(&tmp); 
//                 c0.mul_assign(&norm_inv);

//                 let mut c1 = a1;
//                 c1.mul_assign(&b0);
//                 let mut tmp = a0;
//                 tmp.mul_assign(&b1);
//                 c1.sub_assign(&tmp);
//                 c1.mul_assign(&norm_inv);
                
//                 (Some(c0), Some(c1))
//             },
//             _ => (None, None),
//         };

//         let all_constants = den.is_constant() && chain.is_constant();
//         if all_constants {
//             let res = Self::constant_from_coordinates(res_c0_wit.unwrap(), res_c1_wit.unwrap(), params);
//             Ok(res)
//         }
//         else {
//             let res = Self::alloc_from_coordinates(cs, res_c0_wit, res_c1_wit, params)?;
//             let chain = chain.negate();
//             Self::constraint_fma(cs, &res, &den, chain)?;
//             Ok(res)
//         }
//     }

//     pub fn frobenius_power_map<CS>(&self, cs: &mut CS, power: usize)-> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         if power % 2 == 0 {
//             return Ok(self.clone())
//         } 
//         else {
//             assert!(T::is_default_impl());
//             let new_c1 = self.c1.negate(cs)?;
//             let new_c0 = self.c0.clone();   
            
//             let res = Self::from_coordinates(new_c0, new_c1);
//             let actual_value = self.get_value().map(|x| {
//                 let mut tmp = x;
//                 tmp.frobenius_map(power);
//                 tmp
//             });
//             assert_eq!(res.get_value(), actual_value);

//             return Ok(res)
//         }
//     }

//     #[track_caller]
//     pub fn mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, scalar: (u64, u64), chain: Fp2Chain<'a, E, F, T>
//     ) -> Result<Self, SynthesisError> {
//         // we assume that non_residue = -1
//         assert!(T::is_default_impl());
//         let (s0, s1) = scalar;
//         // if our small constant is (s0, s1) then:
//         // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
//         // 1) v0 = a0 * b0 = a0 * s0
//         // 2) v1 = a1 * b1 = a1 * s1
//         // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * s0 - a1 * s1
//         // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 = a0 * (s0 + s1) + a1 * (s0 + s1) - a0 * s0 - a1 * s1
//         // hence: c1 = a0 * s1 + a1 * s0

//         let mut subchain = chain.get_coordinate_subchain(0); 
//         subchain.add_pos_term(&self.c0.scale(cs, s0)?);
//         subchain.add_neg_term(&self.c1.scale(cs, s1)?);
//         let c0 = FieldElement::collapse_chain(cs, subchain)?;
        
//         let mut subchain = chain.get_coordinate_subchain(1);
//         subchain.add_pos_term(&self.c0.scale(cs, s1)?);
//         subchain.add_pos_term(&self.c1.scale(cs, s0)?);
//         let c1 = FieldElement::collapse_chain(cs, subchain)?;
        
//         Ok(Self::from_coordinates(c0, c1))
//     }

//     pub fn mul_by_small_constant<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, scalar: (u64, u64)
//     ) -> Result<Self, SynthesisError> {
//         let chain = Fp2Chain::new();
//         self.mul_by_small_constant_with_chain(cs, scalar, chain)
//     }

//     #[track_caller]
//     pub fn constraint_mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
//         cs: &mut CS, elem: &Self, scalar: (u64, u64), chain: Fp2Chain<'a, E, F, T>
//     ) -> Result<(), SynthesisError> {
//         assert!(T::is_default_impl());
//         let (s0, s1) = scalar;
//         // if our small constant is (s0, s1) then:
//         // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
//         // 1) v0 = a0 * b0 = a0 * s0
//         // 2) v1 = a1 * b1 = a1 * s1
//         // 3) c0 = v0 + \beta * v1 = v0 - v1 = a0 * s0 - a1 * s1
//         // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 = a0 * (s0 + s1) + a1 * (s0 + s1) - a0 * s0 - a1 * s1
//         // hence: c1 = a0 * s1 + a1 * s0

//         let mut subchain = chain.get_coordinate_subchain(0); 
//         subchain.add_pos_term(&elem.c0.scale(cs, s0)?);
//         subchain.add_neg_term(&elem.c1.scale(cs, s1)?);
//         FieldElement::enforce_chain_is_zero(cs, subchain)?;
        
//         let mut subchain = chain.get_coordinate_subchain(1);
//         subchain.add_pos_term(&elem.c0.scale(cs, s1)?);
//         subchain.add_pos_term(&elem.c1.scale(cs, s0)?);
//         FieldElement::enforce_chain_is_zero(cs, subchain)
//     }

//     pub fn collapse_chain<CS>(cs: &mut CS, chain: Fp2Chain<'a, E, F, T>) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         let subchain = chain.get_coordinate_subchain(0);
//         let c0 = FieldElement::collapse_chain(cs, subchain)?;
//         let subchain = chain.get_coordinate_subchain(1);
//         let c1 = FieldElement::collapse_chain(cs, subchain)?;

//         Ok(Self::from_coordinates(c0, c1))
//     }

//     pub fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
//         cs: &mut CS, chain: Fp2Chain<'a, E, F, T>, 
//     ) -> Result<(), SynthesisError> {
//         for i in 0..2 {
//             FieldElement::enforce_chain_is_zero(cs, chain.get_coordinate_subchain(i))?;
//         }
//         Ok(())
//     }

//     pub fn from_boolean(flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
//         let c0 = FieldElement::from_boolean(flag, params);
//         let c1 = FieldElement::zero(params);
//         Self::from_coordinates(c0, c1)
//     }

//     pub fn conditional_constant(value: T::Witness, flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
//         let (c0, c1) = T::convert_from_structured_witness(value);
//         let c0 = FieldElement::conditional_constant(c0, flag, params);
//         let c1 = FieldElement::conditional_constant(c1, flag, params);
//         Self::from_coordinates(c0, c1)
//     }

//     pub fn mul_by_base_field<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, base_field_var: &FieldElement<'a, E, F>
//     ) -> Result<Self, SynthesisError> {
//         let new_c0 = self.c0.mul(cs, base_field_var)?;
//         let new_c1 = self.c1.mul(cs, base_field_var)?;
//         Ok(Self::from_coordinates(new_c0, new_c1))
//     }

//     pub fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError> {
//         let new_c0 = self.c0.scale(cs, factor)?;
//         let new_c1 = self.c1.scale(cs, factor)?;
//         Ok(Self::from_coordinates(new_c0, new_c1))
//     }

//     pub fn get_params(&self) -> &'a RnsParameters<E, F> {
//         self.c0.representation_params
//     }
// }





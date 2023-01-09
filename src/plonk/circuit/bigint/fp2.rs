use super::*;
use super::traits::CircuitField;
use std::ops::Index;
use num_traits::ToPrimitive;
use plonk::circuit::SomeArithmetizable;
use plonk::circuit::bigint::traits::*;
use paste::paste;
use serde::__private::de;

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

            impl<E: Engine> Extension2Params<E, [<$curve_name Fq2>]> for [<$curve_name Extension2Params>] {} 
        }
    }
}

construct_ext2_params!(Bn256);
construct_ext2_params!(Bls12);
construct_ext2_params!(Secp);


impl<E: Engine, F: Field, T: Extension2Params<E, F>> std::fmt::Display for ExtField<E, F, EXT_DEGREE, T> 
where T::BaseCircuitField : std::fmt::Display
{
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({} + {} * u)", self[0], self[1])
    }
}

impl<E: Engine, F: Field, T: Extension2Params<E, F>> std::fmt::Debug for ExtField<E, F, EXT_DEGREE, T> 
where T::BaseCircuitField : std::fmt::Debug
{
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({:?} + {:?} * u)", self[0], self[1])
    }
}

impl<E: Engine, F: Field, T: Extension2Params<E, F>> ExtField<E, F, EXT_DEGREE, T> {
    #[track_caller]
    pub fn mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: (u64, u64), chain: FieldElementsChain<E, F, Self>
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
        subchain.add_pos_term(&self[0].scale(cs, s0)?);
        subchain.add_neg_term(&self[1].scale(cs, s1)?);
        let c0 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::collapse_chain(cs, subchain)?;
        
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_pos_term(&self[0].scale(cs, s1)?);
        subchain.add_pos_term(&self[1].scale(cs, s0)?);
        let c1 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::collapse_chain(cs, subchain)?;
        
        Ok(Self::from_coordinates([c0, c1]))
    }

    pub fn mul_by_small_constant<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: (u64, u64)
    ) -> Result<Self, SynthesisError> {
        let chain = FieldElementsChain::new();
        self.mul_by_small_constant_with_chain(cs, scalar, chain)
    }

    #[track_caller]
    pub fn constraint_mul_by_small_constant_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, elem: &Self, scalar: (u64, u64), chain: FieldElementsChain<E, F, Self>
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
        subchain.add_pos_term(&elem[0].scale(cs, s0)?);
        subchain.add_neg_term(&elem[1].scale(cs, s1)?);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::enforce_chain_is_zero(cs, subchain)?;
        
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_pos_term(&elem[0].scale(cs, s1)?);
        subchain.add_pos_term(&elem[1].scale(cs, s0)?);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::enforce_chain_is_zero(cs, subchain)
    }
}


impl<E: Engine, F: Field, T: Extension2Params<E, F>> CircuitField<E, F> for ExtField<E, F, EXT_DEGREE, T> {   
    fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, F, Self>
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
        
        let v1 = first[1].mul_by(cs, &second[1])?;
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_neg_term(&v1);
        let c0 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(
            cs, &first[0], &second[0], subchain
        )?;
    
        let a = first[0].add(cs, &first[1])?;
        let b = second[0].add(cs, &second[1])?;
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
        let c1 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(
            cs, &a, &b, subchain
        )?;
        Ok(Self::from_coordinates([c0, c1]))
    }
    
    fn square_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.17
        // input: a = a0 + u * a1; output: a^2
        // 1) c1 = 2 * a0 * a1
        // 2) c0 = (a0 - a1)(a0 + a1)
        
        // we assume that non_residue = -1
        assert!(T::is_default_impl());
    
        let tmp = self[0].double(cs)?;
        let subchain = chain.get_coordinate_subchain(1);
        let c1 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(
            cs, &tmp, &self[1], subchain
        )?;
    
        let x = self[0].sub(cs, &self[1])?;
        let y = self[0].add(cs, &self[1])?;
        let subchain = chain.get_coordinate_subchain(0);
        let c0 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(
            cs, &x, &y, subchain
        )?;
    
        Ok(Self::from_coordinates([c0, c1]))
    }

    fn div_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<E, F, Self>, den: &Self
    ) -> Result<Self, SynthesisError> {
        // we assume that non_residue = -1
        assert!(T::is_default_impl()); 
        let params = den.get_rns_params();
       
        let res_wit = match (chain.get_value(), den.get_value()) {
            (Some(num), Some(den)) => {
                // we do chain/den = result mod p, where we assume that den != 0
                let mut res = den.inverse().expect("denumerator should be nonzero value in the fiedl");
                res.mul_assign(&num);
                Some(res)
            },
            _ => None, 
        };

        let all_constants = den.is_constant() && chain.is_constant();
        if all_constants {
            let res = Self::constant(res_wit.unwrap(), params);
            Ok(res)
        }
        else {
            let res = Self::alloc(cs, res_wit, params)?;
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
            let new_c1 = self[1].negate(cs)?;
            let new_c0 = self[0].clone();   
            
            let res = Self::from_coordinates([new_c0, new_c1]);
            let actual_value = self.get_value().map(|x| {
                let mut tmp = x;
                tmp.frobenius_map(power);
                tmp
            });
            assert_eq!(res.get_value(), actual_value);

            return Ok(res)
        }
    }

    #[track_caller]
    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, F, Self>
    ) -> Result<(), SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.16
        // for a = a0 + u * a1 and b = b0 + u * b1 compute a * b = c0 + u * c1 [\beta = u^2]
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) c0 = v0 + \beta * v1 = v0 - v1
        // 4) c1 = (a0 + a1) * (b0 + b1) - v0 - v1
        
        // we assume that non_residue = -1
        assert!(T::is_default_impl());

        let params = first.get_rns_params();
        let v0 = first[0].mul_by(cs, &second[0])?;
        let v1 = first[1].mul_by(cs, &second[1])?;
    
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0);
        subchain.add_neg_term(&v1);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::collapse_chain(cs, subchain)?;

        let a = first[0].add(cs, &first[1])?;
        let b = second[0].add(cs, &second[1])?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0);
        subchain.add_neg_term(&v1);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::constraint_fma(cs, &a, &b, subchain)?;
        Ok(())
    }
}

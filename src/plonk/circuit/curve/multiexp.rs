use super::*;
use super::sw_affine::*;
use super::sw_projective::*;
use super::super::permutation_network::*;

use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective,
};
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
};
use crate::bellman::SynthesisError;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::plonk::circuit::hashes_with_tables::utils::*;
use crate::bellman::plonk::commitments::transparent::utils::log2_floor;
use plonk::circuit::bigint::*;
use plonk::circuit::allocated_num::Num;
use plonk::circuit::linear_combination::LinearCombination;
use plonk::circuit::hashes_with_tables::utils::{IdentifyFirstLast, u64_to_ff};
use plonk::circuit::boolean::*;

use itertools::Itertools;
use std::collections::HashMap;
use std::convert::TryInto;


// here all methods are related to scalar multiplication and multiexponentiation
// we are particularly interested in three curves: secp256k1, bn256 and bls12-281
// unfortunately, only bls12-381 has a cofactor, hence in order to preserve exception-freness
// we have to play around projective coordinates and field extensions
struct EndoAuxData<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    point: AffinePoint<'a, E, G, T>,
    point_endo: AffinePoint<'a, E, G, T>,
    point_scalar_decomposition: RangeCheckDecomposition<E>,
    point_endo_scalar_decomposition: RangeCheckDecomposition<E>
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    fn compute_endo_aux_data<CS: ConstraintSystem<E>>(
        cs: &mut CS, point: &Self, scalar: &mut FieldElement<'a, E, G::Scalar>, window: usize
    ) -> Result<EndoAuxData<'a, E, G, T>, SynthesisError> {
        if scalar.is_constant() {
            unimplemented!();
        }

        let params = point.circuit_params;
        let scalar_rns_params = &params.scalar_field_rns_params;
        let base_rns_params = &params.base_field_rns_params;

        let limit = params.get_endomorphism_bitlen_limit();
        let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
            Some(x) => {
                let dcmp = params.calculate_decomposition(x);
                (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
            },
            None => (None, None, None, None)
        };
        let (k1_abs, k1_chunks) = FieldElement::alloc_for_known_bitwidth_with_custom_range_check_granularity(
            cs, k1_abs_wit, limit, scalar_rns_params, window
        )?;
        let (k2_abs, k2_chunks) = FieldElement::alloc_for_known_bitwidth_with_custom_range_check_granularity(
            cs, k2_abs_wit, limit, scalar_rns_params, window
        )?;
        let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
        let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

        // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
        let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
        let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&k1).add_neg_term(&scalar);
        let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
        FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

        let point_modified = point.conditionally_negate(cs, &k1_is_negative_flag)?;
        let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
        let x_endo = point.get_x().mul(cs, &beta)?;
        let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
        let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

        let endo_aux_data = EndoAuxData::<E, G, T> {
            point: point_modified,
            point_endo,
            point_scalar_decomposition: k1_chunks,
            point_endo_scalar_decomposition: k2_chunks
        };
        Ok(endo_aux_data) 
    }
}

// when we allow exceptions accumulator is allowed to be in the main group - it would be just an arbitrary
// point with unknown discrete logarithm. If we aim at exceptionfreeness we take offset_generator to be a point
// defined over E(F_q^2).
// When algorithm is formula is exception-free we say that it is complete
pub enum PointWrapper<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField {
    AffineOverBaseField(AffinePoint<'a, E, G, T>),
    AffineOverExtField(AffinePointExt<'a, E, G, T>),
    HomogeniousForm(ProjectivePoint<'a, E, G, T>)
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> PointWrapper<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    pub fn add_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, x: &mut AffinePoint<'a, E, G, T>, strict: bool
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = if strict { point.add_unequal(cs, x)? } else { point.add_unequal_unchecked(cs, x)?};
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                let res = point_ext.mixed_add_unequal_unchecked(cs, x)?;
                PointWrapper::AffineOverExtField(res)
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                let res = point_proj.add_mixed(cs, x)?;
                PointWrapper::HomogeniousForm(res)
            },
        };

        Ok(res)
    }

    pub fn sub_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, x: &mut AffinePoint<'a, E, G, T>, strict: bool
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = if strict { point.sub_unequal(cs, x)? } else { point.sub_unequal_unchecked(cs, x)?};
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                let res = point_ext.mixed_sub_unequal_unchecked(cs, x)?;
                PointWrapper::AffineOverExtField(res)
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                let res = point_proj.sub_mixed(cs, x)?;
                PointWrapper::HomogeniousForm(res)
            },
        };

        Ok(res)
    }

    pub fn double<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = AffinePoint::double(point, cs)?; 
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                let res = point_ext.double(cs)?;
                PointWrapper::AffineOverExtField(res)
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                let res = point_proj.double(cs)?;
                PointWrapper::HomogeniousForm(res)
            },
        };

        Ok(res)
    }
    
    // pub fn double_add_mixed
    // pub 
}




//     pub fn mul_by_scalar_complete(&mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>)

//     pub fn mul_by_scalar_non_complete()

//     fn mul_by_scalar_impl()

//     pub fn multiexp_complete()
    
//     pub fn multiexp_non_complete()

//     fn mul_by_scalar_inner() 
// }

         


// impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
// where <G as GenericCurveAffine>::Base: PrimeField 
// {
    
//     #[track_caller]
//     pub fn mul_by_scalar_descending_skew_ladder_with_endo<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
//     ) -> Result<Self, SynthesisError> {
//         if let Some(value) = scalar.get_field_value() {
//             assert!(!value.is_zero(), "can not multiply by zero in the current approach");
//         }
//         if scalar.is_constant() {
//             unimplemented!();
//         }

//         let params = self.circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
//         let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//         let x_endo = point.get_x().mul(cs, &beta)?;
//         let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//         let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
//         let mut point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
//         let mut offset_generator = AffinePoint::constant(G::one(), params);
//         let mut acc = offset_generator.add_unequal(cs, &mut point_plus_point_endo)?;
//         let num_of_doubles = k1_decomposition[1..].len();
//         let iter = k1_decomposition[1..].into_iter().zip(k2_decomposition[1..].into_iter()).rev().enumerate();

//         for (_idx, (k1_bit, k2_bit)) in iter {
//             // selection tree looks like following:
//             //                              
//             //                         |true --- P + Q
//             //         |true---k2_bit--|
//             //         |               |false --- P - Q
//             // k1_bit--|
//             //         |        
//             //         |                |true --- -P + Q
//             //         |false---k2_bit--|
//             //                          |false --- -P - Q
//             //
//             // hence:
//             // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
//             // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
//             // res.Y = conditionally_negate(!k1, tmp.Y)
//             let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
//             let selected_x = FieldElement:: conditionally_select(
//                 cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
//             )?;
//             let tmp_y = FieldElement::conditionally_select(
//                 cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
//             )?;
//             let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
//             let mut tmp = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) };
//             acc = acc.double_and_add(cs, &mut tmp)?;
//         }

//         // we subtract either O, or P, or Q or P + Q
//         // selection tree in this case looks like following:
//         //                              
//         //                         |true --- O
//         //         |true---k2_bit--|
//         //         |               |false --- Q
//         // k1_bit--|
//         //         |        
//         //         |                |true --- P
//         //         |false---k2_bit--|
//         //                          |false --- P+Q
//         //
//         let k1_bit = k1_decomposition.first().unwrap();
//         let k2_bit = k2_decomposition.first().unwrap();
//         let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
//         let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &point, &point_plus_point_endo)?;
//         tmp = AffinePoint::conditionally_select(cs, &k1_bit, &point_endo, &tmp)?;
//         let skew_acc = acc.sub_unequal_unchecked(cs, &mut tmp)?;
//         acc = AffinePoint::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
       
//         let as_scalar_repr = biguint_to_repr::<G::Scalar>(BigUint::from(1u64) << num_of_doubles);
//         let scaled_offset_wit = G::one().mul(as_scalar_repr).into_affine();
//         let mut scaled_offset = AffinePoint::constant(scaled_offset_wit, params);
//         let result = acc.sub_unequal_unchecked(cs, &mut scaled_offset)?; 

//         Ok(result)
//     }


//     #[track_caller]
//     pub fn mul_by_scalar_descending_skew_ladder_with_base_ext<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
//     ) -> Result<Self, SynthesisError> {
//         if let Some(value) = scalar.get_field_value() {
//             assert!(!value.is_zero(), "can not multiply by zero in the current approach");
//         }
//         if scalar.is_constant() {
//             unimplemented!();
//         }
        
//         let circuit_params = self.circuit_params;
//         let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;

//         let offset_generator = AffinePointExt::constant(
//             circuit_params.fp2_offset_generator_x_c0, circuit_params.fp2_offset_generator_x_c1,
//             circuit_params.fp2_offset_generator_y_c0, circuit_params.fp2_offset_generator_y_c1,
//             &circuit_params.base_field_rns_params
//         );
//         let mut acc = offset_generator.add_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;
//         let mut y_negated = self.get_y().negate(cs)?;
//         y_negated.reduce(cs)?;
//         let num_of_doubles = scalar_decomposition[1..].len();
      
//         for bit in scalar_decomposition[1..].into_iter().rev() {
//             let selected_y = FieldElement::conditionally_select(cs, &bit, &self.y, &y_negated)?;
//             let mut tmp = AffinePointExt::from(
//                 unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), selected_y, circuit_params) }
//             );
//             acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
//         }

//         let with_skew = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;
//         let flag = scalar_decomposition.first().unwrap();
//         acc = AffinePointExt::conditionally_select(cs, flag, &acc, &with_skew)?;
        
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 
//         // let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//         //     G::from_xy_unchecked(x, y)
//         // });

//        let result = AffinePoint { 
//             x: final_x, 
//             y: final_y, 
//             value: final_value, 
//             circuit_params: self.circuit_params 
//         };
//         Ok(result)
//     }

    
//     #[track_caller]
//     pub fn mul_by_scalar_descending_skew_ladder_with_endo_and_base_ext<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
//     ) -> Result<Self, SynthesisError> {
//         if let Some(value) = scalar.get_field_value() {
//             assert!(!value.is_zero(), "can not multiply by zero in the current approach");
//         }
//         if scalar.is_constant() {
//             unimplemented!();
//         }

//         let params = self.circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
//         let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//         let x_endo = point.get_x().mul(cs, &beta)?;
//         let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//         let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
//         let point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let mut acc = offset_generator.add_unequal_unchecked(
//             cs, &AffinePointExt::from(point_plus_point_endo.clone())
//         )?;
//         let num_of_doubles = k1_decomposition[1..].len();
//         let iter = k1_decomposition[1..].into_iter().zip(k2_decomposition[1..].into_iter()).rev().enumerate();

//         let naive_mul_start = cs.get_current_step_number();
//         for (_idx, (k1_bit, k2_bit)) in iter {
//             // selection tree looks like following:
//             //                              
//             //                         |true --- P + Q
//             //         |true---k2_bit--|
//             //         |               |false --- P - Q
//             // k1_bit--|
//             //         |        
//             //         |                |true --- -P + Q
//             //         |false---k2_bit--|
//             //                          |false --- -P - Q
//             //
//             // hence:
//             // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
//             // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
//             // res.Y = conditionally_negate(!k1, tmp.Y)
//             let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
//             let selected_x = FieldElement:: conditionally_select(
//                 cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
//             )?;
//             let tmp_y = FieldElement::conditionally_select(
//                 cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
//             )?;
//             let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
//             let mut tmp = AffinePointExt::from(
//                 unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) }
//             );
//             acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
//         }
//         let naive_mul_end = cs.get_current_step_number();
//         println!("gates fpr main cycle: {}", naive_mul_end - naive_mul_start);

//         // we subtract either O, or P, or Q or P + Q
//         // selection tree in this case looks like following:
//         //                              
//         //                         |true --- O
//         //         |true---k2_bit--|
//         //         |               |false --- Q
//         // k1_bit--|
//         //         |        
//         //         |                |true --- P
//         //         |false---k2_bit--|
//         //                          |false --- P+Q
//         //
//         let k1_bit = k1_decomposition.first().unwrap();
//         let k2_bit = k2_decomposition.first().unwrap();
//         let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
//         let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &point, &point_plus_point_endo)?;
//         tmp = AffinePoint::conditionally_select(cs, &k1_bit, &point_endo, &tmp)?;
//         let skew_acc = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(tmp))?;
//         acc = AffinePointExt::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
       
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 

//        let result = AffinePoint { 
//             x: final_x, 
//             y: final_y, 
//             value: final_value, 
//             is_in_subgroup: self.is_in_subgroup, 
//             circuit_params: self.circuit_params 
//         };
//         Ok(result)
//     }


//     #[track_caller]
//     pub fn test_selector_tree<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
//     ) -> Result<Self, SynthesisError> {
//         if let Some(value) = scalar.get_field_value() {
//             assert!(!value.is_zero(), "can not multiply by zero in the current approach");
//         }
//         if scalar.is_constant() {
//             unimplemented!();
//         }

//         let params = self.circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
//         let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//         let x_endo = point.get_x().mul(cs, &beta)?;
//         let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//         let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//         let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
        
//         let points = [point, point_endo];
//         let selector_tree = SelectorTree::new(cs, &points[..])?;
//         let initial_acc = selector_tree.get_initial_accumulator();
       
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let mut acc = offset_generator.add_unequal_unchecked(
//             cs, &AffinePointExt::from(initial_acc)
//         )?;
//         let num_of_doubles = k1_decomposition[1..].len();
//         let iter = k1_decomposition.into_iter().zip(k2_decomposition.into_iter()).rev().identify_first_last();

//         let naive_mul_start = cs.get_current_step_number();
//         for (_is_first, is_last, (k1_bit, k2_bit)) in iter {
//             let flags = [k1_bit, k2_bit];
//             if !is_last {
//                 let tmp = selector_tree.select(cs, &flags[..])?;
//                 let mut tmp = AffinePointExt::from(tmp);
                    
//                 acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
//             }
//             else {
//                 let naive_mul_end = cs.get_current_step_number();
//                 println!("gates fpr main cycle: {}", naive_mul_end - naive_mul_start);
//                 let tmp = selector_tree.select_last(cs, &flags[..])?;
//                 let mut tmp = AffinePointExt::from(tmp);
//                 acc = acc.add_unequal_unchecked(cs, &mut tmp)?;
//             }
//         }
       
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 

//        let result = AffinePoint { 
//             x: final_x, 
//             y: final_y, 
//             value: final_value, 
//             is_in_subgroup: self.is_in_subgroup, 
//             circuit_params: self.circuit_params 
//         };
//         Ok(result)
//     }

//     #[track_caller]
//     pub fn test_ram<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
//     ) -> Result<Self, SynthesisError> {
//         if let Some(value) = scalar.get_field_value() {
//             assert!(!value.is_zero(), "can not multiply by zero in the current approach");
//         }
//         if scalar.is_constant() {
//             unimplemented!();
//         }

//         let params = self.circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
//         let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//         let x_endo = point.get_x().mul(cs, &beta)?;
//         let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//         let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//         let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
        
//         let points = [point, point_endo];
//         let selector_tree = SelectorTree::new(cs, &points[..])?;
//         let initial_acc = selector_tree.get_initial_accumulator();
       
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let mut acc = offset_generator.add_unequal_unchecked(
//             cs, &AffinePointExt::from(initial_acc)
//         )?;
//         let num_of_doubles = k1_decomposition[1..].len();
//         let iter = k1_decomposition.into_iter().zip(k2_decomposition.into_iter()).rev().identify_first_last();

//         let naive_mul_start = cs.get_current_step_number();
//         for (_is_first, is_last, (k1_bit, k2_bit)) in iter {
//             let flags = [k1_bit, k2_bit];
//             if !is_last {
//                 let tmp = selector_tree.select(cs, &flags[..])?;
//                 let mut tmp = AffinePointExt::from(tmp);
                    
//                 acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
//             }
//             else {
//                 let naive_mul_end = cs.get_current_step_number();
//                 println!("gates fpr main cycle: {}", naive_mul_end - naive_mul_start);
//                 let tmp = selector_tree.select_last(cs, &flags[..])?;
//                 let mut tmp = AffinePointExt::from(tmp);
//                 acc = acc.add_unequal_unchecked(cs, &mut tmp)?;
//             }
//         }
       
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 

//        let result = AffinePoint { 
//             x: final_x, 
//             y: final_y, 
//             value: final_value, 
//             is_in_subgroup: self.is_in_subgroup, 
//             circuit_params: self.circuit_params 
//         };
//         Ok(result)
//     }


    
//     #[track_caller]
//     pub fn safe_multiexp_affine<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self] 
//     ) -> Result<Self, SynthesisError> {
//         let params = points[0].circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let limit = params.get_endomorphism_bitlen_limit();

//         struct PointAuxData<'a1, E1: Engine, G1: GenericCurveAffine + rand::Rand, T1: Extension2Params<G1::Base>> 
//         where <G1 as GenericCurveAffine>::Base: PrimeField 
//         {
//             point: AffinePoint<'a1, E1, G1, T1>,
//             point_endo: AffinePoint<'a1, E1, G1, T1>,
//             point_plus_point_endo: AffinePoint<'a1, E1, G1, T1>,
//             point_minus_point_endo: AffinePoint<'a1, E1, G1, T1>,
//             point_scalar_decomposition: Vec<Boolean>,
//             point_endo_scalar_decomposition: Vec<Boolean>
//         }

//         let mut points_aux_data = Vec::<PointAuxData::<E, G, T>>::with_capacity(scalars.len());
//         for (scalar, point) in scalars.iter().zip(points.iter()) { 
//             let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//                 Some(x) => {
//                     let dcmp = params.calculate_decomposition(x);
//                     (
//                         Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
//                         Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
//                     )
//                 },
//                 None => (None, None, None, None)
//             };
//             let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k1_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k2_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//             let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//             // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//             let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut chain = FieldElementsChain::new();
//             chain.add_pos_term(&k1).add_neg_term(&scalar);
//             let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//             FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//             let mut point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//             let x_endo = point.get_x().mul(cs, &beta)?;
//             let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//             let point_scalar_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let point_endo_scalar_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let point_minus_point_endo = point_reg.sub_unequal_unchecked(cs, &mut point_endo)?;
//             let point_plus_point_endo = point_reg.add_unequal_unchecked(cs, &point_endo)?;

//             let point_aux_data = PointAuxData {
//                 point: point_reg, point_endo, point_plus_point_endo, point_minus_point_endo,
//                 point_scalar_decomposition, point_endo_scalar_decomposition
//             };
//             points_aux_data.push(point_aux_data);
//         }
       
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         // let offset_generator = AffinePointExt::constant(
//         //     params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1,
//         //     params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
//         //     &params.base_field_rns_params
//         // );
        
//         let mut acc = offset_generator.clone();
//         for point_aux_data in points_aux_data.iter() {
//             acc = acc.add_unequal_unchecked(
//                 cs, &AffinePointExt::from(point_aux_data.point_plus_point_endo.clone())
//             )?;
//         }
        
//         let num_of_doubles = points_aux_data[0].point_scalar_decomposition.len() - 1;
//         let mut idx = num_of_doubles; 
//         while idx > 0 {
//             for (is_first, _is_last, data) in points_aux_data.iter().identify_first_last() {
//                 let k1_bit = data.point_scalar_decomposition[idx];
//                 let k2_bit = data.point_endo_scalar_decomposition[idx];
//                 // selection tree looks like following:
//                 //                              
//                 //                         |true --- P + Q
//                 //         |true---k2_bit--|
//                 //         |               |false --- P - Q
//                 // k1_bit--|
//                 //         |        
//                 //         |                |true --- -P + Q
//                 //         |false---k2_bit--|
//                 //                          |false --- -P - Q
//                 //
//                 // hence:
//                 // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
//                 // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
//                 // res.Y = conditionally_negate(!k1, tmp.Y)
//                 let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
//                 let selected_x = FieldElement:: conditionally_select(
//                     cs, &xor_flag, &data.point_minus_point_endo.get_x(), &data.point_plus_point_endo.get_x()
//                 )?;
//                 let tmp_y = FieldElement::conditionally_select(
//                     cs, &xor_flag, &data.point_minus_point_endo.get_y(), &data.point_plus_point_endo.get_y()
//                 )?;
//                 let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
//                 let mut tmp = AffinePointExt::from(
//                     unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) }
//                 );
//                 acc = if is_first { 
//                     acc.double_and_add_unchecked(cs, &mut tmp)? 
//                 } else {
//                     acc.add_unequal_unchecked(cs, &mut tmp)? 
//                 };
//             }
//             idx -= 1;
//         }

//         for data in points_aux_data.iter() {
//             let k1_bit = data.point_scalar_decomposition[idx];
//             let k2_bit = data.point_endo_scalar_decomposition[idx];
//             // we subtract either O, or P, or Q or P + Q
//             // selection tree in this case looks like following:
//             //                              
//             //                         |true --- O
//             //         |true---k2_bit--|
//             //         |               |false --- Q
//             // k1_bit--|
//             //         |        
//             //         |                |true --- P
//             //         |false---k2_bit--|
//             //                          |false --- P+Q
//             //
//             let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
//             let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &data.point, &data.point_plus_point_endo)?;
//             tmp = AffinePoint::conditionally_select(cs, &k1_bit, &data.point_endo, &tmp)?;
//             let skew_acc = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(tmp))?;
//             acc = AffinePointExt::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
//         }
       
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 

//        let result = AffinePoint { 
//             x: final_x, 
//             y: final_y, 
//             value: final_value, 
//             is_in_subgroup: points[0].is_in_subgroup, 
//             circuit_params: points[0].circuit_params 
//         };
//         Ok(result)
//     }

//     pub fn safe_multiexp_affine2<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
//     ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
//         assert_eq!(scalars.len(), points.len());
//         let params = points[0].circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let limit = params.get_endomorphism_bitlen_limit();
        
//         struct Multizip<T>(Vec<T>);
        
//         impl<T> Iterator for Multizip<T>
//         where T: Iterator,
//         {
//             type Item = Vec<T::Item>;

//             fn next(&mut self) -> Option<Self::Item> {
//                 self.0.iter_mut().map(Iterator::next).collect()
//             }
//         }

//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let adj_offset = AffinePointExt::constant(
//             params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
//             params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
//             &params.base_field_rns_params
//         );

//         let mut points_unrolled = Vec::with_capacity(points.len() << 1);
//         let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
//         for (is_first, _is_last, (scalar, point)) in scalars.iter().zip(points.iter()).identify_first_last() { 
//             let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//                 Some(x) => {
//                     let dcmp = params.calculate_decomposition(x);
//                     (
//                         Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
//                         Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
//                     )
//                 },
//                 None => (None, None, None, None)
//             };
//             let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k1_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k2_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//             let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//             // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//             let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut chain = FieldElementsChain::new();
//             chain.add_pos_term(&k1).add_neg_term(&scalar);
//             let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//             FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//             let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//             let x_endo = point.get_x().mul(cs, &beta)?;
//             let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//             let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//             let mut point_ext = AffinePointExt::<E, G, T>::from(point_reg);
//             if is_first {
//                 point_ext = point_ext.add_unequal_unchecked(cs, &adj_offset)?;
//             }
//             let point_endo_ext = AffinePointExt::<E, G, T>::from(point_endo);
//             points_unrolled.push(point_ext);
//             points_unrolled.push(point_endo_ext);

//             let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             scalars_unrolled.push(k1_decomposition.into_iter().rev());
//             scalars_unrolled.push(k2_decomposition.into_iter().rev());
//         }

//         let selector_tree = SelectorTree::new(cs, &points_unrolled)?;
//         let mut acc = selector_tree.get_initial_accumulator();
//         acc = acc.add_unequal_unchecked(cs, &offset_generator)?;

//         for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
//             if !is_last {
//                 let to_add = selector_tree.select(cs, &bits)?;
//                 acc = acc.double_and_add_unchecked(cs, &to_add)?;
//             }
//             else {
//                 let to_add = selector_tree.select_last(cs, &bits)?;
//                 acc = acc.add_unequal_unchecked(cs, &to_add)?;
//             }
//         }

//         let gate_count_start = cs.get_current_step_number();
//         let num_of_doubles = limit - 1;
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         let gate_count_end = cs.get_current_step_number();
//         assert_eq!(gate_count_end - gate_count_start, 0);
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

//         let is_defined_over_base_field = |point: &AffinePointExt<'a, E, G, T>| -> Option<bool> {
//             point.get_value().map(|(_x_c0, x_c1, _y_c0, y_c1)| x_c1.is_zero() && y_c1.is_zero())
//         };

//         println!("before last check");

//         // adj_offset is a point of order 3, hence one of acc, acc + adj_offset, acc - adj belong to E(F_p)
//         let need_to_negate_wit = acc.get_value().map(|(x_c0, x_c1, y_c0, y_c1)| {
//             let gate_count_start = cs.get_current_step_number();

//             let mut tmp = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, base_rns_params);
//             tmp = tmp.add_unequal_unchecked(cs, &adj_offset).expect("should synthesize");
//             let flag = is_defined_over_base_field(&tmp).expect("should be some");    
               
//             let gate_count_end = cs.get_current_step_number();
//             assert_eq!(gate_count_end - gate_count_start, 0);
//             !flag
//         });

//         println!("after last check");


//         let need_to_negate = Boolean::Is(AllocatedBit::alloc(cs, need_to_negate_wit)?);
//         let to_add = adj_offset.conditionally_negate(cs, &need_to_negate)?;
//         let modified_acc = acc.add_unequal_unchecked(cs, &to_add)?;
        
//         let cond_wit = is_defined_over_base_field(&modified_acc);
//         let cond = Boolean::Is(AllocatedBit::alloc(cs, cond_wit)?);
//         let res_ext = AffinePointExt::conditionally_select(cs, &cond, &modified_acc, &acc)?; 

//         let mut final_x = res_ext.get_x();
//         let mut final_y = res_ext.get_y();
//         let final_value = final_x.c0.get_field_value().zip(final_y.c0.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 
//         let mut zero = FieldElement::<E, G::Base>::zero(base_rns_params);
//         FieldElement::enforce_equal(cs, &mut final_x.c1, &mut zero)?;
//         FieldElement::enforce_equal(cs, &mut final_y.c1, &mut zero)?;

//         println!("THE VERY FINAL VALUE: {}", final_value.unwrap());


//         let new = Self {
//             x: final_x.c0,
//             y: final_y.c0,
//             value: final_value,
//             is_in_subgroup: true,
//             circuit_params: params
//         };
//         Ok(new)
//     }

//     pub fn safe_multiexp_affine3<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
//     ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
//         assert_eq!(scalars.len(), points.len());
//         let params = points[0].circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let limit = params.get_endomorphism_bitlen_limit();
        
//         struct Multizip<T>(Vec<T>);
        
//         impl<T> Iterator for Multizip<T>
//         where T: Iterator,
//         {
//             type Item = Vec<T::Item>;

//             fn next(&mut self) -> Option<Self::Item> {
//                 self.0.iter_mut().map(Iterator::next).collect()
//             }
//         }

//         let mut points_unrolled = Vec::with_capacity(points.len() << 1);
//         let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
//         for (scalar, point) in scalars.iter().zip(points.iter()) { 
//             let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//                 Some(x) => {
//                     let dcmp = params.calculate_decomposition(x);
//                     (
//                         Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
//                         Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
//                     )
//                 },
//                 None => (None, None, None, None)
//             };
//             let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k1_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k2_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//             let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//             // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//             let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut chain = FieldElementsChain::new();
//             chain.add_pos_term(&k1).add_neg_term(&scalar);
//             let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//             FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//             let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//             let x_endo = point.get_x().mul(cs, &beta)?;
//             let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//             let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//             points_unrolled.push(point_reg);
//             points_unrolled.push(point_endo);

//             let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             scalars_unrolled.push(k1_decomposition.into_iter().rev());
//             scalars_unrolled.push(k2_decomposition.into_iter().rev());
//         }

//         let selector_tree = SelectorTree2::new(cs, &points_unrolled)?;
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let mut acc = selector_tree.add_initial_into_accumulator(cs, &offset_generator)?;

//         for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
//             if !is_last {
//                 acc = selector_tree.double_and_add_selected(cs, &acc, &bits)?;
//             }
//             else {
//                 acc = selector_tree.add_last_into_accumulator(cs, &acc, &bits)?;
//             }
//         }

//         let gate_count_start = cs.get_current_step_number();
//         let num_of_doubles = limit - 1;
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         let gate_count_end = cs.get_current_step_number();
//         assert_eq!(gate_count_end - gate_count_start, 0);
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

//         let adj_offset = AffinePointExt::constant(
//             params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
//             params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
//             &params.base_field_rns_params
//         );

//         let is_defined_over_base_field = |point: &AffinePointExt<'a, E, G, T>| -> Option<bool> {
//             point.get_value().map(|(_x_c0, x_c1, _y_c0, y_c1)| x_c1.is_zero() && y_c1.is_zero())
//         };

//         // adj_offset is a point of order 3, hence one of acc, acc + adj_offset, acc - adj belong to E(F_p)
//         let need_to_negate_wit = acc.get_value().map(|(x_c0, x_c1, y_c0, y_c1)| {
//             let gate_count_start = cs.get_current_step_number();

//             let mut tmp = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, base_rns_params);
//             tmp = tmp.add_unequal_unchecked(cs, &adj_offset).expect("should synthesize");
//             let flag = is_defined_over_base_field(&tmp).expect("should be some");    
                
//             let gate_count_end = cs.get_current_step_number();
//             assert_eq!(gate_count_end - gate_count_start, 0);
//             !flag
//         });

//         let need_to_negate = Boolean::Is(AllocatedBit::alloc(cs, need_to_negate_wit)?);
//         let to_add = adj_offset.conditionally_negate(cs, &need_to_negate)?;
//         let modified_acc = acc.add_unequal_unchecked(cs, &to_add)?;
        
//         let cond_wit = is_defined_over_base_field(&modified_acc);
//         let cond = Boolean::Is(AllocatedBit::alloc(cs, cond_wit)?);
//         acc = AffinePointExt::conditionally_select(cs, &cond, &modified_acc, &acc)?; 

//         let mut final_x = acc.get_x();
//         let mut final_y = acc.get_y();
//         let final_value = final_x.c0.get_field_value().zip(final_y.c0.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 
//         let mut zero = FieldElement::<E, G::Base>::zero(base_rns_params);
//         FieldElement::enforce_equal(cs, &mut final_x.c1, &mut zero)?;
//         FieldElement::enforce_equal(cs, &mut final_y.c1, &mut zero)?;

//         let new = Self {
//             x: final_x.c0,
//             y: final_y.c0,
//             value: final_value,
//             is_in_subgroup: true,
//             circuit_params: params
//         };
//         Ok(new)
//     }

//     pub fn safe_multiexp_affine4<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
//     ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
//         assert_eq!(scalars.len(), points.len());
//         let params = points[0].circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let limit = params.get_endomorphism_bitlen_limit();
        
//         struct Multizip<T>(Vec<T>);
        
//         impl<T> Iterator for Multizip<T>
//         where T: Iterator,
//         {
//             type Item = Vec<T::Item>;

//             fn next(&mut self) -> Option<Self::Item> {
//                 self.0.iter_mut().map(Iterator::next).collect()
//             }
//         }

//         let mut points_unrolled = Vec::with_capacity(points.len() << 1);
//         let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
//         for (scalar, point) in scalars.iter().zip(points.iter()) { 
//             let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//                 Some(x) => {
//                     let dcmp = params.calculate_decomposition(x);
//                     (
//                         Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
//                         Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
//                     )
//                 },
//                 None => (None, None, None, None)
//             };
//             let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k1_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k2_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//             let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//             // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//             let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut chain = FieldElementsChain::new();
//             chain.add_pos_term(&k1).add_neg_term(&scalar);
//             let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//             FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//             let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//             let x_endo = point.get_x().mul(cs, &beta)?;
//             let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//             let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//             points_unrolled.push(point_reg);
//             points_unrolled.push(point_endo);

//             let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             scalars_unrolled.push(k1_decomposition.into_iter().rev());
//             scalars_unrolled.push(k2_decomposition.into_iter().rev());
//         }

//         let mut selector_tree = SelectorTree3::new(cs, &points_unrolled)?;
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
//         let mut acc = selector_tree.add_initial_into_accumulator(cs, &offset_generator)?;

//         for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
//             if !is_last {
//                 acc = selector_tree.double_and_add_selected(cs, &acc, &bits)?;
//             }
//             else {
//                 acc = selector_tree.add_last_into_accumulator(cs, &acc, &bits)?;
//             }
//         }

//         let gate_count_start = cs.get_current_step_number();
//         let num_of_doubles = limit - 1;
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         let gate_count_end = cs.get_current_step_number();
//         assert_eq!(gate_count_end - gate_count_start, 0);
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

//         let mut final_x = acc.get_x();
//         let mut final_y = acc.get_y();
//         let final_value = final_x.c0.get_field_value().zip(final_y.c0.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         }); 
//         let mut zero = FieldElement::<E, G::Base>::zero(base_rns_params);
//         FieldElement::enforce_equal(cs, &mut final_x.c1, &mut zero)?;
//         FieldElement::enforce_equal(cs, &mut final_y.c1, &mut zero)?;

//         let new = Self {
//             x: final_x.c0,
//             y: final_y.c0,
//             value: final_value,
//             is_in_subgroup: true,
//             circuit_params: params
//         };
//         Ok(new)
//     } 
    

//     pub fn mul_generator_by_scalar<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalar: &FieldElement<'a, E, G::Scalar>, window: usize, 
//         params: &'a CurveCircuitParameters<E, G, T>
//     ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
//         assert!(window >= 2);
//         let columns3 = vec![
//             PolyIdentifier::VariablesPolynomial(0), 
//             PolyIdentifier::VariablesPolynomial(1), 
//             PolyIdentifier::VariablesPolynomial(2)
//         ];
//         let name : &'static str = GEN_SCALAR_MUL_TABLE_NAME;
//         let counter_start = cs.get_current_step_number();
//         let table = get_or_create_table(
//             cs, name,
//             || {
//                 LookupTableApplication::new(
//                     name,
//                     GeneratorScalarMulTable::new::<G, T>(window, name, params),
//                     columns3.clone(),
//                     None,
//                     true
//                 )
//             } 
//         ).unwrap();
//         let counter_end = cs.get_current_step_number();
//         println!("gates for table alloc: {}", counter_end - counter_start);
        
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let shifts = compute_shifts::<E::Fr>();

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let (k1_abs, k1_chunks) = FieldElement::alloc_for_known_bitwidth_with_custom_range_check_granularity(
//             cs, k1_abs_wit, limit, scalar_rns_params, window
//         )?;
//         let (k2_abs, k2_chunks) = FieldElement::alloc_for_known_bitwidth_with_custom_range_check_granularity(
//             cs, k2_abs_wit, limit, scalar_rns_params, window
//         )?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let generator = G::one();
//         let generator_endo = {
//             let (mut x, y) = generator.clone().into_xy_unchecked();
//             x.mul_assign(&params.beta); 
//             G::from_xy_checked(x, y).expect("should be a valid point")
//         };
//         let generator_plus_generator_endo = {
//             let mut tmp = generator.into_projective();
//             tmp.add_assign_mixed(&generator_endo);
//             tmp.into_affine()
//         };
//         let generator_minus_generator_endo = {
//             let mut tmp = generator_endo.into_projective();
//             tmp.negate();
//             tmp.add_assign_mixed(&generator);
//             tmp.into_affine()
//         };

//         let mut lc = LinearCombination::zero();
//         lc.add_assign_boolean_with_coeff(&k1_is_negative_flag, shifts[0]);
//         lc.add_assign_boolean_with_coeff(&k2_is_negative_flag, shifts[1]);
//         let sign_bits = lc.into_num(cs)?;

//         let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
//         let cnst_term_idx = CS::MainGate::index_for_constant_term();

//         let dummy = AllocatedNum::zero(cs);
//         let mut minus_one = E::Fr::one();
//         minus_one.negate();
        
//         // select_y_limbs | limb_idx_selector | sign_k1 | sign_k0 | k1 | k0
//         let k1_offset = 0;
//         let k2_offset = window;
//         let sign_offset = window * 2;
//         let limb_idx_selector_offset = sign_offset + 2;
//         let idx_width = crate::log2_floor(params.base_field_rns_params.num_binary_limbs / 2) as usize;
//         let x_or_y_flag_offset = limb_idx_selector_offset + idx_width;

//         let query_point = |cs: &mut CS, k1_chunk: &Num<E>, k2_chunk: &Num<E>| -> Result<Self, SynthesisError> {
//             let mut lc = LinearCombination::zero();
//             lc.add_assign_number_with_coeff(&k1_chunk, shifts[k1_offset]);
//             lc.add_assign_number_with_coeff(&k2_chunk, shifts[k2_offset]);
//             lc.add_assign_number_with_coeff(&sign_bits, shifts[sign_offset]);
//             let base = lc.into_num(cs)?.get_variable();
            

//             let mut x = FieldElement::zero(base_rns_params);
//             let mut y = FieldElement::zero(base_rns_params);
//             let iter = std::iter::once((&mut x, false)).chain(std::iter::once((&mut y, true)));
//             for (out, x_y_flag) in iter {
//                 let mut raw_limbs = Vec::with_capacity(base_rns_params.num_binary_limbs);
//                 for idx in 0..base_rns_params.num_binary_limbs/ 2 {
//                     let counter_start = cs.get_current_step_number();
//                     let mut prefix = u64_to_ff::<E::Fr>(idx as u64);
//                     prefix.mul_assign(&shifts[limb_idx_selector_offset]);
//                     if x_y_flag {
//                         prefix.add_assign(&shifts[x_or_y_flag_offset])
//                     }
                    
//                     let a = AllocatedNum::alloc(cs, || {
//                         let mut tmp = base.get_value().grab()?;
//                         tmp.add_assign(&prefix);
//                         Ok(tmp)
//                     })?;
//                     let (b, c) = match a.get_value() {
//                         None => {
//                             (
//                                 AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?, 
//                                 AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
//                             )
//                         },
//                         Some(val) => {
//                             println!("val: {}", val);
//                             let vals = table.query(&[val])?;
//                             println!("queried");
//                             (AllocatedNum::alloc(cs, || Ok(vals[0]))?, AllocatedNum::alloc(cs, || Ok(vals[1]))?)
//                         },     
//                     };

//                     let vars = [a.get_variable(), b.get_variable(), c.get_variable(), base.get_variable()];
//                     let coeffs = [minus_one.clone(), E::Fr::zero(), E::Fr::zero(), E::Fr::one()];
//                     let counter_end = cs.get_current_step_number();
//                     println!("gates for table query: {}", counter_end - counter_start);
                    
                   
//                     cs.begin_gates_batch_for_step()?;
//                     cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
                
//                     let gate_term = MainGateTerm::new();
//                     let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy.get_variable())?;
//                     for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
//                         gate_coefs[idx] = *coef;
//                     }
//                     gate_coefs[cnst_term_idx] = prefix;
                   
//                     let mg = CS::MainGate::default();
//                     cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
//                     cs.end_gates_batch_for_step()?;

//                     raw_limbs.push(Num::Variable(b));
//                     raw_limbs.push(Num::Variable(c));
//                 }
               
//                *out = unsafe { FieldElement::alloc_from_limbs_unchecked(cs, &raw_limbs, base_rns_params, true)? };
//             }

//             let res = unsafe { AffinePoint::from_xy_unchecked(x, y, params) };
//             Ok(res)
//         };
        
//         let offset_generator = AffinePointExt::constant(
//             params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
//             params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
//             &params.base_field_rns_params
//         );
        
//         let mut acc = AffinePointExt::from(query_point(cs, &Num::<E>::zero(), &Num::<E>::zero())?);
//         let mut num_of_doubles = 0;

//         let iter = k1_chunks.get_vars().iter().zip(k2_chunks.get_vars().iter()).rev().identify_first_last();
//         for (is_first, _is_last, (k1_chunk, k2_chunk)) in iter {
//             if is_first {
//                 let tmp = limit % window;
//                 let msl_window = if tmp != 0 { tmp } else { window };
//                 assert!(msl_window >= 2);
//                 for _ in 0..msl_window-2 {
//                     acc = acc.double(cs)?;
//                 }
//                 acc = acc.double_and_add_unchecked(cs, &offset_generator)?;
//             }
//             else {
//                 num_of_doubles += window - 1; 
//                 for _ in 0..window-1 {
//                     acc = acc.double(cs)?;
//                 }
//             } 

//             let to_add = query_point(cs, &Num::Variable(*k1_chunk), &Num::Variable(*k2_chunk))?;
//             acc = acc.double_and_add_unchecked(cs, &AffinePointExt::from(to_add))?;
//             num_of_doubles += 1;
//         }

//         let k1_parity_bit = Self::get_parity_bit(cs, &Term::from_allocated_num(k1_chunks.get_vars()[0]), window)?;
//         let k2_parity_bit = Self::get_parity_bit(cs, &Term::from_allocated_num(k1_chunks.get_vars()[0]), window)?;

//         // fro table: 0 -> P, 1: -P
//         // we need: 0 -> 0 1: -P,
//         // hence we use table to get point but then do: 
//         // we additionally add linear combination of the form a * P + b * Q, where both a, b \in {-1, 0, 1}
//         // and a = k1_is_negative * k1_parity_bit and similarly b = k2_s_negative * k2_parity_bit
//         // we say that P and Q are of the same sign of k1_is_negative and k2_is_negative are simultaneously
//         // set or reset
//         // we say that P exists if k1_parity_bit is set, similarly for Q
//         // acc is unchanges if both parity_bits are unset
//         // in case acc is changed selection tree looks like following:
//         //                              
//         //                                                        |true --- P + Q
//         //                     |true--- P and Q of the same sign--|
//         //                     |                                  |false --- P - Q
//         // both P and Q exist--|
//         //                     |        
//         //                     |                                               |--- P
//         //                     |false: only one of them exists: select which --|                            |--Q
//         //                                                                     |--P and Q of the same sign--|
//         //                                                                                                  |-(-Q)
//         // after selection we do negation based on sign of P alone 
//         let generator = AffinePoint::constant(generator, params);
//         let generator_endo = AffinePoint::constant(generator_endo, params);
//         let generator_plus_generator_endo = AffinePoint::constant(generator_plus_generator_endo, params);
//         let generator_minus_generator_endo = AffinePoint::constant(generator_minus_generator_endo, params);

//         let acc_is_changed = Boolean::or(cs, &k1_parity_bit, &k2_parity_bit)?; 
//         let both_exist = Boolean::and(cs, &k1_parity_bit, &k2_parity_bit)?;
//         let of_the_same_sign = Boolean::xor(cs, &k1_is_negative_flag, &k2_is_negative_flag)?.not();

//         let tmp1 = AffinePoint::conditionally_select(
//             cs, &of_the_same_sign, &generator_plus_generator_endo, &generator_minus_generator_endo
//         )?;
//         let tmp2 = generator_endo.conditionally_negate(cs, &of_the_same_sign.not())?;
//         let tmp3 = AffinePoint::conditionally_select(cs, &k1_parity_bit, &generator, &tmp2)?;
//         let tmp4 = AffinePoint::conditionally_select(cs, &both_exist, &tmp1, &tmp3)?;
//         let tmp = tmp4.conditionally_negate(cs, &k1_is_negative_flag)?;

//         let skew_acc = acc.add_unequal_unchecked(cs, &AffinePointExt::from(tmp))?;
//         acc = AffinePointExt::conditionally_select(cs, &acc_is_changed, &skew_acc, &acc)?;
       
//         let mut scaled_offset = offset_generator;
//         for _ in 0..num_of_doubles {
//             scaled_offset = scaled_offset.double(cs)?;
//         }
//         acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

//         let final_x = acc.get_x().c0;
//         let final_y = acc.get_y().c0;
//         let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
//             G::from_xy_checked(x, y).expect("should be on the curve")
//         });
//         println!("at the end");

//         let result = Self {
//             x: final_x,
//             y: final_y,
//             value: final_value,
//             is_in_subgroup: true,
//             circuit_params: params
//         };
//         Ok(result)
//     }
// }


// impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
// where <G as GenericCurveAffine>::Base: PrimeField {
//     pub fn mul_by_scalar_ascending_ladder_proj<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
//     ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
//         let params = self.circuit_params;
//         let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;

//         // TODO: use standard double-add algorithm for now, optimize later
//         let mut acc = ProjectivePoint::<E, G, T>::zero(params);
//         let mut tmp : AffinePoint<E, G, T> = self.clone();

//         for bit in scalar_decomposition.into_iter() {
//             let added = acc.add_mixed(cs, &mut tmp)?;
//             acc = ProjectivePoint::conditionally_select(cs, &bit, &added, &acc)?;
//             tmp = AffinePoint::double(&tmp, cs)?;
//         }
        
//         Ok(acc)
//     }


//     pub fn mul_by_scalar_ascending_skew_ladder_proj<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
//     ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
//         let params = self.circuit_params;
//         let mut scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
//         scalar_decomposition.push(Boolean::constant(true));

//         let point_negated = AffinePoint::negate(&self, cs)?;
//         let bit = scalar_decomposition[0];
//         let mut acc = ProjectivePoint::<E, G, T>::conditionally_select(
//             cs, &bit, &ProjectivePoint::zero(params), &ProjectivePoint::<E, G, T>::from(point_negated)
//         )?;
//         let mut tmp : AffinePoint<_, _, _> = self.clone();
        
//         for (_is_first, is_last, bit) in scalar_decomposition[1..].into_iter().identify_first_last() {
//             let mut to_add = tmp.conditionally_negate(cs, &bit.not())?;
//             acc = acc.add_mixed(cs, &mut to_add)?;
//             if !is_last {   
//                 tmp = AffinePoint::double(&tmp, cs)?;
//             }
//         }
        
//         Ok(acc)
//     }


//     pub fn mul_by_scalar_descending_skew_ladder_proj<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
//     ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
//         let params = self.circuit_params;
//         let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
//         let mut acc = ProjectivePoint::<E, G, T>::from(self.clone());
//         let mut y_negated = self.get_y().negate(cs)?;
//         y_negated.reduce(cs)?;
      
//         for (_, is_last, bit) in scalar_decomposition.into_iter().rev().identify_first_last() {
//             if !is_last {  
//                 acc = acc.double(cs)?;
//                 let selected_y = FieldElement::conditionally_select(cs, &bit, &self.y, &y_negated)?;
//                 let mut tmp = unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), selected_y, params) };
//                 acc = acc.add_mixed(cs, &mut tmp)?;
//             }
//             else {
//                 let mut tmp = unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), y_negated.clone(), params) };
//                 let skewed_acc = acc.add_mixed(cs, &mut tmp)?;
//                 acc = ProjectivePoint::conditionally_select(cs, &bit, &acc, &skewed_acc)?;
//             }
//         }
        
//         Ok(acc)
//     }


//     pub fn mul_by_scalar_descending_skew_ladder_with_endo_proj<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
//     ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
//         let params = self.circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;

//         let limit = params.get_endomorphism_bitlen_limit();
//         let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//             Some(x) => {
//                 let dcmp = params.calculate_decomposition(x);
//                 (Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus))
//             },
//             None => (None, None, None, None)
//         };
//         let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
//         let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
//         let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//         let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//         // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//         let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut chain = FieldElementsChain::new();
//         chain.add_pos_term(&k1).add_neg_term(&scalar);
//         let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//         FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//         let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
//         let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//         let x_endo = point.get_x().mul(cs, &beta)?;
//         let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//         let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//         let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//         let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
//         let point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
//         let mut acc = ProjectivePoint::<E, G, T>::from(point_plus_point_endo.clone());
//         let iter = k1_decomposition.into_iter().zip(k2_decomposition.into_iter()).rev().identify_first_last();

//         for (_, is_last, (k1_bit, k2_bit)) in iter {
//             if !is_last {
//                 // selection tree looks like following:
//                 //                              
//                 //                         |true --- P + Q
//                 //         |true---k2_bit--|
//                 //         |               |false --- P - Q
//                 // k1_bit--|
//                 //         |        
//                 //         |                |true --- -P + Q
//                 //         |false---k2_bit--|
//                 //                          |false --- -P - Q
//                 //
//                 // hence:
//                 // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
//                 // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
//                 // res.Y = conditionally_negate(!k1, tmp.Y)
//                 acc = acc.double(cs)?;
//                 let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
//                 let selected_x = FieldElement:: conditionally_select(
//                     cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
//                 )?;
//                 let tmp_y = FieldElement::conditionally_select(
//                     cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
//                 )?;
//                 let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
//                 let mut tmp = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) };
//                 acc = acc.add_mixed(cs, &mut tmp)?;
//             }
//             else {
//                 // we subtract either O, or P, or Q or P + Q
//                 // selection tree in this case looks like following:
//                 //                              
//                 //                         |true --- O
//                 //         |true---k2_bit--|
//                 //         |               |false --- Q
//                 // k1_bit--|
//                 //         |        
//                 //         |                |true --- P
//                 //         |false---k2_bit--|
//                 //                          |false --- P+Q
//                 //
//                 let tmp0 = ProjectivePoint::conditionally_select(
//                     cs, &k2_bit, &ProjectivePoint::zero(params), &ProjectivePoint::from(point_endo.clone())
//                 )?;
//                 let tmp1 = ProjectivePoint::from(AffinePoint::conditionally_select(
//                     cs, &k2_bit, &point, &point_plus_point_endo
//                 )?);
//                 let mut point_to_sub = ProjectivePoint::conditionally_select(cs, &k1_bit, &tmp0, &tmp1)?;
//                 acc = acc.sub(cs, &mut point_to_sub)?;
//             }
//         }
        
//         Ok(acc)
//     }


//     pub fn safe_multiexp_projective<CS: ConstraintSystem<E>>(
//         cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
//     ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
//         assert_eq!(scalars.len(), points.len());
//         let params = points[0].circuit_params;
//         let scalar_rns_params = &params.scalar_field_rns_params;
//         let base_rns_params = &params.base_field_rns_params;
//         let limit = params.get_endomorphism_bitlen_limit();
        
//         struct Multizip<T>(Vec<T>);
        
//         impl<T> Iterator for Multizip<T>
//         where T: Iterator,
//         {
//             type Item = Vec<T::Item>;

//             fn next(&mut self) -> Option<Self::Item> {
//                 self.0.iter_mut().map(Iterator::next).collect()
//             }
//         }

//         let mut points_unrolled = Vec::with_capacity(points.len() << 1);
//         let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
//         for (scalar, point) in scalars.iter().zip(points.iter()) { 
//             let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
//                 Some(x) => {
//                     let dcmp = params.calculate_decomposition(x);
//                     (
//                         Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
//                         Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
//                     )
//                 },
//                 None => (None, None, None, None)
//             };
//             let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k1_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
//                 cs, k2_abs_wit, limit, scalar_rns_params, true
//             )?;
//             let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
//             let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

//             // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
//             let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
//             let mut chain = FieldElementsChain::new();
//             chain.add_pos_term(&k1).add_neg_term(&scalar);
//             let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
//             FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

//             let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
//             let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
//             let x_endo = point.get_x().mul(cs, &beta)?;
//             let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
//             let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

//             let point_proj = ProjectivePoint::<E, G, T>::from(point_reg);
//             let point_endo_proj = ProjectivePoint::<E, G, T>::from(point_endo);
//             points_unrolled.push(point_proj);
//             points_unrolled.push(point_endo_proj);

//             let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
//             scalars_unrolled.push(k1_decomposition.into_iter().rev());
//             scalars_unrolled.push(k2_decomposition.into_iter().rev());
//         }

//         let selector_tree = SelectorTree::new(cs, &points_unrolled)?;
//         let mut acc = selector_tree.get_initial_accumulator();

//         for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
//             if !is_last {
//                 acc = acc.double(cs)?;
//                 let to_add = selector_tree.select(cs, &bits)?;
//                 acc = acc.add(cs, &to_add)?;
//             }
//             else {
//                 let to_add = selector_tree.select_last(cs, &bits)?;
//                 acc = acc.add(cs, &to_add)?;
//             }
//         }

//         Ok(acc)
//     }    
// }


// // if x = [x_0, x_1, ..., x_n] = /sum x_i 2^i - binary representation of x: x_i /in {0, 1}
// // then x = [y_-1, y_0, y_1, ..., y_n] - skewed naf representation: where y_i /in {0, 1}
// // x = -y_-1 + /sum_{i >= 1} (1 - 2* y_i) 2^i
// // algorithm for construction of skewed representation: 
// // for -1 <= y < n: y_i = ~x_{i+1} = 1 - x_{i+1} and y_n = 0 (always)
// // indeed:
// // y = -y_-1 + /sum (1 - 2* y_i) 2^i = x_0 - 1 + /sum (2* x_{i+1} - 1) 2^i +2^n = 
// // = x - 1 - \sum_{i=0}^{n-1} 2^i + 2^n = x - 1 - (2^n - 1) + 2^n = x




// // The purpose of selection table is the following: 
// // given n points P1, P2, .., Pn (in Affine or Projective coordinates),
// // we want to store and later select linear combinations of the form +/ P1 +/ P2 +/- ... +/ Pn
// // For example for 2 points P1, P2 naive selection tree looks like following:
// //                              
// //                         |true --- P + Q
// //         |true---k2_bit--|
// //         |               |false --- P - Q
// // k1_bit--|
// //         |        
// //         |                |true --- -P + Q
// //         |false---k2_bit--|
// //                          |false --- -P - Q
// //
// // which results in 6 total selections: 3 selects for coordinate X and 3 selects for coordinate Y
// // However, we may use te symmetry in negation formula for elliptic curve points: -P(x, y) = (x, -y) 
// // hence the more optimal routine will look like:
// // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
// // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
// // res.Y = conditionally_negate(!k1, tmp.Y)
// // which requires 3 total selects (as conditional negation costs the same as selection)
// // in general the implementation trick is to replace selections by individual flags k1, k2, ..., k_n
// // by selections by k1 ^ k2, k2 ^k3, ... , k_{n-1} ^ k_n.
// // ideed the selected coordinate x is the same for combinations of flags: [k1, ..., k_n] and [!k1, ..., !k_n]

// pub(crate) trait TreeSelectable<E: Engine>: Sized + Clone {
//     fn add<CS: ConstraintSystem<E>>(
//         cs: &mut CS, first: &mut Self, second: &mut Self
//     ) -> Result<Self, SynthesisError>;
    
//     fn sub<CS: ConstraintSystem<E>>(
//         cs: &mut CS, first: &mut Self, second: &mut Self
//     ) -> Result<Self, SynthesisError>;

//     fn safe_sub<CS: ConstraintSystem<E>>(
//         cs: &mut CS, first: &mut Self, second: &mut Self
//     ) -> Result<Self, SynthesisError> {
//         Self::sub(cs, first, second)
//     }
    
//     fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError>;
    
//     fn conditionally_select<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
//     ) -> Result<Self, SynthesisError>;
    
//     fn conditionally_negate<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &mut Self
//     ) -> Result<Self, SynthesisError>;

//     // given x, returns y, such that x = 2 * y
//     fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError>;
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for AffinePoint<'a, E, G, T>
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     fn add<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E> 
//     {
//         first.add_unequal_unchecked(cs, &second)
//     }

//     fn sub<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         first.sub_unequal_unchecked(cs, second)
//     }

//     fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError> {
//         AffinePoint::negate(first, cs)
//     }

//     fn conditionally_select<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
//     ) -> Result<Self, SynthesisError> {
//         AffinePoint::conditionally_select(cs, flag, first, second)
//     }
    
//     fn conditionally_negate<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &mut Self
//     ) -> Result<Self, SynthesisError> {
//         first.conditionally_negate(cs, flag)
//     }

//     fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError> {
//         let wit = elem.get_value().map(|x| {
//             // if x = 2 * y and order of group is n - odd prime, then:
//             // (n-1)/2 * x = (n-1) * y = -y
//             let mut scalar = <G::Scalar as PrimeField>::char();
//             scalar.div2();
//             let mut res = x.mul(scalar).into_affine();
//             res.negate();
//             res
//         });

//         let halved = AffinePoint::alloc(cs, wit, elem.circuit_params)?;
//         let mut initial = halved.double(cs)?;
//         AffinePoint::enforce_equal(cs, elem, &mut initial)?;
        
//         Ok(halved)
//     }
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for AffinePointExt<'a, E, G, T>
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     fn add<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E> 
//     {
//         first.add_unequal_unchecked(cs, &second)
//     }

//     fn sub<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         first.sub_unequal_unchecked(cs, second)
//     }

//     fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError> {
//         AffinePointExt::negate(first, cs)
//     }

//     fn conditionally_select<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
//     ) -> Result<Self, SynthesisError> {
//         AffinePointExt::conditionally_select(cs, flag, first, second)
//     }
    
//     fn conditionally_negate<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &mut Self
//     ) -> Result<Self, SynthesisError> {
//         first.conditionally_negate(cs, flag)
//     }

//     fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError> {
//         let rns_params = elem.get_x().c0.representation_params;
//         let (wit_x_c0, wit_x_c1, wit_y_c0, wit_y_c1)  = match elem.get_value() {
//             Some((x_c0, x_c1, y_c0, y_c1)) => {
//                 // if x = 2 * y and order of group is n - odd prime, then:
//                 // (n-1)/2 * x = (n-1) * y = -y
//                 let mut scalar = <G::Scalar as PrimeField>::char();
//                 scalar.div2();
                
//                 // it is a dirty hack but fine for now
//                 // at least we enforce that no new constraints will appear this way
//                 let gate_count_start = cs.get_current_step_number();

//                 let to_add = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, rns_params);
//                 let mut acc = to_add.clone();
//                 for bit in BitIterator::new(scalar).skip_while(|x| !x).skip(1) {
//                     acc = acc.double(cs)?;
//                     if bit {
//                         acc = acc.add_unequal_unchecked(cs, &to_add)?;
//                     }
//                 }
//                 let res = acc.negate(cs)?;

//                 let gate_count_end = cs.get_current_step_number();
//                 assert_eq!(gate_count_end - gate_count_start, 0);
                
//                 let (x_c0, x_c1, y_c0, y_c1) = res.get_value().expect("should be some");
//                 (Some(x_c0), Some(x_c1), Some(y_c0), Some(y_c1)) 
//             },
//             None => (None, None, None, None),
//         };

//         let halved = AffinePointExt::alloc(cs, wit_x_c0, wit_x_c1, wit_y_c0, wit_y_c1, rns_params)?;
//         let mut initial = halved.double(cs)?;
//         AffinePointExt::enforce_equal(cs, elem, &mut initial)?;
        
//         Ok(halved)
//     }
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for ProjectivePoint<'a, E, G, T>
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     fn add<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E> 
//     {
//         first.add(cs, &second)
//     }

//     fn sub<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
//     where CS: ConstraintSystem<E>
//     {
//         first.sub(cs, second)
//     }

//     fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError> {
//         ProjectivePoint::negate(first, cs)
//     }

//     fn conditionally_select<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
//     ) -> Result<Self, SynthesisError> {
//         ProjectivePoint::conditionally_select(cs, flag, first, second)
//     }
    
//     fn conditionally_negate<CS: ConstraintSystem<E>>(
//         cs: &mut CS, flag: &Boolean, first: &mut Self
//     ) -> Result<Self, SynthesisError> {
//         first.conditionally_negate(cs, flag)
//     }

//     fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, point: &mut Self) -> Result<Self, SynthesisError> {
//         let default = AffinePoint::constant(G::one(), point.circuit_params);
//         let (mut affine_point, is_point_at_infty) = point.convert_to_affine_or_default(cs, &default)?;
//         let wit = affine_point.get_value().map(|x| {
//             // if x = 2 * y and order of group is n - odd prime, then:
//             // (n-1)/2 * x = (n-1) * y = -y
//             let mut scalar = <G::Scalar as PrimeField>::char();
//             scalar.div2();
//             let mut res = x.mul(scalar).into_affine();
//             res.negate();
//             res
//         });

//         let halved = AffinePoint::alloc(cs, wit, point.circuit_params)?;
//         let mut initial = halved.double(cs)?;
//         AffinePoint::enforce_equal(cs, &mut affine_point, &mut initial)?;

//         ProjectivePoint::conditionally_select(
//             cs, &is_point_at_infty, &ProjectivePoint::zero(point.circuit_params), &ProjectivePoint::from(halved)
//         )
//     }
// }


// #[derive(Clone, Debug)]
// pub(crate) struct SelectorTree<E: Engine, T: TreeSelectable<E>> {
//     entries: Vec<T>, // raw elements P1, P2, ..., Pn
//     precompute: Vec<T>, // precomputed linear combinations +/ P1 +/ P2 +/- ... +/ Pn
//     initial_acc_idx: usize,
//     _marker: std::marker::PhantomData<E>
// }

// impl<E: Engine, T: TreeSelectable<E>> SelectorTree<E, T> {
//     pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS, entries: &[T]) -> Result<Self, SynthesisError> {
//         #[derive(Clone, Copy, PartialEq, Eq, Debug)]
//         enum Sign {
//             Plus,
//             Minus
//         }

//         // using Selector tree makes sense only if there are more than 1 element
//         let mut entries = entries.to_vec();
//         let mut workpad : Vec<(Sign, T)> = vec![(Sign::Plus, entries.get(0).expect("Entries must be nonempty").clone())];

//         for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
//             let mut new_working_pad = Vec::<(Sign, T)>::with_capacity(workpad.len() << 1);
//             for (sign, acc) in workpad.iter_mut() {
//                 match sign {
//                     Sign::Plus => {
//                         new_working_pad.push((Sign::Minus, T::sub(cs, acc, elem)?));
//                         new_working_pad.push((Sign::Plus, T::add(cs, acc, elem)?));   
//                     },
//                     Sign::Minus => {
//                         new_working_pad.push((Sign::Plus, T::add(cs, acc, elem)?));   
//                         new_working_pad.push((Sign::Minus, T::sub(cs, acc, elem)?));
//                     },
//                 };
//             }
//             workpad = new_working_pad
//         }
//         assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
//         let initial_acc_idx = workpad.len() - 1;
//         let precompute = workpad.drain(..).map(|(_sign, pt)| pt).collect();

//         Ok(SelectorTree::<E, T> {
//             entries, 
//             precompute,
//             initial_acc_idx,
//             _marker: std::marker::PhantomData::<E>
//         })
//     }

//     pub fn select<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError> {
//         assert_eq!(bits.len(), self.entries.len());
//         let mut selector_subtree = self.precompute.clone(); 
        
//         for (k0_bit, k1_bit) in bits.iter().rev().tuple_windows() {
//             let mut new_selector_subtree = Vec::<T>::with_capacity(selector_subtree.len() >> 1);
//             let xor_flag = Boolean::xor(cs, &k0_bit, &k1_bit)?;
//             for (first, second) in selector_subtree.into_iter().tuples() {
//                 let selected = T::conditionally_select(cs, &xor_flag, &first, &second)?;
//                 new_selector_subtree.push(selected);
//             }
//             selector_subtree = new_selector_subtree;
//         }

//         assert_eq!(selector_subtree.len(), 1);
//         let last_flag = bits[0];
//         let mut selected = selector_subtree.pop().unwrap();
//         T::conditionally_negate(cs, &last_flag.not(), &mut selected)
//     }

//     pub fn select_last<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError>
//     {
//         // TODO: also can be buggy: what if x = x'?
        
//         // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
//         // we want to retrieve the point which is dependent on bits as follows:
//         // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
//         // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
//         // if we denote the starting value of accumulator = /sum P_i as C
//         // then it is obvious that the following relation always holds: A - C = 2 * B
//         // hence we reduced the computation to one subtraction and one doubling
//         let mut a = self.select(cs, &bits)?;
//         let mut c = self.get_initial_accumulator();
//         // we use safe_sub here as it is possible here that a = +/- c 
//         let mut tmp = T::safe_sub(cs, &mut a, &mut c)?;
//         println!("before halving");
//         let res = T::halving(cs, &mut tmp)?;
//         println!("after halving");
//         Ok(res)
//     }

//     pub fn get_initial_accumulator(&self) -> T {
//         // initial accumulator value is equal to + P1 + P2 + ... + Pn
//         self.precompute[self.initial_acc_idx].clone()
//     }
// }


// #[derive(Clone, Debug)]
// pub(crate) struct SelectorTree2<'a, E: Engine, G: GenericCurveAffine, T> 
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     entries: Vec<AffinePoint<'a, E, G, T>>, // raw elements P1, P2, ..., Pn
//     precompute: Vec<AffinePoint<'a, E, G, T>>, // precomputed linear combinations +/ P1 +/ P2 +/- ... +/ Pn
//     initial_point_affine: AffinePoint<'a, E, G, T>,
//     initial_point_proj: ProjectivePoint<'a, E, G, T>,
//     iniitial_point_is_infty: Boolean,
//     adj_offset: AffinePointExt<'a, E, G, T>
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T> SelectorTree2<'a, E, G, T> 
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     fn get_initial(&self) -> (AffinePoint<'a, E, G, T>, Boolean, ProjectivePoint<'a, E, G, T>) {
//         (self.initial_point_affine.clone(), self.iniitial_point_is_infty, self.initial_point_proj.clone())
//     }
    
//     pub fn new<CS: ConstraintSystem<E>>(
//         cs: &mut CS, entries: &[AffinePoint<'a, E, G, T>]
//     ) -> Result<Self, SynthesisError> {
//         #[derive(Clone, Copy, PartialEq, Eq, Debug)]
//         pub enum Sign {
//             Plus,
//             Minus
//         }

//         let first_elem = entries.get(0).expect("Entries must be nonempty");
//         let params = first_elem.circuit_params;
//         let initial = ProjectivePoint::from(first_elem.clone());
        
//         // using Selector tree makes sense only if there are more than 1 element
//         let mut entries = entries.to_vec();
//         let mut workpad : Vec<(Sign, ProjectivePoint<'a, E, G, T>)> = vec![(Sign::Plus, initial)];

//         for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
//             let mut new_working_pad = Vec::with_capacity(workpad.len() << 1);
//             for (sign, acc) in workpad.iter_mut() {
//                 match sign {
//                     Sign::Plus => {
//                         new_working_pad.push((Sign::Minus, acc.sub_mixed(cs, elem)?));
//                         new_working_pad.push((Sign::Plus, acc.add_mixed(cs, elem)?));   
//                     },
//                     Sign::Minus => {
//                         new_working_pad.push((Sign::Plus, acc.add_mixed(cs, elem)?));   
//                         new_working_pad.push((Sign::Minus, acc.sub_mixed(cs, elem)?));
//                     },
//                 };
//             }
//             workpad = new_working_pad
//         }
//         assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
//         let point_uninitialized = AffinePoint::uninitialized(params);
//         let mut precompute = Vec::with_capacity(workpad.len());
//         let mut initial_point_affine = point_uninitialized.clone();
//         let mut iniitial_point_is_infty = Boolean::constant(false);
//         let mut initial_point_proj = ProjectivePoint::zero(params);

//         let mut adj_offset = AffinePointExt::constant(
//             params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
//             params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
//             &params.base_field_rns_params
//         );
        
//         for (_is_first, is_last, elem) in workpad.into_iter().identify_first_last() {
//             let (_sign, mut point_proj) = elem;
//             let (point_affine, is_infty) = point_proj.convert_to_affine_or_default(cs, &point_uninitialized)?;
            
//             if is_last {
//                 initial_point_affine = point_affine.clone();
//                 iniitial_point_is_infty = is_infty;
//                 initial_point_proj = point_proj;
//             }
//             precompute.push(point_affine);
//         }
//         Ok(SelectorTree2 {
//             entries, 
//             precompute,
//             initial_point_affine,
//             iniitial_point_is_infty,
//             initial_point_proj,
//             adj_offset
//         })
//     }

//     fn select<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, bits: &[Boolean]
//     ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
//         assert_eq!(bits.len(), self.entries.len());
//         let mut selector_subtree = self.precompute.clone(); 
        
//         for (k0_bit, k1_bit) in bits.iter().rev().tuple_windows() {
//             let mut new_selector_subtree = Vec::with_capacity(selector_subtree.len() >> 1);
//             let xor_flag = Boolean::xor(cs, &k0_bit, &k1_bit)?;
//             for (first, second) in selector_subtree.into_iter().tuples() {
//                 let selected = AffinePoint::conditionally_select(cs, &xor_flag, &first, &second)?;
//                 new_selector_subtree.push(selected);
//             }
//             selector_subtree = new_selector_subtree;
//         }

//         assert_eq!(selector_subtree.len(), 1);
//         let last_flag = bits[0];
//         let selected = selector_subtree.pop().unwrap();
        
//         let is_point_at_infty = FieldElement::is_zero(&mut selected.get_y(), cs)?;
//         let candidate = AffinePoint::conditionally_negate(&selected, cs, &last_flag.not())?;

//         Ok((candidate, is_point_at_infty))
//     }
   
//     pub fn double_and_add_selected<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>, bits: &[Boolean]
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError> 
//     {
//         let (candidate, is_point_at_infty) = self.select(cs, bits)?;
//         let params = candidate.circuit_params;
//         // It is sometimes buggy(
//         let x_c0 = candidate.get_x();
//         let x_c1 = FieldElement::zero(&params.base_field_rns_params);
//         let y_c0 = candidate.get_y();
//         let y_c1 = FieldElement::conditionally_select(
//             cs, &is_point_at_infty, &self.adj_offset.get_y().c1, &FieldElement::zero(&params.base_field_rns_params)
//         )?;
//         let x_ext = Fp2::from_coordinates(x_c0, x_c1);
//         let y_ext = Fp2::from_coordinates(y_c0, y_c1);
//         let to_add = AffinePointExt { x: x_ext, y: y_ext };
        
//         // let to_add = AffinePointExt::conditionally_select(
//         //     cs, &is_point_at_infty, &self.adj_offset, &AffinePointExt::from(candidate)
//         // )?;
//         acc.double_and_add_unchecked(cs, &to_add)
//         //AffinePointExt::conditionally_select(cs, &is_point_at_infty, &acc, &acc_modified)
//     }

//     pub fn add_initial_into_accumulator<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError> 
//     {
//         // initial accumulator value is equal to + P1 + P2 + ... + Pn
//         let (point, is_point_at_infty, _point_proj) = self.get_initial();
//         let acc_modified = acc.add_unequal_unchecked(cs, &AffinePointExt::from(point))?;
//         AffinePointExt::conditionally_select(cs, &is_point_at_infty, &acc, &acc_modified)
//     }

//     pub fn add_last_into_accumulator<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>, bits: &[Boolean]
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError>
//     { 
//         // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
//         // we want to retrieve the point which is dependent on bits as follows:
//         // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
//         // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
//         // if we denote the starting value of accumulator = /sum P_i as C
//         // then it is obvious that the following relation always holds: A - C = 2 * B
//         // hence we reduced the computation to one subtraction and one doubling
        
//         let (selected, is_selected_point_at_infty) = self.select(cs, &bits)?;
//         let params = selected.circuit_params;
//         let rns_params = &params.base_field_rns_params;

//         let proj_x = selected.get_x();
//         let proj_y = FieldElement::conditionally_select(
//             cs, &is_selected_point_at_infty, &FieldElement::one(rns_params), &selected.get_y()
//         )?;
//         let proj_z = FieldElement::conditionally_select(
//             cs, &is_selected_point_at_infty, &FieldElement::zero(rns_params), &FieldElement::one(rns_params)
//         )?;
//         let a = ProjectivePoint::from_coordinates_unchecked(
//             proj_x, proj_y, proj_z, selected.is_in_subgroup, params
//         );
        
//         let (_, _, c) = self.get_initial();
//         let mut a_minus_c = a.sub(cs, &c)?;
//         let mut res_proj = ProjectivePoint::halving(cs, &mut a_minus_c)?;

//         let (res_affine, is_infty) = res_proj.convert_to_affine_or_default(
//             cs, &AffinePoint::uninitialized(params)
//         )?;
//         let acc_modified = acc.add_unequal_unchecked(cs, &AffinePointExt::from(res_affine))?;
//         AffinePointExt::conditionally_select(cs, &is_infty, &acc, &acc_modified)
//     }

//     pub fn add_last_into_accumulator_unoptimized<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>, bits: &[Boolean]
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError>
//     {
//         let mut acc = acc.clone();
//         for (bit, point) in bits.iter().zip(self.entries.iter()) {
//             let is_point_at_infty = FieldElement::is_zero(&mut point.get_y(), cs)?;
//             let acc_modified = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(point.clone()))?;
//             let cond_flag = Boolean::or(cs, &is_point_at_infty, &bit)?;
//             acc = AffinePointExt::conditionally_select(cs, &cond_flag, &acc, &acc_modified)?;
//         }
//         Ok(acc) 
//     }
// }


// #[derive(Clone, Debug)]
// pub(crate) struct SelectorTree3<'a, E: Engine, G: GenericCurveAffine, T> 
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     entries: Vec<AffinePoint<'a, E, G, T>>, // raw elements P1, P2, ..., Pn
//     precompute: Vec<AffinePoint<'a, E, G, T>>, // precomputed linear combinations +/ P1 +/ P2 +/- ... +/ Pn
//     initial_point_base: AffinePoint<'a, E, G, T>,
//     initial_point_ext: AffinePointExt<'a, E, G, T>,
//     iniitial_point_is_infty: Boolean,
//     adj_offset: AffinePointExt<'a, E, G, T>
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T> SelectorTree3<'a, E, G, T> 
// where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
// {
//     fn get_initial(&self) -> (AffinePoint<'a, E, G, T>, Boolean, AffinePointExt<'a, E, G, T>) {
//         (self.initial_point_base.clone(), self.iniitial_point_is_infty, self.initial_point_ext.clone())
//     }
    
//     pub fn new<CS: ConstraintSystem<E>>(
//         cs: &mut CS, entries: &[AffinePoint<'a, E, G, T>]
//     ) -> Result<Self, SynthesisError> {
//         #[derive(Clone, Copy, PartialEq, Eq, Debug)]
//         enum Sign {
//             Plus,
//             Minus
//         }

//         let first_elem = entries.get(0).expect("Entries must be nonempty");
//         let params = first_elem.circuit_params;
//         let rns_params = &params.base_field_rns_params;
        
//         let mut adj_offset = AffinePointExt::constant(
//             params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
//             params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
//             &params.base_field_rns_params
//         );

//         let initial = adj_offset.add_unequal_unchecked(cs, &AffinePointExt::from(first_elem.clone()))?;
//         // using Selector tree makes sense only if there are more than 1 element
//         let mut entries = entries.to_vec();
//         let mut workpad : Vec<(Sign, AffinePointExt<'a, E, G, T>)> = vec![(Sign::Plus, initial)];

//         for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
//             let elem = AffinePointExt::from(elem.clone());
//             let mut new_working_pad = Vec::with_capacity(workpad.len() << 1);
//             for (sign, acc) in workpad.iter_mut() {
//                 match sign {
//                     Sign::Plus => {
//                         new_working_pad.push((Sign::Minus, acc.sub_unequal_unchecked(cs, &elem)?));
//                         new_working_pad.push((Sign::Plus, acc.add_unequal_unchecked(cs, &elem)?));   
//                     },
//                     Sign::Minus => {
//                         new_working_pad.push((Sign::Plus, acc.add_unequal_unchecked(cs, &elem)?));   
//                         new_working_pad.push((Sign::Minus, acc.sub_unequal_unchecked(cs, &elem)?));
//                     },
//                 };
//             }
//             workpad = new_working_pad
//         }
//         assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
//         let point_uninitialized = AffinePoint::uninitialized(params);
//         let mut precompute = Vec::with_capacity(workpad.len());
//         let mut initial_point_base = point_uninitialized.clone();
//         let mut iniitial_point_is_infty = Boolean::constant(false);
//         let mut initial_point_ext = AffinePointExt::uninitialized(rns_params);
        
//         for (_is_first, is_last, elem) in workpad.into_iter().identify_first_last() {
//             let (_sign, mut point_ext) = elem;
//             // point_ext is of the form: R + base_field
//             // hence it is zero if it is equal to R, 
//             // hence it is enough to compare x cooridnate
//             // as it is impossible that R + base_field;
//             let is_infty = Fp2::equals(cs, &mut point_ext.x, &mut adj_offset.x)?;

//             let mut point_ext_copy = point_ext.clone(); 
//             point_ext_copy.x.c0 = FieldElement::conditionally_select(
//                 cs, &is_infty, &FieldElement::one(rns_params), &point_ext.x.c0
//             )?;
//             let res_ext = point_ext_copy.sub_unequal_unchecked(cs, &adj_offset)?;

//             let final_x = res_ext.get_x().c0.clone();
//             let final_y = FieldElement::conditionally_select(
//                 cs, &is_infty, &FieldElement::zero(rns_params), &res_ext.get_y().c0
//             )?;
            
//             // println!("final_x_c1: {}", res_ext.get_x().c1.get_field_value().unwrap());
//             // println!("final_y_c1: {}", res_ext.get_y().c1.get_field_value().unwrap());

//             let final_value = match (final_x.get_field_value(), final_y.get_field_value(), is_infty.get_value()) 
//             {
//                 (_, _, Some(true)) => Some(G::zero()),
//                 (Some(x), Some(y), Some(false)) => Some(G::from_xy_checked(x, y).expect("should be on the curve")),
//                 _ => None,
//             }; 

//             let point_base = AffinePoint {
//                 x : final_x,
//                 y : final_y,
//                 value: final_value,
//                 is_in_subgroup: true,
//                 circuit_params: params
//             };
            
//             if is_last {
//                 initial_point_base = point_base.clone();
//                 initial_point_ext = point_ext;
//                 iniitial_point_is_infty = is_infty
//             }
//             precompute.push(point_base);
//         }
//         Ok(SelectorTree3 {
//             entries, 
//             precompute,
//             initial_point_base,
//             initial_point_ext,
//             iniitial_point_is_infty,
//             adj_offset
//         })
//     }

//     fn select<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, bits: &[Boolean]
//     ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
//         assert_eq!(bits.len(), self.entries.len());
//         let mut selector_subtree = self.precompute.clone(); 
        
//         for (k0_bit, k1_bit) in bits.iter().rev().tuple_windows() {
//             let mut new_selector_subtree = Vec::with_capacity(selector_subtree.len() >> 1);
//             let xor_flag = Boolean::xor(cs, &k0_bit, &k1_bit)?;
//             for (first, second) in selector_subtree.into_iter().tuples() {
//                 let selected = AffinePoint::conditionally_select(cs, &xor_flag, &first, &second)?;
//                 new_selector_subtree.push(selected);
//             }
//             selector_subtree = new_selector_subtree;
//         }

//         assert_eq!(selector_subtree.len(), 1);
//         let last_flag = bits[0];
//         let selected = selector_subtree.pop().unwrap();
        
//         let is_point_at_infty = FieldElement::is_zero(&mut selected.get_y(), cs)?;
//         let candidate = AffinePoint::conditionally_negate(&selected, cs, &last_flag.not())?;

//         Ok((candidate, is_point_at_infty))
//     }
   
//     pub fn double_and_add_selected<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>, bits: &[Boolean]
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError> 
//     {
//         let (candidate, is_point_at_infty) = self.select(cs, bits)?;
//         let acc_modified = acc.double_and_add_unchecked(cs, &AffinePointExt::from(candidate))?;
//         AffinePointExt::conditionally_select(cs, &is_point_at_infty, &acc, &acc_modified)
//     }

//     pub fn add_initial_into_accumulator<CS: ConstraintSystem<E>>(
//         &self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError> 
//     {
//         // initial accumulator value is equal to + P1 + P2 + ... + Pn
//         let (point, is_point_at_infty, _point_proj) = self.get_initial();
//         let acc_modified = acc.add_unequal_unchecked(cs, &AffinePointExt::from(point))?;
//         AffinePointExt::conditionally_select(cs, &is_point_at_infty, &acc, &acc_modified)
//     }

//     pub fn add_last_into_accumulator<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, acc: &AffinePointExt<'a, E, G, T>, bits: &[Boolean]
//     ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError>
//     { 
//         // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
//         // we want to retrieve the point which is dependent on bits as follows:
//         // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
//         // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
//         // if we denote the starting value of accumulator = /sum P_i as C
//         // then it is obvious that the following relation always holds: A - C = 2 * B
//         // hence we reduced the computation to one subtraction and one doubling
        
//         let (selected, is_selected_point_at_infty) = self.select(cs, &bits)?;
//         let params = selected.circuit_params;
//         let rns_params = &params.base_field_rns_params;

//         let (_, _, c) = self.get_initial();
//         let c_minus_a = c.sub_unequal_unchecked(cs, &AffinePointExt::from(selected))?;
//         let mut to_sub_ext = AffinePointExt::conditionally_select(
//             cs, &is_selected_point_at_infty, &c, &c_minus_a
//         )?;
//         // println!("before halving");
//         // to_sub_ext = AffinePointExt::halving(cs, &mut to_sub_ext)?;
//         // println!("after halving");

//         let is_infty = Fp2::equals(cs, &mut to_sub_ext.x, &mut self.adj_offset.x)?;
//         println!("is ifty: {}", is_infty.get_value().unwrap());
//         to_sub_ext.x.c0 = FieldElement::conditionally_select(
//             cs, &is_infty, &FieldElement::one(rns_params), &to_sub_ext.x.c0
//         )?;
//         let res_ext = to_sub_ext.sub_unequal_unchecked(cs, &self.adj_offset)?;

//         // println!("final_x_c1 end: {}", res_ext.get_x().c1.get_field_value().unwrap());
//         // println!("final_y_c1 end : {}", res_ext.get_y().c1.get_field_value().unwrap());

//         let final_x = res_ext.get_x().c0.clone();
//         let final_y = res_ext.get_y().c0.clone();
//         let final_value = match (final_x.get_field_value(), final_y.get_field_value(), is_infty.get_value()) 
//         {
//             (_, _, Some(true)) => Some(G::zero()),
//             (Some(x), Some(y), Some(false)) => Some(G::from_xy_checked(x, y).expect("should be on the curve")),
//             _ => None,
//         }; 

//         let point_base = AffinePoint {
//             x : final_x,
//             y : final_y,
//             value: final_value,
//             is_in_subgroup: true,
//             circuit_params: params
//         };

//         let acc_modified = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(point_base))?;
//         AffinePointExt::conditionally_select(cs, &is_infty, &acc, &acc_modified)
//     }
// }


// const RATE: usize = 2;
// const WIDTH: usize = 3;

// fn round_function_absorb<E: Engine, CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
//     cs: &mut CS, state: &mut [Num<E>; WIDTH], input: &[Num<E>], hash_params: &P
// ) -> Result<(), SynthesisError> 
// {
//     assert_eq!(input.len(), RATE);
    
//     let mut state_lcs = vec![];
//     for (s, inp) in state.iter().zip(input.iter())  {
//         let mut lc = LinearCombination::from(*s);
//         lc.add_assign_number_with_coeff(&inp, E::Fr::one());
//         state_lcs.push(lc);
//     }

//     for s in state[input.len()..].iter() {
//         let lc = LinearCombination::from(*s);
//         state_lcs.push(lc);
//     }

//     let mut state_lcs = state_lcs.try_into().expect("state width should match");
    
//     use crate::plonk::circuit::curve_new::ram_via_hashes::circuit::sponge::circuit_generic_round_function;
//     circuit_generic_round_function(cs, &mut state_lcs, hash_params)?;

//     for (a, b) in state.iter_mut().zip(state_lcs.iter()) {
//         *a = b.clone().into_num(cs)?;
//     }

//     Ok(())
// }

// fn round_function_squeeze<E: Engine>(state: &[Num<E>; WIDTH]) -> (Num<E>, Num<E>) {
//     (state[0].clone(), state[1].clone())
// }


// #[derive(Clone, PartialEq, Eq, Debug)]
// pub enum MemoryEnforcementStrategy {
//     Waksman,
//     HashSets,
// }
   
// pub(crate) struct Memory<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
// where <G as GenericCurveAffine>::Base: PrimeField
// {
//     queries: Vec<(Num<E>, AffinePoint<'a, E, G, T>)>,
//     witness_map: HashMap<u64, Option<G>>,
//     address_width: usize,
//     validity_is_enforced: bool,
//     permutation_enforcement_strategy: MemoryEnforcementStrategy,

//     permutation: IntegerPermutation,
//     unsorted_packed_elems_0: Vec<Num<E>>,
//     unsorted_packed_elems_1: Vec<Num<E>>,
//     sorted_packed_elems_0: Vec<Num<E>>,
//     sorted_packed_elems_1: Vec<Num<E>>,
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Drop for Memory<'a, E, G, T> 
// where <G as GenericCurveAffine>::Base: PrimeField
// {
//     fn drop(&mut self) {
//         assert!(self.validity_is_enforced);
//     }
// }

// impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Memory<'a, E, G, T>
// where <G as GenericCurveAffine>::Base: PrimeField
// {
//     pub fn new(address_width: usize, permutation_enforcement_strategy: MemoryEnforcementStrategy) -> Self {
//         Self {
//             queries: vec![],
//             witness_map: HashMap::new(),
//             address_width,
//             validity_is_enforced: false,
//             permutation_enforcement_strategy,

//             permutation: IntegerPermutation::new(1),
//             unsorted_packed_elems_0: vec![],
//             unsorted_packed_elems_1: vec![],
//             sorted_packed_elems_0: vec![],
//             sorted_packed_elems_1: vec![],
//         }
//     }

//     pub fn write(&mut self, addr: u64, point: AffinePoint<'a, E, G, T>) {
//         assert!(log2_floor(addr as usize) as usize <= self.address_width);
//         self.witness_map.insert(addr, point.get_value());
//         let addr_as_num = Num::Constant(u64_to_ff(addr));
//         self.queries.push((addr_as_num, point));
//         self.validity_is_enforced = false; 
//     }

//     pub fn read<CS: ConstraintSystem<E>>(
//         &mut self, cs: &mut CS, addr: Num<E>, params: &'a CurveCircuitParameters<E, G, T>
//     ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
//         let wit = addr.get_value().and_then(|x| { self.witness_map.get(&ff_to_u64(&x)).cloned().unwrap_or(None) });
//         let res = AffinePoint::alloc(cs, wit, params)?;
//         self.queries.push((addr, res.clone()));
//         self.validity_is_enforced = false;

//         Ok(res)
//     }

//     fn calculate_permutation(&self) -> IntegerPermutation {
//         let mut keys = Vec::with_capacity(self.queries.len());
//         for (idx, (addr, _)) in self.queries.iter().enumerate() {
//             if let Some(addr) = addr.get_value() {
//                 let composite_key = ff_to_u64(&addr);
//                 keys.push((idx, composite_key));
//             } else {
//                 return IntegerPermutation::new(self.queries.len());
//             }
//         }

//         keys.sort_by(|a, b| a.1.cmp(&b.1));
//         let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();
//         IntegerPermutation::new_from_permutation(integer_permutation)
//     }

//     fn enforce_correctness_of_sorted_packed_queries<CS>(&mut self, cs: &mut CS)-> Result<(), SynthesisError>
//     where CS: ConstraintSystem<E>
//     {
//         let limit = Num::Constant(u64_to_ff((1u64 << self.address_width) - 1));
//         let mut counter = Num::zero();
//         let iter = self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter()).identify_first_last();
//         let mut el_0_prev = Num::zero();
//         let mut el_1_prev = Num::zero();
    
//         for (is_first, _is_last, (el_0_cur, el_1_cur)) in iter {
//             if !is_first {
//                 let is_equal_0 = Num::equals(cs, &el_0_prev, &el_0_cur)?;
//                 let is_equal_1 = Num::equals(cs, &el_1_prev, &el_1_cur)?;
//                 let both_are_equal = Boolean::and(cs, &is_equal_0, &is_equal_1)?;
//                 counter = counter.conditionally_increment(cs, &both_are_equal.not())?;
//             }
           
//             el_0_prev = *el_0_cur;
//             el_1_prev = *el_1_cur;
//         }
//         counter.enforce_equal(cs, &limit)
//     }

//     pub fn enforce_ram_correctness<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> 
//     {
//         self.validity_is_enforced = true;
//         let size = self.queries.len();

//         let permutation = self.calculate_permutation();
        
//         let mut unsorted_packed_elems_0 = Vec::with_capacity(size);
//         let mut unsorted_packed_elems_1 = Vec::with_capacity(size);
//         let mut sorted_packed_elems_0 = Vec::with_capacity(size);
//         let mut sorted_packed_elems_1 = Vec::with_capacity(size);

//         for (addr, point) in self.queries.iter_mut() {
//             let packed = point.pack(cs, addr, self.address_width)?;
//             unsorted_packed_elems_0.push(packed[0]);
//             unsorted_packed_elems_1.push(packed[1]);
//         }
//         for index in permutation.elements.iter() {
//             let value_0 = unsorted_packed_elems_0[*index].clone();
//             sorted_packed_elems_0.push(value_0);
//             let value_1 = unsorted_packed_elems_1[*index].clone();
//             sorted_packed_elems_1.push(value_1);
//         }

//         self.permutation = permutation;
//         self.unsorted_packed_elems_0 = unsorted_packed_elems_0;
//         self.unsorted_packed_elems_1 = unsorted_packed_elems_1;
//         self.sorted_packed_elems_0 = sorted_packed_elems_0;
//         self.sorted_packed_elems_1 = sorted_packed_elems_1;

//         self.enforce_correctness_of_permutation(cs)?;
//         self.enforce_correctness_of_sorted_packed_queries(cs)
//     }

    

//     fn enforce_correctness_of_permutation<CS>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>
//     where CS: ConstraintSystem<E>
//     {
//         match self.permutation_enforcement_strategy {
//             MemoryEnforcementStrategy::Waksman => {
//                 let switches = order_into_switches_set(cs, &self.permutation)?;
//                 prove_permutation_of_nums_using_switches_witness(
//                     cs, &self.unsorted_packed_elems_0, &self.sorted_packed_elems_0, &switches
//                 )?;
//                 prove_permutation_of_nums_using_switches_witness(
//                     cs, &self.unsorted_packed_elems_1, &self.sorted_packed_elems_1, &switches
//                 )
//             },
//             MemoryEnforcementStrategy::HashSets => {
//                 let hash_params = RescuePrimeParams::<E, RATE, WIDTH>::new_with_width4_custom_gate();
//                 let mut state = [Num::<E>::zero(); WIDTH];

//                 let iter = self.unsorted_packed_elems_0.iter().zip(self.unsorted_packed_elems_1.iter()).chain(
//                     self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter())
//                 );
//                 for (x, y) in iter {
//                     let input = [x.clone(), y.clone()];
//                     round_function_absorb(cs, &mut state, &input, &hash_params)?;
//                 };
//                 let (challenge_a, challenge_b) = round_function_squeeze(&state);

//                 // (Polynomials are of the form X + c0 * Y + c1)
//                 // we substitute X and Y with challenge a and b correspondingly
//                 let mut lhs = Num::Constant(E::Fr::one());
//                 let mut rhs = Num::Constant(E::Fr::one());
                
//                 let outer_iter = std::iter::once(
//                     (&self.unsorted_packed_elems_0, &self.unsorted_packed_elems_1, &mut lhs)
//                 ).chain(std::iter::once(
//                     (&self.sorted_packed_elems_0, &self.sorted_packed_elems_1, &mut rhs)
//                 ));
//                 for (column_0, column_1, out) in outer_iter {
//                     let inner_iter = column_0.iter().zip(column_1.iter());
//                     for (c0, c1) in inner_iter {
//                         let mut lc = LinearCombination::zero(); 
//                         lc.add_assign_number_with_coeff(&challenge_a.clone(), E::Fr::one());
//                         lc.add_assign_number_with_coeff(&c1, E::Fr::one());
//                         let c0_mul_challenge = c0.mul(cs, &challenge_b)?;
//                         lc.add_assign_number_with_coeff(&c0_mul_challenge, E::Fr::one());
//                         let multiplier = lc.into_num(cs)?;
//                         *out = Num::mul(out, cs, &multiplier)?;
//                     }
//                 } 
//                 lhs.enforce_equal(cs, &rhs)
//             }
//         }    
//     }
// }


// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1, G1Affine};
//     use crate::bellman::pairing::bls12_381::Bls12;
//     use plonk::circuit::Width4WithCustomGates;
//     use bellman::plonk::better_better_cs::gates::{selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self};
//     use rand::{XorShiftRng, SeedableRng, Rng};
//     use bellman::plonk::better_better_cs::cs::*;
//     use plonk::circuit::boolean::AllocatedBit;
//     use itertools::Itertools;

//     struct TestSelectorTreeCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
//     where <G as GenericCurveAffine>::Base: PrimeField
//     {
//         circuit_params: CurveCircuitParameters<E, G, T>,
//         num_of_points: usize
//     }
    
//     impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestSelectorTreeCircuit<E, G, T> 
//     where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
//     {
//         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
//             )
//         }
    
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let mut rng = rand::thread_rng();
//             let mut points = Vec::with_capacity(self.num_of_points);
//             let mut scalars = Vec::with_capacity(self.num_of_points);

//             for _ in 0..self.num_of_points {
//                 let scalar_wit : G::Scalar = rng.gen();
//                 let point_wit : G = rng.gen();
    
//                 let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
//                 let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;
    
//                 points.push(point);
//                 scalars.push(scalar);
//             }

//             let selector_tree = SelectorTree::new(cs, &points)?;
//             let in_circuit_false = Boolean::Is(AllocatedBit::alloc(cs, Some(false))?);
//             let in_circuit_true = Boolean::Is(AllocatedBit::alloc(cs, Some(true))?);
//             let iter = (0..self.num_of_points).map(
//                 |_| std::iter::once(in_circuit_false).chain(std::iter::once(in_circuit_true))
//             ).multi_cartesian_product();

//             for (is_first, _is_last, bits) in iter.identify_first_last() {
//                 let mut acc = points[0].conditionally_negate(cs, &bits[0].not())?;
//                 for (point, bit) in points.iter().zip(bits.iter()).skip(1) {
//                     let mut to_add = point.conditionally_negate(cs, &bit.not())?;
//                     acc = acc.add_unequal(cs, &mut to_add)?;
//                 }
//                 let mut chosen_from_selector_tree = selector_tree.select(cs, &bits[..])?;
//                 AffinePoint::enforce_equal(cs, &mut acc, &mut chosen_from_selector_tree)?;

//                 if bits.iter().all(|x| x.get_value().unwrap()) {
//                     let mut sum_all = selector_tree.get_initial_accumulator();
//                     AffinePoint::enforce_equal(cs, &mut acc, &mut sum_all)?;
//                 }

//                 // check what should be done on the last iterator
//                 let mut is_infty = true;
//                 let mut acc = AffinePoint::constant(G::one(), &self.circuit_params);
//                 for (point, bit) in points.iter().zip(bits.iter()) {
//                     if !bit.get_value().unwrap() {
//                         if is_infty {
//                             is_infty = false;
//                             acc = point.negate(cs)?;
//                         }
//                         else {
//                             let mut tmp = point.clone();    
//                             acc = acc.sub_unequal(cs, &mut tmp)?;
//                         }
//                     }
//                 }
//                 if !is_infty && !is_first {
//                     let mut last_selection = selector_tree.select_last(cs, &bits[..])?; 
//                     AffinePoint::enforce_equal(cs, &mut acc, &mut last_selection)?;
//                 }
//             }
           
//             Ok(())
//         }
//     }

//     #[test]
//     fn test_tree_selector_for_bn256() {
//         const LIMB_SIZE: usize = 80;
//         const NUM_OF_POINTS: usize = 3;

//         let mut cs = TrivialAssembly::<
//             Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
//         >::new();
//         inscribe_default_bitop_range_table(&mut cs).unwrap();
//         let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

//         let circuit = TestSelectorTreeCircuit { circuit_params, num_of_points: NUM_OF_POINTS };
//         circuit.synthesize(&mut cs).expect("must work");
//         cs.finalize();
//         assert!(cs.is_satisfied()); 
//     }    
// }
 

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
use rand::Rng;


// here all methods are related to scalar multiplication and multiexponentiation
// we are particularly interested in three curves: secp256k1, bn256 and bls12-281
// unfortunately, only bls12-381 has a cofactor, hence in order to preserve exception-freness
// we have to play around projective coordinates and field extensions
pub struct EndoAuxData<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub point: AffinePoint<'a, E, G, T>,
    pub point_endo: AffinePoint<'a, E, G, T>,
    pub point_scalar_decomposition: Vec<Boolean>,
    pub point_endo_scalar_decomposition: Vec<Boolean>,
}

impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    fn compute_endo_aux_data<CS: ConstraintSystem<E>>(
        cs: &mut CS, point: &Self, scalar: &FieldElement<'a, E, G::Scalar>
    ) -> Result<EndoAuxData<'a, E, G, T>, SynthesisError> {
        const HEIGHT: usize = 1;
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
            cs, k1_abs_wit, limit, scalar_rns_params, HEIGHT
        )?;
        let (k2_abs, k2_chunks) = FieldElement::alloc_for_known_bitwidth_with_custom_range_check_granularity(
            cs, k2_abs_wit, limit, scalar_rns_params, HEIGHT
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

        let point_scalar_decomposition = k1_chunks.get_bits().iter().map(|x| Boolean::Is(*x)).collect();
        let point_endo_scalar_decomposition = k2_chunks.get_bits().iter().map(|x| Boolean::Is(*x)).collect();

        let endo_aux_data = EndoAuxData::<E, G, T> {
            point: point_modified,
            point_endo,
            point_scalar_decomposition,
            point_endo_scalar_decomposition
        };
        Ok(endo_aux_data) 
    }

    fn get_offset_generator(
        exception_free_version: bool, params: &'a CurveCircuitParameters<E, G, T>
    ) -> PointWrapper<'a, E, G, T> {
        let use_ext_point = exception_free_version && params.is_prime_order_curve;
        if use_ext_point {
            let offset_generator = AffinePointExt::constant(
                params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
                params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
                &params
            );
            PointWrapper::AffineOverExtField(offset_generator)
        } else {
            let point = if params.is_prime_order_curve {
                let mut rng = rand::thread_rng();
                PointWrapper::AffineOverBaseField(AffinePoint::constant(rng.gen(), params))
            } else { 
                let point = G::from_xy_checked(
                    params.fp2_offset_generator_x_c0, params.fp2_offset_generator_y_c0).expect(
                    "should be a valid point"
                );
                let offset_generator = AffinePoint::constant(point, params);
                PointWrapper::AffineOverBaseFieldInCofactor(offset_generator)
            };

            point
        }
    }

    fn get_adj_generator(params: &'a CurveCircuitParameters<E, G, T>) -> PointWrapper<'a, E, G, T> {
        if params.is_prime_order_curve {
            let offset_generator = AffinePointExt::constant(
                params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1,
                params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c0,
                &params
            );
            PointWrapper::AffineOverExtField(offset_generator)
        } else {
            let x = G::from_xy_checked(params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_y_c0).expect("valid point");
            let offset_generator = AffinePoint::constant(x, params);
            PointWrapper::AffineOverBaseFieldInCofactor(offset_generator)
        }
    }

    fn final_normalization<CS: ConstraintSystem<E>>(
        cs: &mut CS, mut wrapped_point: PointWrapper<'a, E, G, T>, mut scaled_offset: PointWrapper<'a, E, G, T>, 
        num_of_doubles: usize, adj_offset_is_used: bool, exception_free_version: bool 
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        let params = wrapped_point.get_params();
        let gate_count_start = cs.get_current_step_number();
        for _ in 0..num_of_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        let gate_count_end = cs.get_current_step_number();
        assert_eq!(gate_count_end - gate_count_start, 0);
        assert!(params.is_prime_order_curve);

        let (acc, infty_flag_0) = if exception_free_version {
            wrapped_point.prudent_sub(cs, &mut scaled_offset)?
        } else {
            let res = wrapped_point.checked_sub(cs, &mut scaled_offset)?;
            (res, Boolean::constant(false))
        };

        let (acc, infty_flag) = if adj_offset_is_used {
            // TODO: this should be rewritten and for now it only works for prime order curves
            // it should be modified to work aver BLS as well
            let is_defined_over_base_field = |point: &AffinePointExt<'a, E, G, T>| -> Option<bool> {
                point.get_value().map(|(_x_c0, x_c1, _y_c0, y_c1)| x_c1.is_zero() && y_c1.is_zero())
            };
            
            let adj_offset = AffinePointExt::constant(
                params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
                params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
                params
            );

            // adj_offset is a point of order 3, hence one of acc, acc + adj_offset, acc - adj belong to E(F_p)
            let mut acc = acc.get_as_ext_point();
            let need_to_negate_wit = acc.get_value().map(|(x_c0, x_c1, y_c0, y_c1)| {
                let gate_count_start = cs.get_current_step_number();
                let mut tmp = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, params);
                tmp = tmp.add_unequal_unchecked(cs, &adj_offset).expect("should synthesize");
                let flag = is_defined_over_base_field(&tmp).expect("should be some");    
                   
                let gate_count_end = cs.get_current_step_number();
                assert_eq!(gate_count_end - gate_count_start, 0);
                !flag
            });
    
            let need_to_negate = Boolean::Is(AllocatedBit::alloc(cs, need_to_negate_wit)?);
            let mut to_add = adj_offset.conditionally_negate(cs, &need_to_negate)?;
            let (modified_acc, possible_infty_flag_1) = if exception_free_version {
                acc.prudent_add(cs, &mut to_add)?
            } else {
                let res = acc.add_unequal(cs, &mut to_add)?;
                (res, Boolean::constant(false))
            };
            let cond_wit = is_defined_over_base_field(&modified_acc);
            let cond = Boolean::Is(AllocatedBit::alloc(cs, cond_wit)?);
            let res_ext = AffinePointExt::conditionally_select(cs, &cond, &modified_acc, &acc)?; 

            let infty_flag_1 = Boolean::and(cs, &possible_infty_flag_1, &cond)?;
            let infty_flag = Boolean::or(cs, &infty_flag_0, &infty_flag_1)?;

            let mut final_x = res_ext.get_x();
            let mut final_y = res_ext.get_y();

            let mut zero = FieldElement::<E, G::Base>::zero(&params.base_field_rns_params);
            final_x.c1 = FieldElement::conditionally_select(cs, &infty_flag, &zero, &final_x.c1)?;
            final_y.c1 = FieldElement::conditionally_select(cs, &infty_flag, &zero, &final_x.c1)?;
            FieldElement::enforce_equal(cs, &mut final_x.c1, &mut zero)?;
            FieldElement::enforce_equal(cs, &mut final_y.c1, &mut zero)?;
            (PointWrapper::AffineOverExtField(res_ext), infty_flag)
        } else {
            (acc, infty_flag_0)
        };

        let (result, _) = acc.convert_to_affine_or_uninitialized(
            cs, infty_flag.get_value().unwrap_or(false)
        )?; 
        Ok((result, infty_flag))
    }
}

// when we allow exceptions accumulator is allowed to be in the main group - it would be just an arbitrary
// point with unknown discrete logarithm. If we aim at exceptionfreeness we take offset_generator to be a point
// defined over E(F_q^2).
// When algorithm is formula is exception-free we say that it is complete
#[derive(Clone, Debug)]
pub enum PointWrapper<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField {
    AffineOverBaseField(AffinePoint<'a, E, G, T>),
    AffineOverBaseFieldInCofactor(AffinePoint<'a, E, G, T>),
    AffineOverExtField(AffinePointExt<'a, E, G, T>),
    HomogeniousForm(ProjectivePoint<'a, E, G, T>)
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> PointWrapper<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    pub fn get_as_ext_point(self) -> AffinePointExt<'a, E, G, T> {
        if let PointWrapper::AffineOverExtField(x) = self {
            x
        } else {
            unreachable!()
        }
    }
    
    pub fn add_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, x: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = point.add_unequal(cs, x)?;
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                let res = point.add_unequal_unchecked(cs, x)?;
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            }
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
        &mut self, cs: &mut CS, x: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = point.sub_unequal(cs, x)?;
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                let res = point.sub_unequal_unchecked(cs, x)?;
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            }
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
            PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                let res = AffinePoint::double(point, cs)?; 
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            }
            PointWrapper::AffineOverExtField(point_ext) => {
                let res = AffinePointExt::double(point_ext, cs)?;
                PointWrapper::AffineOverExtField(res)
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                let res = ProjectivePoint::double(point_proj, cs)?;
                PointWrapper::HomogeniousForm(res)
            },
        };

        Ok(res)
    }
    
    pub fn double_and_add_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, x: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) => {
                let res = point.double_and_add_unequal(cs, x)?; 
                PointWrapper::AffineOverBaseField(res)
            },
            PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                let res = point.double_and_add_unequal_unchecked(cs, x)?; 
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                let res = point_ext.mixed_double_and_add_unequal_unchecked(cs, x)?;
                PointWrapper::AffineOverExtField(res)
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                let res = ProjectivePoint::double(point_proj, cs)?;
                let res = res.add_mixed(cs, x)?;
                PointWrapper::HomogeniousForm(res)
            },
        };

        Ok(res)
    }

    pub fn convert_to_affine_or_uninitialized<CS: ConstraintSystem<E>>(
        self, cs: &mut CS, check_correctness: bool
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> 
    {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) | PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                (point.clone(), Boolean::constant(false))
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                let final_x = point_ext.get_x().c0;
                let final_y = point_ext.get_y().c0;
                let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
                    if check_correctness {
                        G::from_xy_checked(x, y).expect("should be on the curve")
                    } else {
                        G::from_xy_unchecked(x, y)
                    }
                });
                let point = AffinePoint { 
                    x: final_x, 
                    y: final_y, 
                    value: final_value, 
                    circuit_params: point_ext.circuit_params 
                };
                (point, Boolean::constant(false))
            },
            PointWrapper::HomogeniousForm(mut point_proj) => {
                point_proj.convert_to_affine_or_uninitialized(cs)?
            },
        };

        Ok(res)
    }

    pub fn convert_to_projective(self) -> ProjectivePoint<'a, E, G, T>
    {
        let res = match self {
            PointWrapper::AffineOverBaseField(point) | PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                ProjectivePoint::from(point)
            },
            PointWrapper::AffineOverExtField(_point_ext) => {
                unreachable!();
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                point_proj
            },
        };

        res
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, left: &Self, right: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let res = match (left, right) {
            (PointWrapper::AffineOverBaseField(x), PointWrapper::AffineOverBaseField(y)) => {
                let res = AffinePoint::conditionally_select(cs, flag, x, y)?;
                PointWrapper::AffineOverBaseField(res)
            },
            (PointWrapper::AffineOverBaseFieldInCofactor(x), PointWrapper::AffineOverBaseFieldInCofactor(y)) => {
                let res = AffinePoint::conditionally_select(cs, flag, x, y)?;
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            },
            (PointWrapper::AffineOverExtField(x), PointWrapper::AffineOverExtField(y)) => {
                let res = AffinePointExt::conditionally_select(cs, flag, x, y)?;
                PointWrapper::AffineOverExtField(res)
            },
            (PointWrapper::HomogeniousForm(x), PointWrapper::HomogeniousForm(y)) => {
                let res = ProjectivePoint::conditionally_select(cs, flag, x, y)?;
                PointWrapper::HomogeniousForm(res)
            }
            _ => unreachable!(),
        };

        Ok(res)
    }

    pub fn checked_add<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let res = match (self, other) {
            (PointWrapper::AffineOverBaseField(point), PointWrapper::AffineOverBaseField(x))  => {
                let res = point.add_unequal(cs, x)?; 
                PointWrapper::AffineOverBaseField(res)
            },
            (PointWrapper::AffineOverBaseFieldInCofactor(point), PointWrapper::AffineOverBaseFieldInCofactor(x)) => 
            {
                let res = point.add_unequal(cs, x)?; 
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            },
            (PointWrapper::AffineOverExtField(point_ext), PointWrapper::AffineOverExtField(x))  => {
                let res = point_ext.add_unequal(cs, x)?;
                PointWrapper::AffineOverExtField(res)
            },
            (PointWrapper::HomogeniousForm(point_proj), PointWrapper::HomogeniousForm(x))  => {
                let res = point_proj.add(cs, x)?;
                PointWrapper::HomogeniousForm(res)
            },
            _ => unreachable!(),
        };

        Ok(res)
    }

    pub fn checked_sub<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let res = match (self, other) {
            (PointWrapper::AffineOverBaseField(point), PointWrapper::AffineOverBaseField(x))  => {
                let res = point.sub_unequal(cs, x)?; 
                PointWrapper::AffineOverBaseField(res)
            },
            (PointWrapper::AffineOverBaseFieldInCofactor(point), PointWrapper::AffineOverBaseFieldInCofactor(x)) => 
            {
                let res = point.sub_unequal(cs, x)?; 
                PointWrapper::AffineOverBaseFieldInCofactor(res)
            },
            (PointWrapper::AffineOverExtField(point_ext), PointWrapper::AffineOverExtField(x))  => {
                let res = point_ext.sub_unequal(cs, x)?;
                PointWrapper::AffineOverExtField(res)
            },
            (PointWrapper::HomogeniousForm(point_proj), PointWrapper::HomogeniousForm(x))  => {
                let res = point_proj.sub(cs, x)?;
                PointWrapper::HomogeniousForm(res)
            },
            _ => unreachable!(),
        };

        Ok(res)
    }

    pub fn prudent_add<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<(Self, Boolean), SynthesisError> {
        let res = match (self, other) {
            (PointWrapper::AffineOverBaseField(point), PointWrapper::AffineOverBaseField(x))  => {
                let (res, is_garbage) = point.prudent_add(cs, x)?; 
                (PointWrapper::AffineOverBaseField(res), is_garbage)
            },
            (PointWrapper::AffineOverBaseFieldInCofactor(point), PointWrapper::AffineOverBaseFieldInCofactor(x)) => 
            {
                let (res, is_garbage) = point.prudent_add(cs, x)?; 
                (PointWrapper::AffineOverBaseFieldInCofactor(res), is_garbage)
            },
            (PointWrapper::AffineOverExtField(point_ext), PointWrapper::AffineOverExtField(x))  => {
                let (res, is_garbage) = point_ext.prudent_add(cs, x)?;
                (PointWrapper::AffineOverExtField(res), is_garbage)
            },
            (PointWrapper::HomogeniousForm(point_proj), PointWrapper::HomogeniousForm(x))  => {
                let res = point_proj.add(cs, x)?;
                (PointWrapper::HomogeniousForm(res), Boolean::constant(false))
            },
            _ => unreachable!(),
        };

        Ok(res)
    }

    pub fn prudent_sub<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<(Self, Boolean), SynthesisError> {
        let res = match (self, other) {
            (PointWrapper::AffineOverBaseField(point), PointWrapper::AffineOverBaseField(x))  => {
                let (res, is_garbage) = point.prudent_sub(cs, x)?; 
                (PointWrapper::AffineOverBaseField(res), is_garbage)
            },
            (PointWrapper::AffineOverBaseFieldInCofactor(point), PointWrapper::AffineOverBaseFieldInCofactor(x)) => 
            {
                let (res, is_garbage) = point.prudent_sub(cs, x)?; 
                (PointWrapper::AffineOverBaseFieldInCofactor(res), is_garbage)
            },
            (PointWrapper::AffineOverExtField(point_ext), PointWrapper::AffineOverExtField(x))  => {
                let (res, is_garbage) = point_ext.prudent_sub(cs, x)?;
                (PointWrapper::AffineOverExtField(res), is_garbage)
            },
            (PointWrapper::HomogeniousForm(point_proj), PointWrapper::HomogeniousForm(x))  => {
                let res = point_proj.sub(cs, x)?;
                (PointWrapper::HomogeniousForm(res), Boolean::constant(false))
            },
            _ => unreachable!(),
        };

        Ok(res)
    }

    pub fn get_params(&self) -> &'a CurveCircuitParameters<E, G, T> {
        match self {
            PointWrapper::AffineOverBaseField(point) | PointWrapper::AffineOverBaseFieldInCofactor(point) => {
                point.circuit_params
            },
            PointWrapper::AffineOverExtField(point_ext) => {
                point_ext.circuit_params
            },
            PointWrapper::HomogeniousForm(point_proj) => {
                point_proj.circuit_params
            }
        }
    }
}


pub(crate) trait Selector<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>>
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    fn new(geometry: MultiExpGeometry) -> Self;
    
    fn absorb_precompute<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, precompute: Vec<(u64, AffinePoint<'a, E, G, T>)>
    ) -> Result<(), SynthesisError>;
    
    fn select<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean], params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError>;
    
    fn postprocess<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>;
}


const RATE: usize = 2;
const WIDTH: usize = 3;

fn round_function_absorb<E: Engine, CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
    cs: &mut CS, state: &mut [Num<E>; WIDTH], input: &[Num<E>], hash_params: &P
) -> Result<(), SynthesisError> 
{
    assert_eq!(input.len(), RATE);
    
    let mut state_lcs = vec![];
    for (s, inp) in state.iter().zip(input.iter())  {
        let mut lc = LinearCombination::from(*s);
        lc.add_assign_number_with_coeff(&inp, E::Fr::one());
        state_lcs.push(lc);
    }

    for s in state[input.len()..].iter() {
        let lc = LinearCombination::from(*s);
        state_lcs.push(lc);
    }

    let mut state_lcs = state_lcs.try_into().expect("state width should match");
    
    use crate::plonk::circuit::curve::ram_via_hashes::circuit::sponge::circuit_generic_round_function;
    circuit_generic_round_function(cs, &mut state_lcs, hash_params)?;

    for (a, b) in state.iter_mut().zip(state_lcs.iter()) {
        *a = b.clone().into_num(cs)?;
    }

    Ok(())
}

fn round_function_squeeze<E: Engine>(state: &[Num<E>; WIDTH]) -> (Num<E>, Num<E>) {
    (state[0].clone(), state[1].clone())
}


pub(crate) struct Memory<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    queries: Vec<(Num<E>, AffinePoint<'a, E, G, T>)>,
    witness_map: HashMap<u64, Option<G>>,
    address_width: usize,
    validity_is_enforced: bool,
    permutation_enforcement_strategy: MultiexpStrategy,

    permutation: IntegerPermutation,
    unsorted_packed_elems_0: Vec<Num<E>>,
    unsorted_packed_elems_1: Vec<Num<E>>,
    sorted_packed_elems_0: Vec<Num<E>>,
    sorted_packed_elems_1: Vec<Num<E>>,
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Drop for Memory<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    fn drop(&mut self) {
        assert!(self.validity_is_enforced);
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Memory<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField
{
    pub fn new(address_width: usize, permutation_enforcement_strategy: MultiexpStrategy) -> Self {
        Self {
            queries: vec![],
            witness_map: HashMap::new(),
            address_width,
            validity_is_enforced: false,
            permutation_enforcement_strategy,

            permutation: IntegerPermutation::new(1),
            unsorted_packed_elems_0: vec![],
            unsorted_packed_elems_1: vec![],
            sorted_packed_elems_0: vec![],
            sorted_packed_elems_1: vec![],
        }
    }

    pub fn write(&mut self, addr: u64, point: AffinePoint<'a, E, G, T>) {
        assert!(crate::log2_floor(addr as usize) as usize <= self.address_width);
        self.witness_map.insert(addr, point.get_value());
        let addr_as_num = Num::Constant(u64_to_ff(addr));
        self.queries.push((addr_as_num, point));
        self.validity_is_enforced = false; 
    }

    pub fn read<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, addr: Num<E>, params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
        let wit = addr.get_value().and_then(|x| { self.witness_map.get(&ff_to_u64(&x)).cloned().unwrap_or(None) });
        let res = AffinePoint::alloc(cs, wit, params)?;
        self.queries.push((addr, res.clone()));
        self.validity_is_enforced = false;

        Ok(res)
    }

    fn calculate_permutation(&self) -> IntegerPermutation {
        let mut keys = Vec::with_capacity(self.queries.len());
        for (idx, (addr, _)) in self.queries.iter().enumerate() {
            if let Some(addr) = addr.get_value() {
                let composite_key = ff_to_u64(&addr);
                keys.push((idx, composite_key));
            } else {
                return IntegerPermutation::new(self.queries.len());
            }
        }

        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();
        IntegerPermutation::new_from_permutation(integer_permutation)
    }

    fn enforce_correctness_of_sorted_packed_queries<CS>(&mut self, cs: &mut CS)-> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let limit = Num::Constant(u64_to_ff((1u64 << self.address_width) - 1));
        let mut counter = Num::zero();
        let iter = self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter()).identify_first_last();
        let mut el_0_prev = Num::zero();
        let mut el_1_prev = Num::zero();
    
        for (is_first, _is_last, (el_0_cur, el_1_cur)) in iter {
            if !is_first {
                let is_equal_0 = Num::equals(cs, &el_0_prev, &el_0_cur)?;
                let is_equal_1 = Num::equals(cs, &el_1_prev, &el_1_cur)?;
                let both_are_equal = Boolean::and(cs, &is_equal_0, &is_equal_1)?;
                counter = counter.conditionally_increment(cs, &both_are_equal.not())?;
            }
           
            el_0_prev = *el_0_cur;
            el_1_prev = *el_1_cur;
        }
        counter.enforce_equal(cs, &limit)
    }

    pub fn enforce_ram_correctness<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> 
    {
        self.validity_is_enforced = true;
        let size = self.queries.len();

        let permutation = self.calculate_permutation();
        
        let mut unsorted_packed_elems_0 = Vec::with_capacity(size);
        let mut unsorted_packed_elems_1 = Vec::with_capacity(size);
        let mut sorted_packed_elems_0 = Vec::with_capacity(size);
        let mut sorted_packed_elems_1 = Vec::with_capacity(size);

        for (addr, point) in self.queries.iter_mut() {
            let packed = point.pack(cs, addr, self.address_width)?;
            unsorted_packed_elems_0.push(packed[0]);
            unsorted_packed_elems_1.push(packed[1]);
        }
        for index in permutation.elements.iter() {
            let value_0 = unsorted_packed_elems_0[*index].clone();
            sorted_packed_elems_0.push(value_0);
            let value_1 = unsorted_packed_elems_1[*index].clone();
            sorted_packed_elems_1.push(value_1);
        }

        self.permutation = permutation;
        self.unsorted_packed_elems_0 = unsorted_packed_elems_0;
        self.unsorted_packed_elems_1 = unsorted_packed_elems_1;
        self.sorted_packed_elems_0 = sorted_packed_elems_0;
        self.sorted_packed_elems_1 = sorted_packed_elems_1;

        self.enforce_correctness_of_permutation(cs)?;
        self.enforce_correctness_of_sorted_packed_queries(cs)
    }

    fn enforce_correctness_of_permutation<CS>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        match self.permutation_enforcement_strategy {
            MultiexpStrategy::WaksmanBasedRam => {
                // better investigate Waksman code more
                let switches = order_into_switches_set(cs, &self.permutation)?;
                prove_permutation_of_nums_using_switches_witness(
                    cs, &self.sorted_packed_elems_0, &self.unsorted_packed_elems_0, &switches
                )?;
                prove_permutation_of_nums_using_switches_witness(
                    cs, &self.sorted_packed_elems_1, &self.unsorted_packed_elems_1, &switches
                )
            },
            MultiexpStrategy::HashSetsBasedRam => {
                let hash_params = RescuePrimeParams::<E, RATE, WIDTH>::new_with_width4_custom_gate();
                let mut state = [Num::<E>::zero(); WIDTH];

                let iter = self.unsorted_packed_elems_0.iter().zip(self.unsorted_packed_elems_1.iter()).chain(
                    self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter())
                );
                for (x, y) in iter {
                    let input = [x.clone(), y.clone()];
                    round_function_absorb(cs, &mut state, &input, &hash_params)?;
                };
                let (challenge_a, challenge_b) = round_function_squeeze(&state);

                // (Polynomials are of the form X + c0 * Y + c1)
                // we substitute X and Y with challenge a and b correspondingly
                let mut lhs = Num::Constant(E::Fr::one());
                let mut rhs = Num::Constant(E::Fr::one());
                
                let outer_iter = std::iter::once(
                    (&self.unsorted_packed_elems_0, &self.unsorted_packed_elems_1, &mut lhs)
                ).chain(std::iter::once(
                    (&self.sorted_packed_elems_0, &self.sorted_packed_elems_1, &mut rhs)
                ));
                for (column_0, column_1, out) in outer_iter {
                    let inner_iter = column_0.iter().zip(column_1.iter());
                    for (c0, c1) in inner_iter {
                        let mut lc = LinearCombination::zero(); 
                        lc.add_assign_number_with_coeff(&challenge_a.clone(), E::Fr::one());
                        lc.add_assign_number_with_coeff(&c1, E::Fr::one());
                        let c0_mul_challenge = c0.mul(cs, &challenge_b)?;
                        lc.add_assign_number_with_coeff(&c0_mul_challenge, E::Fr::one());
                        let multiplier = lc.into_num(cs)?;
                        *out = Num::mul(out, cs, &multiplier)?;
                    }
                } 
                lhs.enforce_equal(cs, &rhs)
            },
            _ => unreachable!(),
        }    
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T> Selector<'a, E, G, T> for Memory<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    fn new(geometry: MultiExpGeometry) -> Self {
        Self::new(geometry.width * 2, geometry.strategy)
    }
    
    fn absorb_precompute<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, precompute: Vec<(u64, AffinePoint<'a, E, G, T>)>
    ) -> Result<(), SynthesisError> {
        for (addr, point) in precompute.into_iter() {
            let bitflipped_addr = !addr & ((1 << self.address_width) - 1);
            let point_negated = point.negate(cs)?;
            self.write(addr, point);
            self.write(bitflipped_addr, point_negated);
        }
        Ok(())
    }
    
    fn select<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean], params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
        let mut offset = E::Fr::one();
        let mut lc = LinearCombination::zero();
        for bit in bits.iter() {
            lc.add_assign_boolean_with_coeff(bit, offset);
            offset.double();
        }
        let addr = lc.into_num(cs)?;
        self.read(cs, addr, params)
    }
    
    fn postprocess<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.enforce_ram_correctness(cs)
    }
}


// // The purpose of Tree Selector is the following: 
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
pub(crate) struct TreeSelector<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField {
    precompute: Vec<AffinePoint<'a, E, G, T>>
}

impl<'a, E: Engine, G: GenericCurveAffine, T> Selector<'a, E, G, T> for TreeSelector<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    fn new(_geometry: MultiExpGeometry) -> Self {
        TreeSelector {
            precompute: vec![]
        }
    }
    
    fn absorb_precompute<CS: ConstraintSystem<E>>(
        &mut self, _cs: &mut CS, mut precompute: Vec<(u64, AffinePoint<'a, E, G, T>)>
    ) -> Result<(), SynthesisError> {
        self.precompute.extend(precompute.drain(..).map(|x| x.1));
        Ok(())
    }
    
    fn select<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean], _params: &CurveCircuitParameters<E, G, T>
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
        let mut selector_subtree = self.precompute.clone(); 
        
        for (k0_bit, k1_bit) in bits.iter().rev().tuple_windows() {
            let mut new_selector_subtree = Vec::with_capacity(selector_subtree.len() >> 1);
            let xor_flag = Boolean::xor(cs, &k0_bit, &k1_bit)?;
            for (first, second) in selector_subtree.into_iter().tuples() {
                let selected = AffinePoint::conditionally_select(cs, &xor_flag, &first, &second)?;
                new_selector_subtree.push(selected);
            }
            selector_subtree = new_selector_subtree;
        }

        assert_eq!(selector_subtree.len(), 1);
        let last_flag = bits[0];
        let selected = selector_subtree.pop().unwrap();
        let candidate = AffinePoint::conditionally_negate(&selected, cs, &last_flag.not())?;
        
        Ok(candidate)    
    }
    
    fn postprocess<CS: ConstraintSystem<E>>(&mut self, _cs: &mut CS) -> Result<(), SynthesisError> {
        Ok(())
    }
}


#[derive(Clone, Debug)]
pub(crate) struct Combiner<'a, E: Engine, G: GenericCurveAffine, T, S: Selector<'a, E, G, T>> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    entries: Vec<AffinePoint<'a, E, G, T>>, // raw elements P1, P2, ..., Pn
    selector_impl: S,
    exception_free_version: bool,

    initial_point_affine: AffinePoint<'a, E, G, T>,
    initial_point_proj: ProjectivePoint<'a, E, G, T>,
    initial_point_is_infty: Boolean,
    params: &'a CurveCircuitParameters<E, G, T>,
}

impl<'a, E: Engine, G: GenericCurveAffine, T, S: Selector<'a, E, G, T>> Combiner<'a, E, G, T, S> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    pub fn get_initial(&self) -> (AffinePoint<'a, E, G, T>, Boolean, ProjectivePoint<'a, E, G, T>) {
        (self.initial_point_affine.clone(), self.initial_point_is_infty, self.initial_point_proj.clone())
    }

    pub fn postprocess<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.selector_impl.postprocess(cs)
    }
    
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, entries: &[AffinePoint<'a, E, G, T>], 
        geometry: MultiExpGeometry, exception_free_version: bool
    ) -> Result<Self, SynthesisError> {
        let first_elem = entries.get(0).expect("Entries must be nonempty");
        let params = first_elem.circuit_params;
        // for now we do not work over BLS12-381 but all it trvially extendable
        assert_eq!(params.is_prime_order_curve, true);

        let get_bit_at_pos = |num: u64, pos: usize| -> bool {
            (num >> pos) & 1 != 0
        };
        let extend_addr = |num: u64, pos: usize, msb: bool| -> u64 {
            if msb { (1u64 << (pos+1)) + num } else { num }
        }; 
        
        let initial = if exception_free_version {
            PointWrapper::HomogeniousForm(ProjectivePoint::from(first_elem.clone()))
        } else {
            PointWrapper::AffineOverBaseField(first_elem.clone())
        };

        // using Selector tree makes sense only if there are more than 1 element
        let mut entries = entries.to_vec();
        let mut workpad : Vec<(u64, PointWrapper<'a, E, G, T>)> = vec![(1, initial)];
        let mut pos = 0;

        for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
            let mut new_working_pad = Vec::with_capacity(workpad.len() << 1);
            for (addr, acc) in workpad.iter_mut() {
                let msb = get_bit_at_pos(*addr, pos);
                if msb { 
                    new_working_pad.push((extend_addr(*addr, pos, !msb), acc.sub_mixed(cs, elem)?));
                    new_working_pad.push((extend_addr(*addr, pos, msb), acc.add_mixed(cs, elem)?));   
                }
                else {
                    new_working_pad.push((extend_addr(*addr, pos, !msb), acc.add_mixed(cs, elem)?));   
                    new_working_pad.push((extend_addr(*addr, pos, msb), acc.sub_mixed(cs, elem)?));
                }
            };
            pos += 1;
            workpad = new_working_pad
        }
        assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
        let mut precompute = Vec::with_capacity(workpad.len());
        let mut initial_point_affine = AffinePoint::uninitialized(params);
        let mut initial_point_is_infty = Boolean::constant(false);
        let mut initial_point_proj = ProjectivePoint::zero(params);

        for (_is_first, is_last, elem) in workpad.into_iter().identify_first_last() {
            let (addr, wrapped_point) = elem;
            let (point_affine, is_infty) = wrapped_point.clone().convert_to_affine_or_uninitialized(cs, true)?;
            
            if is_last {
                initial_point_affine = point_affine.clone();
                initial_point_is_infty = is_infty;
                initial_point_proj = wrapped_point.convert_to_projective();
            }
            precompute.push((addr, point_affine));
        }

        let mut selector = S::new(geometry);
        selector.absorb_precompute(cs, precompute)?;

        Ok(Combiner {
            entries,
            selector_impl: selector,
            exception_free_version,
            initial_point_affine,
            initial_point_is_infty,
            initial_point_proj,
            params
        })
    }

    fn select<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean]
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        let candidate = self.selector_impl.select(cs, bits, self.params)?;
        let checked_candidate = if self.exception_free_version {
            (candidate, Boolean::constant(false))
        } else {
            let is_point_at_infty = FieldElement::is_zero(&mut candidate.get_y(), cs)?;
            (candidate, is_point_at_infty)
        };
        Ok(checked_candidate)
    }

    fn select_last<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean]
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
        // we want to retrieve the point which is dependent on bits as follows:
        // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
        // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
        // if we denote the starting value of accumulator = /sum P_i as C
        // then it is obvious that the following relation always holds: A - C = 2 * B
        // hence we reduced the computation to one subtraction and one doubling
        let rns_params = &self.params.base_field_rns_params;
        let (selected, is_selected_point_at_infty) = self.select(cs, &bits)?;
       
        let proj_x = selected.get_x();
        let proj_y = FieldElement::conditionally_select(
            cs, &is_selected_point_at_infty, &FieldElement::one(rns_params), &selected.get_y()
        )?;
        let proj_z = FieldElement::conditionally_select(
            cs, &is_selected_point_at_infty, &FieldElement::zero(rns_params), &FieldElement::one(rns_params)
        )?;
        let a = ProjectivePoint::from_coordinates_unchecked(proj_x, proj_y, proj_z, self.params);
        
        let (_, _, c) = self.get_initial();
        let mut a_minus_c = a.sub(cs, &c)?;
        let mut res_proj = ProjectivePoint::halving(&mut a_minus_c, cs)?;
        res_proj.convert_to_affine_or_uninitialized(cs)
    }
}
   
   
impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub fn mul_by_scalar_complete<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<(Self, Boolean), SynthesisError> {
        self.mul_by_scalar_impl(cs, scalar, true)
    }
    
    pub fn mul_by_scalar_non_complete<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<Self, SynthesisError> {
        let (point, _is_infty) = self.mul_by_scalar_impl(cs, scalar, false)?;
        Ok(point)
    }

    #[track_caller]
    fn mul_by_scalar_impl_wth_accumulator<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, mut acc: PointWrapper<'a, E, G, T> 
    ) -> Result<(PointWrapper<'a, E, G, T>, usize), SynthesisError> {
        if scalar.is_constant() {
            unimplemented!();
        }
        let params = self.circuit_params;
        let aux_data = Self::compute_endo_aux_data(cs, self, scalar)?;
        let point_minus_point_endo = aux_data.point.sub_unequal_unchecked(cs, &aux_data.point_endo)?;
        let mut point_plus_point_endo = aux_data.point.add_unequal_unchecked(cs, &aux_data.point_endo)?;
        
        let mut acc = acc.add_mixed(cs, &mut point_plus_point_endo)?;
        let num_of_doubles = aux_data.point_scalar_decomposition[1..].len();
        let iter = aux_data.point_scalar_decomposition[1..].iter().zip(
            aux_data.point_endo_scalar_decomposition[1..].iter()
        ).rev();

        // if x = [x_0, x_1, ..., x_n] = /sum x_i 2^i - binary representation of x: x_i /in {0, 1}
        // then x = [y_-1, y_0, y_1, ..., y_n] - skewed naf representation: where y_i /in {0, 1}
        // x = -y_-1 + /sum_{i >= 1} (1 - 2* y_i) 2^i
        // algorithm for construction of skewed representation: 
        // for -1 <= y < n: y_i = ~x_{i+1} = 1 - x_{i+1} and y_n = 0 (always)
        // indeed:
        // y = -y_-1 + /sum (1 - 2* y_i) 2^i = x_0 - 1 + /sum (2* x_{i+1} - 1) 2^i +2^n = 
        // = x - 1 - \sum_{i=0}^{n-1} 2^i + 2^n = x - 1 - (2^n - 1) + 2^n = x

        for (k1_bit, k2_bit) in iter {
            // selection tree looks like following:
            //                              
            //                         |true --- P + Q
            //         |true---k2_bit--|
            //         |               |false --- P - Q
            // k1_bit--|
            //         |        
            //         |                |true --- -P + Q
            //         |false---k2_bit--|
            //                          |false --- -P - Q
            //
            // hence:
            // res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
            // tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
            // res.Y = conditionally_negate(!k1, tmp.Y)
            let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
            let selected_x = FieldElement:: conditionally_select(
                cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
            )?;
            let tmp_y = FieldElement::conditionally_select(
                cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
            )?;
            let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
            let mut tmp = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) };
            acc = acc.double_and_add_mixed(cs, &mut tmp)?;
        }

        // we subtract either O, or P, or Q or P + Q
        // selection tree in this case looks like following:
        //                              
        //                         |true --- O
        //         |true---k2_bit--|
        //         |               |false --- Q
        // k1_bit--|
        //         |        
        //         |                |true --- P
        //         |false---k2_bit--|
        //                          |false --- P+Q
        //
        let k1_bit = aux_data.point_scalar_decomposition.first().unwrap();
        let k2_bit = aux_data.point_endo_scalar_decomposition.first().unwrap();
        let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
        let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &aux_data.point, &point_plus_point_endo)?;
        tmp = AffinePoint::conditionally_select(cs, &k1_bit, &aux_data.point_endo, &tmp)?;
        let skew_acc = acc.sub_mixed(cs, &mut tmp)?;
        acc = PointWrapper::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;

        Ok((acc, num_of_doubles))
    }

    
    fn mul_by_scalar_impl<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, exception_free_version: bool
    ) -> Result<(Self, Boolean), SynthesisError> {
        let params = self.circuit_params;
        let offset_generator = Self::get_offset_generator(exception_free_version, params);
        let (acc, num_of_doubles) = self.mul_by_scalar_impl_wth_accumulator(cs, scalar, offset_generator.clone())?;
        Self::final_normalization(cs, acc, offset_generator, num_of_doubles, false, exception_free_version)
    } 
   
    pub fn multiexp_complete<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &mut [Self] 
    ) -> Result<(Self, Boolean), SynthesisError> {
        let params = points[0].circuit_params;
        let geometry = params.get_opt_multiexp_geometry();
        Self::multiexp_impl(cs, scalars, points, geometry, true)
    }

    pub fn multiexp_non_complete<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &mut [Self] 
    ) -> Result<Self, SynthesisError> {
        let params = points[0].circuit_params;
        let geometry = params.get_opt_multiexp_geometry();
        let (point, _is_infty) = Self::multiexp_impl(cs, scalars, points, geometry, false)?;
        Ok(point)
    }

    pub fn multiexp_complete_with_custom_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &mut [Self], gmtr: MultiExpGeometry 
    ) -> Result<(Self, Boolean), SynthesisError> {
        Self::multiexp_impl(cs, scalars, points, gmtr, true)
    }

    pub fn multiexp_non_complete_with_custom_geometry<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &mut [Self], gmtr: MultiExpGeometry 
    ) -> Result<Self, SynthesisError> {
        let (point, _is_infty) = Self::multiexp_impl(cs, scalars, points, gmtr, false)?;
        Ok(point)
    }

    #[track_caller]
    fn multiexp_impl<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &mut [Self], 
        geometry: MultiExpGeometry, exception_free_version: bool
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> 
    {
        assert_eq!(scalars.len(), points.len());
        let params = points[0].circuit_params;
        let offset_generator = Self::get_offset_generator(exception_free_version, params);
        
        let mut acc = offset_generator.clone();
        let mut idx = 0;
        let mut num_of_doubles = 0;

        while idx < points.len() {
            let chunk_size = std::cmp::min(points.len() - idx, geometry.width);
            let chunk_geometry = MultiExpGeometry {
                strategy: geometry.strategy,
                width: chunk_size,
            };
            let (new_acc, num_of_doubles_in_chunk) = if chunk_size > 1 {
                match geometry.strategy {
                    MultiexpStrategy::HashSetsBasedRam | MultiexpStrategy::WaksmanBasedRam => {
                        Self::multiexp_impl_chunk_processing::<CS, Memory<E, G, T>>(
                            cs, &mut scalars[idx..idx+chunk_size], &points[idx..idx+chunk_size], acc, 
                            exception_free_version, chunk_geometry
                        )?
                    },
                    MultiexpStrategy::SelectionTree => {
                        Self::multiexp_impl_chunk_processing::<CS, TreeSelector<E, G, T>>(
                            cs, &mut scalars[idx..idx+chunk_size], &points[idx..idx+chunk_size], acc, 
                            exception_free_version, chunk_geometry
                        )?
                    }
                }
            } else {
                points[idx].mul_by_scalar_impl_wth_accumulator(cs, &mut scalars[idx], acc)?
            };
            acc = new_acc;
            num_of_doubles += num_of_doubles_in_chunk;
            idx += chunk_size;
        }

        Self::final_normalization(
            cs, acc, offset_generator, num_of_doubles, exception_free_version, exception_free_version
        )
    }

    #[track_caller]
    fn safe_conversion_to_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS, candidate: &Self, is_point_at_infty: &Boolean
    ) -> Result<AffinePointExt<'a, E, G, T>, SynthesisError> {
        let params = candidate.circuit_params;
        let x_c0 = candidate.get_x();
        let x_c1 = FieldElement::zero(&params.base_field_rns_params);
        let y_c0 = candidate.get_y();
        let aux_c1 = FieldElement::constant(
            params.fp2_pt_ord3_y_c1.clone(), &params.base_field_rns_params
        );
        let y_c1 = FieldElement::conditionally_select(
            cs, &is_point_at_infty, &aux_c1, &FieldElement::zero(&params.base_field_rns_params)
        )?;

        let x_ext = Fp2::from_coordinates(x_c0, x_c1);
        let y_ext = Fp2::from_coordinates(y_c0, y_c1);
        let res = AffinePointExt { x: x_ext, y: y_ext, circuit_params: params };

        Ok(res)
    }

    #[track_caller]
    fn multiexp_impl_chunk_processing<CS: ConstraintSystem<E>, S: Selector<'a, E, G, T>>(
        cs: &mut CS, scalars: &mut [FieldElement<'a, E, G::Scalar>], points: &[Self], 
        mut acc: PointWrapper<'a, E, G, T>, exception_free_version: bool, geometry: MultiExpGeometry
    ) -> Result<(PointWrapper<'a, E, G, T>, usize), SynthesisError> 
    {
        assert_eq!(scalars.len(), points.len());
        let params = points[0].circuit_params;
                
        struct Multizip<T>(Vec<T>);
        
        impl<T> Iterator for Multizip<T>
        where T: Iterator,
        {
            type Item = Vec<T::Item>;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.iter_mut().map(Iterator::next).collect()
            }
        }
                
        let should_add_adj_generator = !params.is_prime_order_curve && exception_free_version;
        let mut points_unrolled = Vec::with_capacity(points.len() << 1);
        let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
        let iter = scalars.iter_mut().zip(points.iter()).identify_first_last();
        for (is_first, _is_last, (mut scalar, point)) in iter { 
            let aux_data = Self::compute_endo_aux_data(cs, point, &mut scalar)?;
            scalars_unrolled.push(aux_data.point_scalar_decomposition.into_iter().rev());
            scalars_unrolled.push(aux_data.point_endo_scalar_decomposition.into_iter().rev());

            let point_reg = if is_first && should_add_adj_generator {
                let x = G::from_xy_checked(params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_y_c0).expect("valid point");
                let adj_generator = AffinePoint::constant(x, params);
                aux_data.point.add_unequal_unchecked(cs, &adj_generator)?
            } else {
                aux_data.point.clone()
            };
            points_unrolled.push(point_reg);
            points_unrolled.push(aux_data.point_endo);
        }

        let exception_free_combiner = exception_free_version && params.is_prime_order_curve;
        let mut combiner = Combiner::<E, G, T, S>::new(cs, &points_unrolled, geometry, exception_free_combiner)?;
        let (mut initial, is_initial_point_at_infty, _) = combiner.get_initial();
        // I do not know how to get rid of this boilerplate code
        let mut acc = if exception_free_combiner {
            let to_add = Self::safe_conversion_to_ext(cs, &initial, &is_initial_point_at_infty)?;
            let acc_as_ext = acc.get_as_ext_point();
            let res = acc_as_ext.add_unequal_unchecked(cs, &to_add)?;
            PointWrapper::AffineOverExtField(res)
        } else {
            acc.add_mixed(cs, &mut initial)?
        };
       
        for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
            if !is_last {
                let (mut to_add, is_point_at_infty) = combiner.select(cs, &bits)?;
                acc = if exception_free_combiner {
                    let to_add = Self::safe_conversion_to_ext(cs, &to_add, &is_point_at_infty)?;
                    let acc_as_ext = acc.get_as_ext_point();
                    let res = acc_as_ext.double_and_add_unequal_unchecked(cs, &to_add)?;
                    PointWrapper::AffineOverExtField(res)
                } else {
                    acc.double_and_add_mixed(cs, &mut to_add)?
                };
            }
            else {
                let (mut to_add, is_point_at_infty) = combiner.select_last(cs, &bits)?;
                acc = if exception_free_combiner {
                    let to_add = Self::safe_conversion_to_ext(cs, &to_add, &is_point_at_infty)?;
                    let acc_as_ext = acc.get_as_ext_point();
                    let res = acc_as_ext.add_unequal_unchecked(cs, &to_add)?;
                    PointWrapper::AffineOverExtField(res)
                } else {
                    let acc_modified = acc.add_mixed(cs, &mut to_add)?;
                    PointWrapper::conditionally_select(cs, &is_point_at_infty, &acc, &acc_modified)?
                };
            }
        }

        combiner.postprocess(cs)?;
        let limit = params.get_endomorphism_bitlen_limit();
        Ok((acc, limit - 1))
    }
}


         


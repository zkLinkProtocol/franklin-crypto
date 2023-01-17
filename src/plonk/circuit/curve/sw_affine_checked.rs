use super::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::plonk::circuit::boolean::Boolean;
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

use crate::bellman::{
    SynthesisError,
};
use plonk::circuit::bigint::*;


// NB: works only if there are no points of order 2 on the curve
// So it al least works for all our three curves of interest
#[derive(Clone, Debug)]
pub struct AffinePointChecked<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>>  
where <G as GenericCurveAffine>::Base: PrimeField 
{
    inner: AffinePoint<'a, E, G, T>,
    is_infty: Boolean,
}

impl<'a, E, G, T> From<AffinePoint<'a, E, G, T>> for AffinePointChecked<'a, E, G, T>
where E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>, <G as GenericCurveAffine>::Base: PrimeField {
    fn from(value: AffinePoint<'a, E, G, T>) -> Self {
        AffinePointChecked {
            inner: value,
            is_infty: Boolean::Constant(false),
        }
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePointChecked<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField, G: rand::Rand {
    pub fn infty(circuit_params: &'a CurveCircuitParameters<E, G, T>) -> Self {
        AffinePointChecked {
            inner: AffinePoint::generator(circuit_params),
            is_infty: Boolean::Constant(true),
        }
    }

    pub fn is_constant(&self) -> bool {
        self.inner.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.is_infty.get_value().map(|flag| if flag { Some(G::zero()) } else { self.inner.value } ).flatten()
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        res.inner = res.inner.negate(cs)?;
        Ok(res)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let mut res = self.clone();
        res.inner = res.inner.conditionally_negate(cs, flag)?;
        Ok(res)
    }
   
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let inner = AffinePoint::conditionally_select(cs, flag, &first.inner, &second.inner)?;
        let is_infty = Boolean::conditionally_select(cs, flag, &first.is_infty, &second.is_infty)?;
        Ok(AffinePointChecked { inner, is_infty })
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        res.inner = res.inner.double(cs)?;
        Ok(res)
    }

    #[track_caller]
    pub fn add_mixed<CS>(&mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let xs_are_equal = FieldElement::equals(cs, &mut self.inner.x, &mut other.x)?;
        let mut other_negated_y = other.y.negate(cs)?;
        let ys_are_equal = FieldElement::equals(cs, &mut self.inner.y, &mut other_negated_y)?;
        let coords_are_equal = Boolean::and(cs, &xs_are_equal, &ys_are_equal)?;

        let lambda_for_double = {
            // lambda = (3 x^2) / (2 * y) 
            let x_squared = self.inner.x.square(cs)?;
            let x_squared_mul_3 = x_squared.scale(cs, 3)?;
            let two_y = self.inner.y.double(cs)?;
            FieldElement::div(&x_squared_mul_3, cs, &two_y)?
        };
        let lambda_for_add = {
            let mut chain = FieldElementsChain::new();
            let x_eq_flag_as_fe = FieldElement::from_boolean(&xs_are_equal, &other.circuit_params.base_field_rns_params);
            chain.add_pos_term(&other.x).add_neg_term(&self.inner.x).add_pos_term(&x_eq_flag_as_fe);
            let denom = FieldElement::collapse_chain(cs, chain)?;
            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&other.y).add_neg_term(&self.inner.y);
            FieldElement::div_with_chain(cs, chain, &denom)?
        };
        let lambda = FieldElement::conditionally_select(cs, &xs_are_equal, &lambda_for_double, &lambda_for_add)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.inner.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        let selected_x = FieldElement::conditionally_select(cs, &self.is_infty, &other.x, &new_x)?;
        let selected_y = FieldElement::conditionally_select(cs, &self.is_infty, &other.y, &new_y)?;  

        let inner = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, self.inner.circuit_params) };
        let is_infty = Boolean::and(cs, &coords_are_equal, &self.is_infty.not())?;
        Ok(AffinePointChecked { inner, is_infty})
    }

    pub fn double_and_add_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::double(&self, cs)?;
        tmp.add_mixed(cs, other)
    }  

    pub fn sub_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let mut tmp = AffinePoint::negate(other, cs)?;
        self.add_mixed(cs, &mut tmp)
    }

    #[track_caller]
    pub fn mul_by_scalar_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS, point: &mut AffinePoint<'a, E, G, T>, scalar: &mut FieldElement<'a, E, G::Scalar> 
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        if scalar.is_constant() {
            unimplemented!();
        }
        let params = point.circuit_params;
        let aux_data = AffinePoint::compute_endo_aux_data(cs, point, scalar)?;
        let point_minus_point_endo = aux_data.point.sub_unequal_unchecked(cs, &aux_data.point_endo)?;
        let point_plus_point_endo = aux_data.point.add_unequal_unchecked(cs, &aux_data.point_endo)?;

        let mut acc = Self::from(point_plus_point_endo.clone());
        let iter = aux_data.point_scalar_decomposition[1..].iter().zip(
            aux_data.point_endo_scalar_decomposition[1..].iter()
        ).rev();

        for (k1_bit, k2_bit) in iter {
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

        let k1_bit = aux_data.point_scalar_decomposition.first().unwrap();
        let k2_bit = aux_data.point_endo_scalar_decomposition.first().unwrap();
        let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
        let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &aux_data.point, &point_plus_point_endo)?;
        tmp = AffinePoint::conditionally_select(cs, &k1_bit, &aux_data.point_endo, &tmp)?;
        let skew_acc = acc.sub_mixed(cs, &mut tmp)?;
        acc = Self::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;

        let AffinePointChecked { inner, is_infty } = acc;
        Ok((inner, is_infty))
    }

    #[track_caller]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let xs_are_equal = FieldElement::equals(cs, &mut self.inner.x, &mut other.inner.x)?;
        let mut other_negated_y = other.inner.y.negate(cs)?;
        let ys_are_equal = FieldElement::equals(cs, &mut self.inner.y, &mut other_negated_y)?;
        let coords_are_equal = Boolean::and(cs, &xs_are_equal, &ys_are_equal)?;

        let lambda_for_double = {
            // lambda = (3 x^2) / (2 * y) 
            let x_squared = self.inner.x.square(cs)?;
            let x_squared_mul_3 = x_squared.scale(cs, 3)?;
            let two_y = self.inner.y.double(cs)?;
            FieldElement::div(&x_squared_mul_3, cs, &two_y)?
        };
        let lambda_for_add = {
            let mut chain = FieldElementsChain::new();
            let x_eq_flag_as_fe = FieldElement::from_boolean(
                &xs_are_equal, &other.inner.circuit_params.base_field_rns_params
            );
            chain.add_pos_term(&other.inner.x).add_neg_term(&self.inner.x).add_pos_term(&x_eq_flag_as_fe);
            let denom = FieldElement::collapse_chain(cs, chain)?;
            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&other.inner.y).add_neg_term(&self.inner.y);
            FieldElement::div_with_chain(cs, chain, &denom)?
        };
        let lambda = FieldElement::conditionally_select(cs, &xs_are_equal, &lambda_for_double, &lambda_for_add)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.x).add_neg_term(&other.inner.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.inner.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        // resulting_inner is equal to:
        // [self.is_infty] -> other.inner, other.is_infty -> self.inner, and (new_x, new_y) otherwise
        let mut selected_x = FieldElement::conditionally_select(cs, &self.is_infty, &other.inner.x, &new_x)?;
        selected_x = FieldElement::conditionally_select(cs, &other.is_infty, &self.inner.x, &selected_x)?;
        let mut selected_y = FieldElement::conditionally_select(cs, &self.is_infty, &other.inner.y, &new_y)?;
        selected_y = FieldElement::conditionally_select(cs, &other.is_infty, &self.inner.y, &selected_y)?;
        let inner = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, self.inner.circuit_params) };
        
        // is_infty = either booth_are_infty or both are not infty and coordinates are equal
        let both_is_infty = Boolean::and(cs, &self.is_infty, &other.is_infty)?;
        let tmp_check = Boolean::and(cs, &both_is_infty.not(), &coords_are_equal)?;
        let is_infty = Boolean::or(cs, &both_is_infty, &tmp_check)?;

        Ok(AffinePointChecked { inner, is_infty})
    }

    pub fn double_and_add<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::double(&self, cs)?;
        tmp.add(cs, other)
    }  

    pub fn sub<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::negate(other, cs)?;
        self.add(cs, &mut tmp)
    }
}

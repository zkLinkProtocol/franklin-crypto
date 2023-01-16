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


#[derive(Clone, Debug)]
pub enum MaskType {
    MaskByZero,
    MaskByOne,
}


#[derive(Clone, Debug)]
pub struct AffinePointChecked<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>>  
where <G as GenericCurveAffine>::Base: PrimeField 
{
    inner: AffinePoint<'a, E, G, T>,
    is_infty: Boolean,
    mask_type: MaskType
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePointChecked<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField {
    #[track_caller]
    pub fn from_point_and_mask_type(
        point: AffinePoint<'a, E, G, T>, mask_type: MaskType
    ) -> Self {
        AffinePointChecked {
            inner: point,
            is_infty: Boolean::Constant(false),
            mask_type
        }
    }

    fn construct_masked_x(
        rns_params: &'a RnsParameters<E, G::Base>, mask_type: MaskType
    ) -> FieldElement<'a, E, G::Base> {
        match mask_type {
            MaskType::MaskByZero => FieldElement::zero(rns_params),
            MaskType::MaskByOne => FieldElement::one(rns_params),
            _ => unreachable!()
        }
    } 

    pub fn infty(circuit_params: &'a CurveCircuitParameters<E, G, T>, mask_type: MaskType) -> Self {
        let x = Self::construct_masked_x(circuit_params.base_field_rns_params, mask_type);
        let y = FieldElement::zero(circuit_params.base_field_rns_params);
        AffinePointChecked {
            inner: AffinePoint::from_coordinates(x, y),
            is_infty: Boolean::Constant(true),
            mask_type
        }
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        FieldElement::enforce_equal(cs, &mut this.x, &mut other.x)?;
        FieldElement::enforce_equal(cs, &mut this.y, &mut other.y)
    }

    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let x_check = FieldElement::equals(cs, &mut this.x, &mut other.x)?;
        let y_check = FieldElement::equals(cs, &mut this.y, &mut other.y)?;
        let equals = Boolean::and(cs, &x_check, &y_check)?;
        
        Ok(equals)
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let y_negated = self.y.negate(cs)?;
        let new_value = self.value.map(|x| {
            let mut tmp = x;
            tmp.negate();
            tmp
        });
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            value: new_value,
            circuit_params: self.circuit_params
        };

        Ok(new)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let y_negated = self.y.conditionally_negate(cs, flag)?;
        let new_value = match (flag.get_value(), self.value) {
            (Some(flag), Some(x)) => {
                let mut tmp = x;
                if flag { tmp.negate() };
                Some(tmp)
            },
            _ => None,
        };
           
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            value: new_value,
            circuit_params: self.circuit_params,
        };

        Ok(new)
    }

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let first_value = first.get_value();
        let second_value = second.get_value();
        let x = FieldElement::conditionally_select(cs, flag, &first.x, &second.x)?;
        let y = FieldElement::conditionally_select(cs, flag, &first.y, &second.y)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };
        let selected = AffinePoint { x, y, value, circuit_params: first.circuit_params };

        Ok(selected)
    }

    #[track_caller]
    pub fn add_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // only enforce that x != x'
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.add_unequal_unchecked(cs, other)
    }

    #[track_caller]
    pub fn sub_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // only enforce that x != x'
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.sub_unequal_unchecked(cs, other)
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {}

    #[track_caller]
    pub fn double_and_add_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
}



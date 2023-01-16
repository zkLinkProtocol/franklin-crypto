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
pub struct TwistedCurvePoint<'a, E: Engine, G: GenericCurveAffine, F: PrimeField, T: Extension2Params<F, Witness = G::Base>>
{
    pub x: Fp2<'a, E, F, T>,
    pub y: Fp2<'a, E, F, T>,
    pub value: Option<G>,
} 

impl<'a, E: Engine, G: GenericCurveAffine, F: PrimeField, T> TwistedCurvePoint<'a, E, G, F, T> 
where T: Extension2Params<F, Witness = G::Base>
{
    pub fn get_x(&self) -> Fp2<'a, E, F, T> {
        self.x.clone()
    }

    pub fn get_y(&self) -> Fp2<'a, E, F, T> {
        self.y.clone()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn from_coordinates(x: Fp2<'a, E, F, T>, y: Fp2<'a, E, F, T>) -> Self {
        let witness = x.get_value().zip(y.get_value()).map(|(x, y)| {
            G::from_xy_unchecked(x, y)
        });
        Self { x, y, value: witness }
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, wit: Option<G>, rns_params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (x_wit, y_wit) = wit.map(|pt| pt.into_xy_unchecked()).unzip();
        let x = Fp2::alloc(cs, x_wit, rns_params)?;
        let y = Fp2::alloc(cs, y_wit, rns_params)?;
        let point = TwistedCurvePoint { x, y, value: wit };
        Ok(point)
    } 

    #[track_caller]
    pub fn constant(wit: G, rns_params: &'a RnsParameters<E, F>) -> Self {
        let (x_wit, y_wit) = wit.into_xy_unchecked();
        let x = Fp2::constant(x_wit, rns_params);
        let y = Fp2::constant(y_wit, rns_params);
        let point = TwistedCurvePoint { x, y, value: Some(wit) };
        point
    } 

    #[track_caller]
    fn is_on_curve_prepare<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS
    ) -> Result<(Fp2<'a, E, F, T>, Fp2<'a, E, F, T>), SynthesisError> {
        let rns_params = self.x.c0.representation_params;
        let a = Fp2::<E, F, T>::constant(G::a_coeff(), rns_params);
        let b = Fp2::constant(G::b_coeff(), rns_params);

        let lhs = self.y.square(cs)?;
        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let rhs = if a.get_value().unwrap().is_zero() {
            x_cubed.add(cs, &b)?
        } else {
            let mut chain = Fp2Chain::new();
            chain.add_pos_term(&x_cubed).add_pos_term(&b);
            Fp2::mul_with_chain(cs, &self.x, &a, chain)?
        };
        Ok((lhs, rhs))
    }

    #[track_caller]
    pub fn enforce_if_on_curve<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let (mut lhs, mut rhs) = self.is_on_curve_prepare(cs)?;
        Fp2::enforce_equal(cs, &mut lhs, &mut rhs)
    }

    #[track_caller]
    pub fn is_on_curve<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let (mut lhs, mut rhs) = self.is_on_curve_prepare(cs)?;
        Fp2::equals(cs, &mut lhs, &mut rhs)
    }

    pub fn generator(params: &'a RnsParameters<E, F>) -> Self {
        Self::constant(G::one(), params)
    }

    pub fn check_is_on_curve_and_replace<CS>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let invalid_point = self.is_on_curve(cs)?.not();
        let params = self.x.get_params();
        *self = Self::conditionally_select(cs, &invalid_point, &Self::generator(params), &self)?;
        Ok(invalid_point)
    }

    #[track_caller]
    pub fn enforce_equal<CS>(cs: &mut CS, left: &mut Self, right: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp2::enforce_equal(cs, &mut left.x, &mut right.x)?;
        Fp2::enforce_equal(cs, &mut left.y, &mut right.y)
    }

    pub fn add_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp2::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.add_unequal_unchecked(cs, other)
    }

    pub fn add_unequal_unchecked<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let (res, _slope) = self.add_unequal_unchecked_and_return_slope(cs, other)?;
        Ok(res)
    }

    #[track_caller]
    pub fn add_unequal_unchecked_and_return_slope<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self
    ) -> Result<(Self, Fp2<'a, E, F, T>), SynthesisError> {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                let (lhs_x, _lhs_y) = first.as_xy();
                let (rhs_x, _rhs_y) = second.as_xy();
                assert!(lhs_x != rhs_x, "can't add points with the same x cooridnate");
            },
            _ => {}
        }
        
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y);
        let lambda = Fp2::div_with_chain(cs, chain, &other_x_minus_this_x)?;
        
        // lambda^2 + (-x' - x)
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.y);
        let new_y = Fp2::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);
                Some(tmp.into_affine())
            },
            _ => None
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok((new, lambda))
    }

    #[track_caller]
    pub fn double_and_add_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                let (lhs_x, _lhs_y) = first.as_xy();
                let (rhs_x, _rhs_y) = second.as_xy();
                assert!(lhs_x != rhs_x, "can't add points with the same x cooridnate");
            },
            _ => {}
        }
        
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y); 
        let lambda = Fp2::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;
        
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let two_y = self.y.double(cs)?;
        let t0 = two_y.div(cs, &new_x_minus_this_x)?;
        let t1 = lambda.add(cs, &t0)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.x).add_neg_term(&new_x);
        let new_x = t1.square_with_chain(cs, chain)?;

        let new_x_minus_x= new_x.sub(cs, &self.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.y);
        let new_y = Fp2::mul_with_chain(cs, &t1, &new_x_minus_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.double();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok(new)
    }

    pub fn sub_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp2::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.sub_unequal_unchecked(cs, other)
    }

    pub fn sub_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let (res, _slope) = self.sub_unequal_unchecked_and_return_slope(cs, other)?;
        Ok(res)
    }

    #[track_caller]
    pub fn sub_unequal_unchecked_and_return_slope<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self
    ) -> Result<(Self, Fp2<'a, E, F, T>), SynthesisError> 
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                let (lhs_x, _lhs_y) = first.as_xy();
                let (rhs_x, _rhs_y) = second.as_xy();
                assert!(lhs_x != rhs_x, "can't add points with the same x cooridnate");
            },
            _ => {}
        }
        
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&other.y).add_pos_term(&self.y);
        let lambda = Fp2::div_with_chain(cs, chain, &other_x_minus_this_x)?;
        // lambda^2 + (-x' - x)
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * -(x - new_x) + (- y)
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.y);
        let new_y = Fp2::mul_with_chain(cs, &lambda, &new_x_minus_this_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                let mut t0 = other;
                t0.negate();
                tmp.add_assign_mixed(&t0);

                Some(tmp.into_affine())
            },
            _ => None
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok((new, lambda))
    }

    #[track_caller]
    pub fn double_and_return_slope<CS>(&self, cs: &mut CS) -> Result<(Self, Fp2<'a, E, F, T>), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let x_squared = self.x.square(cs)?;
        let mut chain = Fp2Chain::new();
        chain.add_pos_term(&x_squared).add_pos_term(&x_squared).add_pos_term(&x_squared);
        let two_y = self.y.double(cs)?;
        let lambda = Fp2::div_with_chain(cs, chain, &two_y)?;

        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        let x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = Fp2Chain::new();
        chain.add_neg_term(&self.y);
        let new_y = Fp2::mul_with_chain(cs, &lambda, &x_minus_new_x, chain)?;

        let new_value = self.get_value().map(|this| {
            let mut tmp = this.into_projective();
            tmp.double();
            tmp.into_affine()
        });

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok((new, lambda))
    }

    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let (res, _slope) = self.double_and_return_slope(cs)?;
        Ok(res)
    } 

    #[track_caller]
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let x = Fp2::conditionally_select(cs, &flag, &first.x, &second.x)?;
        let y = Fp2::conditionally_select(cs, &flag, &first.y, &second.y)?;
        let value = match (flag.get_value(), first.get_value(), second.get_value()) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };
        Ok(Self {x, y, value })
    }

    #[track_caller]
    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let x = self.x.clone();
        let y = self.y.negate(cs)?;
        let new_value = self.get_value().map(|x| {
            let mut res = x;
            res.negate();
            res
        });
        Ok(Self {x, y, value: new_value })
    }

    #[track_caller]
    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let x = self.x.clone();
        let y = self.y.conditionally_negate(cs, flag)?;
        let value = match (flag.get_value(), self.value) {
            (Some(flag), Some(x)) => {
                let mut tmp = x;
                if flag { tmp.negate() };
                Some(tmp)
            },
            _ => None,
        };
        Ok(Self {x, y, value })
    }

    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let x_check = Fp2::equals(cs, &mut this.x, &mut other.x)?;
        let y_check = Fp2::equals(cs, &mut this.y, &mut other.y)?;
        println!(" x check: {}", x_check.get_value().unwrap());
        println!(" y check: {}", y_check.get_value().unwrap());
        let equals = Boolean::and(cs, &x_check, &y_check)?;
        
        Ok(equals)
    }
}

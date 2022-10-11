use super::*;
use crate::plonk::circuit::bigint_new::*;

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

use crate::bellman::plonk::better_better_cs::cs::{
    Variable, 
    ConstraintSystem,
    ArithmeticTerm,
    MainGateTerm,
    Width4MainGateWithDNext,
    MainGate,
    GateInternal,
    Gate,
    LinearCombinationOfTerms,
    PolynomialMultiplicativeTerm,
    PolynomialInConstraint,
    TimeDilation,
    Coefficient,
    PlonkConstraintSystemParams,
    TrivialAssembly,
    PlonkCsWidth4WithNextStepParams,
};

use crate::plonk::circuit::Assignment;
use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};
use num_traits::ToPrimitive;


#[derive(Clone, Debug)]
pub struct ProjectivePoint<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    pub z: FieldElement<'a, E, G::Base>,
    pub value: Option<G>,
    pub is_in_subgroup: bool,
    pub circuit_params: &'a CurveCircuitParameters<E, G, T>
}


impl<'a, E, G, T> From<AffinePoint<'a, E, G, T>> for ProjectivePoint<'a, E, G, T>
where E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>, <G as GenericCurveAffine>::Base: PrimeField 
{
    fn from(affine_pt: AffinePoint<'a, E, G, T>) -> Self {
        let params = affine_pt.x.representation_params;
        let AffinePoint { x, y, value, is_in_subgroup, circuit_params} = affine_pt;

        ProjectivePoint::<E, G, T> {
            x, y,
            z: FieldElement::one(&params),
            value: value,
            is_in_subgroup,
            circuit_params
        }
    }    
}


impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> ProjectivePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    pub fn get_z(&self) -> FieldElement<'a, E, G::Base> {
        self.z.clone()
    }

    pub fn from_coordinates_unchecked(
        x: FieldElement<'a, E, G::Base>, y: FieldElement<'a, E, G::Base>, z: FieldElement<'a, E, G::Base>,
        is_in_subgroup: bool, circuit_params: &'a CurveCircuitParameters<E, G, T>
    ) -> Self {
        let value = match (x.get_field_value(), y.get_field_value(), z.get_field_value()) {
            (Some(mut x), Some(mut y), Some(z)) => {
                let res = if z.is_zero() { 
                    G::zero()
                } else {
                    let z_inv = z.inverse().unwrap();
                    x.mul_assign(&z_inv);
                    x.mul_assign(&z_inv);
                    y.mul_assign(&z_inv);
                    y.mul_assign(&z_inv);
                    y.mul_assign(&z_inv);
                    G::from_xy_checked(x, y).expect("should be a valid point")
                };
                Some(res)
            },
            _ => None,
        };

        Self { x, y, z, value, is_in_subgroup, circuit_params }
    }

    #[track_caller]
    pub fn enforce_if_on_curve<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a: u64 = fe_to_biguint(&G::a_coeff()).to_u64().expect("G::a_ceoff should fit into u64");
        let b: u64 = fe_to_biguint(&G::b_coeff()).to_u64().expect("G::a_ceoff should fit into u64");

        // Y^2 * Z = X^3 + a * X * Z^2 + b * Z^3
        let mut lhs = self.y.square(cs)?;
        lhs = lhs.mul(cs, &self.z)?;

        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let z_squared = self.z.square(cs)?;
        let z_mul_b = self.z.scale(cs, b)?;
        let mut rhs = z_squared.mul(cs, &z_mul_b)?;

        rhs = rhs.add(cs, &x_cubed)?;
        if a != 0 {
            let x_mul_a = self.x.scale(cs, a)?;
            let tmp = z_squared.mul(cs, &x_mul_a)?;
            rhs = rhs.add(cs, &tmp)?
        };
        FieldElement::enforce_equal(cs, &mut lhs, &mut rhs)
    }

    #[track_caller]
    pub fn enforce_equal<CS>(cs: &mut CS, left: &mut Self, right: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // we should check that x2 = t * x1; y2 = t * y1; z2 = t * z1 for some scalar t
        let mut t_wit = None;
        let rns_params = &left.circuit_params.base_field_rns_params;
        
        for (cand1, cand2) in [&left.x, &left.y, &left.z].iter().zip([&right.x, &right.y, &right.z].iter()) {
            if cand2.get_field_value().is_some() && !cand1.get_field_value().unwrap_or(G::Base::zero()).is_zero() {
                let res = cand1.get_field_value().unwrap();
                let mut res_inversed = res.inverse().unwrap();
                res_inversed.mul_assign(&cand2.get_field_value().unwrap());
                t_wit = Some(res_inversed);
                break;
            };
        }
        let t = FieldElement::alloc(cs, t_wit, rns_params)?;

        for (a, b) in [&left.x, &left.y, &left.z].iter().zip([&right.x, &right.y, &right.z].iter()) {
            let mut lhs = FieldElement::mul(&a, cs, &t)?;
            let mut rhs : FieldElement<E, G::Base> = (*b).clone();
            FieldElement::enforce_equal(cs, &mut lhs, &mut rhs)?;
        }
        
        Ok(())
    }

    pub fn zero(params: &'a CurveCircuitParameters<E, G, T>) -> Self
    {
        let rns_params = &params.base_field_rns_params;
        let x = FieldElement::zero(rns_params);
        let y = FieldElement::one(rns_params);
        let z = FieldElement::zero(rns_params);
        let value = Some(G::zero());

        Self { x, y, z, value, is_in_subgroup: true, circuit_params: params }
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant() & self.z.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value.clone()
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let y_negated = self.y.negate(cs)?;
        let new_value = self.value.map(|el| {
            let mut t = el;
            t.negate();
            t
        });
   
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            z: self.z.clone(),
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };

        Ok(new)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let y_negated = self.y.conditionally_negate(cs, flag)?;
        let new_value = match (self.value, flag.get_value()) {
            (Some(val), Some(flag)) => { 
                let mut t = val;
                if flag { t.negate() };
                Some(t)
            },
            _ => None,
        };
       
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            z: self.z.clone(),
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };

        Ok(new)
    }

    pub unsafe fn convert_to_affine<CS>(&self, cs: &mut CS) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let x = self.x.div(cs, &self.z)?;
        let y = self.y.div(cs, &self.z)?;
        let value = self.get_value();

        Ok(AffinePoint { x, y, value, is_in_subgroup: self.is_in_subgroup, circuit_params: self.circuit_params })
    }

    pub fn convert_to_affine_or_default<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, default: &AffinePoint<'a, E, G, T>
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        let params = self.x.representation_params;
        let is_point_at_infty = FieldElement::is_zero(&mut self.z, cs)?;
        let safe_z = FieldElement::conditionally_select(
            cs, &is_point_at_infty, &FieldElement::one(params), &self.z
        )?;
        let x_for_safe_z = self.x.div(cs, &safe_z)?;
        let y_for_safe_z = self.y.div(cs, &safe_z)?;
        let x = FieldElement::conditionally_select(cs, &is_point_at_infty, &default.x, &x_for_safe_z)?;
        let x = x_for_safe_z;
        let y = FieldElement::conditionally_select(cs, &is_point_at_infty, &default.y, &y_for_safe_z)?;

        let value = match (is_point_at_infty.get_value(), self.get_value(), AffinePoint::get_value(&default)) {
            (Some(true), _, Some(val)) | (Some(false), Some(val), _) => Some(val),
            _ => None,
        };

        let is_in_subgroup = self.is_in_subgroup;
        let new = AffinePoint { x, y, value, is_in_subgroup, circuit_params: self.circuit_params };
        Ok((new, is_point_at_infty))
    }

    #[track_caller]
    fn add_sub_impl<CS>(&self, cs: &mut CS, other: &Self, is_subtraction: bool) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // this formula is only valid for curve of prime order with zero j-ivariant
        let params = self.circuit_params;
        assert!(G::a_coeff().is_zero());
        assert!(params.is_prime_order_curve);

        let curve_b: u64 = fe_to_biguint(&G::b_coeff()).to_u64().expect("G::b_ceoff should fit into u64");
        let curve_b3 = curve_b * 3;

        let x1 = self.x.clone();
        let y1 = self.y.clone();
        let z1 = self.z.clone();

        let x2 = other.x.clone();
        let y2 = other.y.clone();
        let gate_count_start = cs.get_current_step_number();
        let y2 = if is_subtraction { y2.negate(cs)? } else { y2 };
        let gate_count_end = cs.get_current_step_number();
        assert_eq!(gate_count_end - gate_count_start, 0);
        let z2 = other.z.clone();

        // t0 = x1 * x2
        let t0 = x1.mul(cs, &x2)?; 
        // t1 = y1 * y2 
        let t1 = y1.mul(cs, &y2)?; 
        // t2 = z1 * z2
        let t2 = z1.mul(cs, &z2)?;
        // a1 = x1 + y1
        let a1 = x1.add(cs, &y1)?;
        // a2 = x2 + y2
        let a2 = x2.add(cs, &y2)?;
        // t3 = a1 * a2 - t0 - t1 
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&t0).add_neg_term(&t1);
        let t3 = FieldElement::mul_with_chain(cs, &a1, &a2, chain)?;
        // t4 = y1 + z1
        let t4 = y1.add(cs, &z1)?;
        // x3 = y2 + z2 
        let x3 = y2.add(cs, &z2)?;
        // t4 = t4 * x3 - t1 - t2 
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&t1).add_neg_term(&t2);
        let t4 = FieldElement::mul_with_chain(cs, &t4, &x3, chain)?;
        // a3 = x1 + z1
        let a3 = x1.add(cs, &z1)?;
        // a4 = x2 + z2
        let a4 = x2.add(cs, &z2)?;
        // y3 = a3 * a4 - t0 - t2
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&t0).add_neg_term(&t2);
        let y3 = FieldElement::mul_with_chain(cs, &a3, &a4, chain)?;
        // t2 = b3 * z1 * z2
        let b3_mul_z1 = z1.scale(cs, curve_b3)?;
        let t2 = b3_mul_z1.mul(cs, &z2)?;
        // z3 = t1 + t2
        let z3 = t1.add(cs, &t2)?;
        // t1 = t1 - t2
        let t1 = t1.sub(cs, &t2)?;  
        // x3 = t4 * b3 * y3
        let b3_mul_y3 = y3.scale(cs, curve_b3)?;
        let x3 = b3_mul_y3.mul(cs, &t4)?;
        // x3 = t3 * t1 - x3
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&x3);
        let x3 = FieldElement::mul_with_chain(cs, &t1, &t3, chain)?;
        // y3 = (b3 * y3) * (3 * t0)
        let t0_mul_3 = t0.scale(cs, 3)?;
        let y3 = b3_mul_y3.mul(cs, &t0_mul_3)?; 
        // y3 = t1 * z3  + y3
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&y3);
        let y3 = FieldElement::mul_with_chain(cs, &t1, &z3, chain)?;
        // z3 = z3 * t4
        let z3 = z3.mul(cs, &t4)?; 
        // z3 = (3 * t0) * t3 + z3 
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&z3);
        let z3 = FieldElement::mul_with_chain(cs, &t0_mul_3, &t3, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(mut other)) => {
                let mut tmp = this.into_projective();
                if is_subtraction {
                    other.negate();
                }
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: x3, y: y3, z: z3,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    {
        self.add_sub_impl(cs, other, false)
    } 

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    {
        self.add_sub_impl(cs, other, true)
    } 

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // this formula is only valid for curve of prime order with zero j-ivariant
        let params = self.circuit_params;
        assert!(G::a_coeff().is_zero());
        assert!(params.is_prime_order_curve);

        let curve_b: u64 = fe_to_biguint(&G::b_coeff()).to_u64().expect("G::b_ceoff should fit into u64");
        let curve_b3 = curve_b * 3;

        let x = self.x.clone();
        let y = self.y.clone();
        let z = self.z.clone();

        // t0 = y * y 
        let t0 = y.square(cs)?;
        // t2 = b3 * z * z
        let b3_mul_z = z.scale(cs, curve_b3)?;
        let t2 = b3_mul_z.mul(cs, &z)?;
        // y3 = t0 + t2
        let y3 = t0.add(cs, &t2)?;
        // t1 = y * z 
        let t1 = y.mul(cs, &z)?;
        // z3 = 8 * t0 * t1
        let t0_mul_4 = t0.scale(cs, 4)?;
        let t0_mul_8 = t0_mul_4.double(cs)?;
        let z3 = t0_mul_8.mul(cs, &t1)?;
        // t4 = 4 * t0 - 3 * y3
        let y3_mul_3 = y3.scale(cs, 3)?;
        let t4 = t0_mul_4.sub(cs, &y3_mul_3)?;
        // y3 = t4 * y3
        let y3 = t4.mul(cs, &y3)?;
        // y3 = 8 * t0 * t2  + y3
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&y3);
        let y3 = FieldElement::mul_with_chain(cs, &t0_mul_8, &t2, chain)?;
        // t1 = x * y
        let t1 = x.mul(cs, &y)?; 
        // x3 = 2 * t4 * t1
        let t4_mul_2 = t4.double(cs)?;
        let x3 = t4_mul_2.mul(cs, &t1)?;

        let new_value = self.value.clone().map(|el| {
            let mut tmp = el.into_projective();
            tmp.double();
            tmp.into_affine()
        });
   
        let new = Self {
            x: x3, y: y3, z: z3,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }
   
    #[track_caller]
    fn add_sub_mixed_impl<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &AffinePoint<'a, E, G, T>, is_subtraction: bool
    ) -> Result<Self, SynthesisError>  
    {
        let params = self.circuit_params;
        assert!(G::a_coeff().is_zero());
        assert!(params.is_prime_order_curve);

        let curve_b: u64 = fe_to_biguint(&G::b_coeff()).to_u64().expect("G::b_ceoff should fit into u64");
        let curve_b3 = curve_b * 3; 

        let x1 = self.x.clone();
        let y1 = self.y.clone();
        let z1 = self.z.clone();
        
        let x2 = other.x.clone();
        let y2 = other.y.clone();
        let gate_count_start = cs.get_current_step_number();
        let y2 = if is_subtraction { y2.negate(cs)? } else { y2 };
        let gate_count_end = cs.get_current_step_number();
        assert_eq!(gate_count_end - gate_count_start, 0);

        // t4 = y2 * z1 + y1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&y1);
        let t4 = FieldElement::mul_with_chain(cs, &y2, &z1, chain)?;
        // y3 = x2 * z1 + x1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&x1);
        let y3 = FieldElement::mul_with_chain(cs, &x2, &z1, chain)?;
        // z3 = y1 * y2 + b3 * z1
        let z1_mul_b3 = z1.scale(cs, curve_b3)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&z1_mul_b3);
        let z3 = FieldElement::mul_with_chain(cs, &y1, &y2, chain)?;
        // t0 = x1 * x2
        let t0 = x1.mul(cs, &x2)?;
        // t3 = (x2 + y2) * (x1 + y1) - t0 - z3 + b3 * z1
        let a = x2.add(cs, &y2)?;
        let b = x1.add(cs, &y1)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&z1_mul_b3).add_neg_term(&t0).add_neg_term(&z3);
        let t3 = FieldElement::mul_with_chain(cs, &a, &b, chain)?;
        // x3 = t4 * b3 * y3
        let y3_mul_b3 = y3.scale(cs, curve_b3)?;
        let x3 = t4.mul(cs, &y3_mul_b3)?;
        // t1 = z3 - 2 * b3 * z1
        let z1_mul_2_b3 = z1.scale(cs, 2 * curve_b3)?;
        let t1 = z3.sub(cs, &z1_mul_2_b3)?;
        // x3 = t3 * t1 - x3
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&x3);
        let x3 = FieldElement::mul_with_chain(cs, &t1, &t3, chain)?;
        // y3 = (b3 * y3) * (3 * t0)
        let t0_mul_3 = t0.scale(cs, 3)?;
        let y3 = y3_mul_b3.mul(cs, &t0_mul_3)?; 
        // y3 = t1 * z3  + y3 
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&y3);
        let y3 = FieldElement::mul_with_chain(cs, &t1, &z3, chain)?;
        // t0 = (3 * t0) * t3
        let t0 = t0_mul_3.mul(cs, &t3)?;
        // z3 = z3 * t4 + t0
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&t0);
        let z3 = FieldElement::mul_with_chain(cs, &t4, &z3, chain)?;

        let new_value = match (self.value, other.get_value()) {
            (Some(this), Some(mut other)) => {
                let mut tmp = this.into_projective();
                if is_subtraction {
                    other.negate();
                }
                tmp.add_assign_mixed(&other);
                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: x3, y: y3, z: z3,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup && other.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }

    pub fn add_mixed<CS>(&self, cs: &mut CS, other: &AffinePoint<'a, E, G, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        self.add_sub_mixed_impl(cs, other, false)
    } 

    pub fn sub_mixed<CS>(&self, cs: &mut CS, other: &AffinePoint<'a, E, G, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        self.add_sub_mixed_impl(cs, &other, true)
    } 

    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {

        let first_value = first.value;
        let second_value = second.value;
        let x = FieldElement::conditionally_select(cs, flag, &first.x, &second.x)?;
        let y = FieldElement::conditionally_select(cs, flag, &first.y, &second.y)?;
        let z = FieldElement::conditionally_select(cs, flag, &first.z, &second.z)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };

        let is_in_subgroup = first.is_in_subgroup && second.is_in_subgroup;
        let circuit_params = first.circuit_params;
        let selected = Self { x, y, z, value, is_in_subgroup, circuit_params };
        Ok(selected)
    }
}



    
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
use crate::plonk::circuit::hashes_with_tables::utils::{IdentifyFirstLast, u64_to_ff};

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use super::super::boolean::{Boolean, AllocatedBit};

use num_bigint::BigUint;
use num_integer::Integer;

use crate::plonk::circuit::bigint_new::*;
use crate::plonk::circuit::curve_new::sw_projective::*;


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PointByScalarMulStrategy {
    Basic,
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurveCircuitParameters<E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub base_field_rns_params: RnsParameters<E, G::Base>,
    pub scalar_field_rns_params: RnsParameters<E, G::Scalar>,
    pub is_prime_order_curve: bool,
    pub point_by_scalar_mul_strategy: PointByScalarMulStrategy,

    // this generator is used for scalar multiplication
    // Sage script to find generator for quadratic extension (taking BN256 curve as an example):
    // q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
    // Fq = GF(q)
    // R.<x> = Fq[] 
    // Fq2 = Fq.extension(x^2+1,'u')
    // Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    // B = 3
    // print Fq2.cardinality() == q^2
    // curve = EllipticCurve(Fq2, [0,3])
    // point = curve.random_point()
    // for j in xrange(0, 256):
    //     print point
    //     point = 2 * point

    fp2_generator_x_c0: G::Base,
    fp2_generator_x_c1: G::Base,
    fp2_generator_y_c0: G::Base,
    fp2_generator_y_c1: G::Base,
    
    _marker: std::marker::PhantomData<T>

    // parameters related to endomorphism:
    // decomposition of scalar k as k = k1 + \lambda * k2 
    // where multiplication by \lambda transorms affine point P=(x, y) into Q=(\beta * x, -y)
    // scalars k1 and k2 have bitlength twice shorter than k
    // a1, b1, a2, b2 are auxiliary parameters dependent only on the curve, which are used actual decomposition
    // see "Guide to Elliptic Curve Cryptography" algorithm  3.74 for reference
    // pub lambda: E::Fr,
    // pub beta: E::Fq,
    // pub a1: BigUint,
    // pub a2: BigUint,
    // pub minus_b1: BigUint,
    // pub b2: BigUint,
}

use crate::bellman::pairing::bn256::Bn256;
type Bn256CircuitParameters<E> = CurveCircuitParameters<E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>; 
pub fn generate_optimal_circuit_params_for_bn256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, base_field_limb_size: usize, scalar_field_limb_size: usize
) -> Bn256CircuitParameters<E>
{
    type Fq = <<Bn256 as Engine>::G1Affine as GenericCurveAffine>::Base;
    type Fr = <<Bn256 as Engine>::G1Affine as GenericCurveAffine>::Scalar;

    let fp2_generator_x_c0 = Fq::from_str(
        "17121668968360376440073452595519517444769132227617365077403755834749278043815"
    ).expect("should parse");
    let fp2_generator_x_c1 = Fq::from_str(
        "419498279616971835019397848440367748195944242286251665483842484997631036276"
    ).expect("should parse");
    let fp2_generator_y_c0 = Fq::from_str(
        "15700638644566209537916323943619823104238275494394006479723875651809222746581"
    ).expect("should parse");
    let fp2_generator_y_c1 = Fq::from_str(
        "11945101449646283729085354065658026304542755875752930267052478828467356003660"
    ).expect("should parse");

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        point_by_scalar_mul_strategy: PointByScalarMulStrategy::Basic,
        fp2_generator_x_c0,
        fp2_generator_x_c1,
        fp2_generator_y_c0,
        fp2_generator_y_c1,
        _marker: std::marker::PhantomData::<Bn256Extension2Params>
    }
}


#[derive(Clone, Debug)]
pub struct AffinePoint<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    // the used paradigm is zero abstraction: we won't pay for this flag if it is never used and 
    // all our points are regular (i.e. not points at infinity)
    // for this purpose we introduce lazy_select
    // if current point is actually a point at infinity than x, y may contain any values and are actually meaningless
    //pub is_infinity: Boolean,
    pub value: Option<G>,
    // true if we have already checked that point is in subgroup
    pub is_in_subgroup: bool,
    pub circuit_params: &'a CurveCircuitParameters<E, G, T>,
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<G>, params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<Self, SynthesisError> {
        let (new, _x_decomposition, _y_decomposition) = Self::alloc_ext(cs, value, params, true)?;
        Ok(new)
    }

    // allocation without checking that point is indeed on curve and in the right subgroup
    #[track_caller]
    pub fn alloc_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<G>, params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<Self, SynthesisError> {
        let (new, _x_decomposition, _y_decomposition) = Self::alloc_ext(cs, value, params, false)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<G>, params: &'a CurveCircuitParameters<E, G, T>, require_checks: bool
    ) -> Result<(Self, RangeCheckDecomposition<E>, RangeCheckDecomposition<E>), SynthesisError>  {
        let (x, y) = match value {
            Some(v) => {
                assert!(!v.is_zero());
                let (x, y) = v.into_xy_unchecked();
                (Some(x), Some(y))
            },
            None => {
                (None, None)
            }
        };

        let (x, x_decomposition) = FieldElement::alloc_ext(cs, x, &params.base_field_rns_params)?;
        let (y, y_decomposition) = FieldElement::alloc_ext(cs, y, &params.base_field_rns_params)?;
        let is_in_subgroup = params.is_prime_order_curve;
        let circuit_params = params;
        let mut new = Self { x, y, value, is_in_subgroup, circuit_params};

        if require_checks {
            new.enforce_if_on_curve(cs)?;
            new.enforce_if_in_subgroup(cs)?;
        }
        new.is_in_subgroup |= require_checks;
        
        Ok((new, x_decomposition, y_decomposition))
    }

    pub unsafe fn from_xy_unchecked(
        x: FieldElement<'a, E, G::Base>,
        y: FieldElement<'a, E, G::Base>,
        params: &'a CurveCircuitParameters<E, G, T>,
    ) -> Self {
        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_unchecked(x, y))
            },
            _ => {
                None
            }
        };

        let new = Self {x, y, value, is_in_subgroup: params.is_prime_order_curve, circuit_params: params };
        new
    }

    pub fn constant(value: G, params: &'a CurveCircuitParameters<E, G, T>) -> Self {
        assert!(!value.is_zero());
        let is_in_subgroup = {
            let scalar = G::Scalar::char();
            let mut point = value.into_projective();
            point.mul_assign(scalar);
            point.is_zero() 
        };
        let (x, y) = value.into_xy_unchecked();
        let x = FieldElement::constant(x, &params.base_field_rns_params);
        let y = FieldElement::constant(y, &params.base_field_rns_params);
        let new = Self { x, y, value: Some(value), is_in_subgroup, circuit_params: params };

        new
    }

    pub fn get_raw_limbs_representation<CS>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> 
    where CS: ConstraintSystem<E> {
        let mut res = self.x.get_raw_limbs_representation(cs)?;
        let extension = self.y.get_raw_limbs_representation(cs)?;
        res.extend_from_slice(&extension[..]);
        Ok(res)
    }
    
    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.x.normalize(cs)?;
        self.y.normalize(cs)
    }

    pub fn enforce_if_normalized<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.x.enforce_if_normalized(cs)?;
        self.y.enforce_if_normalized(cs)
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
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };

        Ok(new)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let y_negated = self.y.conditionally_negate(cs, flag)?;
        let new_value = self.value.map(|x| {
            let mut tmp = x;
            tmp.negate();
            tmp
        });
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };

        Ok(new)
    }

    pub fn select<CS>(cs: &mut CS, flag: &Boolean, first: &Self, second: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
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
        let is_in_subgroup = first.is_in_subgroup && second.is_in_subgroup;
        let selected = AffinePoint { x, y, value, is_in_subgroup, circuit_params: first.circuit_params };

        Ok(selected)
    }

    #[track_caller]
    pub fn enforce_if_on_curve<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let params = &self.x.representation_params;
        let a = FieldElement::constant(G::a_coeff(), params);
        let b = FieldElement::constant(G::b_coeff(), params);

        let mut lhs = self.y.square(cs)?;
        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let mut rhs = if a.get_field_value().unwrap().is_zero() {
            x_cubed.add(cs, &b)?
        } else {
            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&x_cubed).add_pos_term(&b);
            FieldElement::mul_with_chain(cs, &self.x, &a, chain)?
        };

        FieldElement::enforce_equal(cs, &mut lhs, &mut rhs)
    }

    #[track_caller]
    pub fn enforce_if_in_subgroup<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> Result<(), SynthesisError> {
        if !self.circuit_params.is_prime_order_curve {
            // mul_by_scalar_for_composite_order_curve<CS: ConstraintSystem<E>>(
            //     &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
            return Ok(())
        }
        Ok(())
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
    pub fn add_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal");
            },
            _ => {}
        }
        // since we are in a circuit we don't use projective coodinates: inversions are "cheap" in terms of constraints 
        // we also do not want to have branching here, so this function implicitly requires that points are not equal
        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;
        
        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);
                Some(tmp.into_affine())
            },
            _ => None
        };
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup || other.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
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
    pub fn sub_unequal_unchecked<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal");
            },
            _ => {}
        }

        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_pos_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * -(x - new_x) + (- y)
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &new_x_minus_this_x, chain)?;

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
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup || other.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // this formula is only valid for curve with zero j-ivariant
        assert!(G::a_coeff().is_zero());

        let x_squared = self.x.square(cs)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&x_squared).add_pos_term(&x_squared).add_pos_term(&x_squared);
        let two_y = self.y.double(cs)?;
        let lambda = FieldElement::div_with_chain(cs, chain, &two_y)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        let x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &x_minus_new_x, chain)?;

        let new_value = self.get_value().map(|this| {
            let mut tmp = this.into_projective();
            tmp.double();
            tmp.into_affine()
        });
        
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }

    // doubles self and adds other
    #[track_caller]
    pub fn double_and_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better
        // we can also try https://eprint.iacr.org/2015/1060.pdf
        // only check that x - x' != 0 and go into the unchecked routine
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.double_and_add_unchecked(cs, &other)
    }

    #[track_caller]
    pub fn double_and_add_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y); 
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;
        
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let two_y = self.y.double(cs)?;
        let t0 = two_y.div(cs, &new_x_minus_this_x)?;
        let t1 = lambda.add(cs, &t0)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&new_x);
        let new_x = t1.square_with_chain(cs, chain)?;

        let new_x_minus_x= new_x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &t1, &new_x_minus_x, chain)?;

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
   
        let new = Self {
            x: new_x,
            y: new_y,
            value: new_value,
            is_in_subgroup: self.is_in_subgroup || other.is_in_subgroup,
            circuit_params: self.circuit_params
        };
        Ok(new)
    }
}


// this is ugly and should be rewritten, but OK for initial draft
// it defines elliptic point over Extension Field
#[derive(Clone, Debug)]
pub struct AffinePointExt<'a, E: Engine,  G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField {
    x: Fp2<'a, E, G::Base, T>,
    y: Fp2<'a, E, G::Base, T>,
}

use std::convert::From;

impl<'a, E: Engine, G: GenericCurveAffine, T> From<AffinePoint<'a, E, G, T>> for AffinePointExt<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<<G as GenericCurveAffine>::Base>
{
    fn from(item: AffinePoint<'a, E, G, T>) -> Self {
        AffinePointExt::<E, G, T> {
            x: Fp2::from_base_field(item.get_x()),
            y: Fp2::from_base_field(item.get_y())
        } 
    }
}


impl<'a, E: Engine, G: GenericCurveAffine, T> AffinePointExt<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<<G as GenericCurveAffine>::Base> {
    pub fn get_x(&self) -> Fp2<'a, E, G::Base, T> {
        self.x.clone()
    }

    pub fn get_y(&self) -> Fp2<'a, E, G::Base, T> {
        self.y.clone()
    }

    #[track_caller]
    pub fn constant(
        x0: G::Base, x1: G::Base, y0: G::Base, y1: G::Base, params: &'a CurveCircuitParameters<E, G, T>
    ) -> Self {
        let rns_params = &params.base_field_rns_params;
        let x = Fp2::constant(x0, x1, rns_params);
        let y = Fp2::constant(y0, y1, rns_params);
        AffinePointExt::<E, G, T> { x, y }
    }

    #[track_caller]
    pub fn add_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
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

        let new = Self { x: new_x, y: new_y };
        Ok(new)
    }

    #[track_caller]
    pub fn double_and_add_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
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

        let new = Self { x: new_x, y: new_y };
        Ok(new)
    }

    #[track_caller]
    pub fn sub_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
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

        let new = Self { x: new_x, y: new_y};
        Ok(new)
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
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

        let new = Self { x: new_x, y: new_y };
        Ok(new)
    }
}


// we are particularly interested in three curves: secp256k1, bn256 and bls12-281
// unfortunately, only bls12-381 has a cofactor
impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    #[track_caller]
    pub fn mul_by_scalar_for_composite_order_curve<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }
        
        let circuit_params = self.circuit_params;
        let entries = scalar.decompose_into_skewed_representation(cs)?;
       
        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"
        let offset_generator = AffinePointExt::constant(
            circuit_params.fp2_generator_x_c0, circuit_params.fp2_generator_x_c1,
            circuit_params.fp2_generator_y_c0, circuit_params.fp2_generator_y_c1,
            circuit_params
        );
        let mut acc = offset_generator.add_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];
        let mut num_doubles = 0;

        let x = self.x.clone();
        let mut minus_y = self.y.negate(cs)?;
        minus_y.reduce(cs)?;

        for e in entries_without_first_and_last.iter() {
            let selected_y = FieldElement::conditionally_select(cs, e, &minus_y, &self.y)?;  
            let t_value = match (self.value, e.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }
                    Some(val)
                },
                _ => None
            };
            let t = Self {
                x: x.clone(),
                y: selected_y,
                value: t_value,
                is_in_subgroup: self.is_in_subgroup,
                circuit_params
            };

            acc = acc.double_and_add_unchecked(cs, &t.into())?;
            num_doubles += 1;
        }

        let mut scaled_offset = offset_generator.clone();
        for _ in 0..num_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        acc = acc.sub_unequal_unchecked(cs, &mut scaled_offset)?;

        let with_skew = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;
        let flag = entries.first().unwrap();
        let final_x = FieldElement::conditionally_select(cs, flag, &with_skew.x.c0, &acc.x.c0)?;
        let final_y = FieldElement::conditionally_select(cs, flag, &with_skew.y.c0, &acc.y.c0)?;

        let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        }); 

       let result = AffinePoint { 
            x: final_x, 
            y: final_y, 
            value: final_value, 
            is_in_subgroup: self.is_in_subgroup, 
            circuit_params: self.circuit_params 
        };
        Ok(result)
    }
}


impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField {
    pub fn mul_by_scalar_for_prime_order_curve<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        let params = self.circuit_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs)?;

        // TODO: use standard double-add algorithm for now, optimize later
        let mut acc = ProjectivePoint::<E, G, T>::zero(params);
        let mut tmp : AffinePoint<E, G, T> = self.clone();

        for bit in scalar_decomposition.into_iter() {
            let added = acc.add_mixed(cs, &mut tmp)?;
            acc = ProjectivePoint::conditionally_select(cs, &bit, &added, &acc)?;
            tmp = AffinePoint::double(&tmp, cs)?;
        }
        
        Ok(acc)
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};
    use plonk::circuit::Width4WithCustomGates;
    use bellman::plonk::better_better_cs::gates::{selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self};
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;

    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
    use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
    use crate::bellman::plonk::better_better_cs::verifier::verify;

    #[test]
    fn test_arithmetic_for_bn256_curve() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
        let mut rng = rand::thread_rng();

        let a: G1Affine = rng.gen();
        let b: G1Affine = rng.gen();
        let mut tmp = a.into_projective();
        tmp.add_assign_mixed(&b);
        let result = tmp.into_affine();
        
        let a = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
        let mut b = AffinePoint::alloc(&mut cs, Some(b), &params).unwrap();
        let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
        let naive_mul_start = cs.get_current_step_number();
        let mut result = a.add_unequal_unchecked(&mut cs, &mut b).unwrap();
        let naive_mul_end = cs.get_current_step_number();
        println!("num of gates: {}", naive_mul_end - naive_mul_start);

        // println!("actual result: x: {}, y: {}", actual_result.x.get_field_value().unwrap(), actual_result.y.get_field_value().unwrap());
        // println!("computed result: x: {}, y: {}", result.x.get_field_value().unwrap(), result.y.get_field_value().unwrap());

        AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
        assert!(cs.is_satisfied()); 
        println!("SCALAR MULTIPLICATION final");
    }

    struct TestCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>,
        use_projective: bool
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestCircuit<E, G, T> 
    where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
    {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }
    
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            inscribe_default_bitop_range_table(cs).unwrap();
            let mut rng = rand::thread_rng();

            let a: G = rng.gen();
            let scalar : G::Scalar = rng.gen();
            let mut tmp = a.into_projective();
            tmp.mul_assign(scalar);
            let result = tmp.into_affine();
            
            let mut a = AffinePoint::alloc(cs, Some(a), &self.circuit_params)?;
            let mut scalar = FieldElement::alloc(cs, Some(scalar), &self.circuit_params.scalar_field_rns_params)?;
            let mut actual_result = AffinePoint::alloc(cs, Some(result), &self.circuit_params)?;
            let naive_mul_start = cs.get_current_step_number();
            let result = a.mul_by_scalar_for_prime_order_curve(cs, &mut scalar)?;
            let mut result = unsafe { result.convert_to_affine(cs)? };
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)
        }
    }

    #[test]
    fn test_scalar_multiplication_for_bn256() {
        const USE_PROJECTIVE: bool = true;
        const LIMB_SIZE: usize = 80;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestCircuit { circuit_params, use_projective: USE_PROJECTIVE };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }

    // #[test]
    // fn test_arithmetic_for_secp256k1_curve() {
    //     use super::super::secp256k1::fq::Fq as SecpFq;
    //     use super::super::secp256k1::fr::Fr as SecpFr;
    //     use super::super::secp256k1::PointAffine as SecpG1;

    //     struct TestCircuit<E:Engine>{
    //         _marker: std::marker::PhantomData<E>
    //     }
    
    //     impl<E: Engine> Circuit<E> for TestCircuit<E> {
    //         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
    //         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
    //             Ok(
    //                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
    //             )
    //         }
    
    //         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
    //             inscribe_default_bitop_range_table(cs).unwrap();
    //             let params = RnsParameters::<E, SecpFq>::new_optimal(cs, 64usize);
    //             let scalar_params = RnsParameters::<E, SecpFr>::new_optimal(cs, 64usize);
    //             let mut rng = rand::thread_rng();

    //             let a: SecpG1 = rng.gen();
    //             let scalar : SecpFr = rng.gen();
    //             let mut tmp = a.into_projective();
    //             tmp.mul_assign(scalar);
    //             let result = tmp.into_affine();
                
    //             let mut a = AffinePoint::alloc(cs, Some(a), &params)?;
    //             let mut scalar = FieldElement::alloc(cs, Some(scalar), &scalar_params)?;
    //             let mut actual_result = AffinePoint::alloc(cs, Some(result), &params)?;
    //             let naive_mul_start = cs.get_current_step_number();
    //             let mut result = a.mul_by_scalar_for_prime_order_curve(cs, &mut scalar)?;
    //             let mut result = unsafe { result.convert_to_affine(cs)? };
    //             let naive_mul_end = cs.get_current_step_number();
    //             println!("num of gates: {}", naive_mul_end - naive_mul_start);
    //             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)
    //         }
    //     }

    //     use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    //     use crate::bellman::worker::Worker;
    //     use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
    //     use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
    //     use crate::bellman::plonk::better_better_cs::verifier::verify;
      
    //     let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
    //     inscribe_default_bitop_range_table(&mut cs).unwrap();
    //     let circuit = TestCircuit::<Bn256> {_marker: std::marker::PhantomData};
    //     circuit.synthesize(&mut cs).expect("must work");
    //     cs.finalize();
    //     assert!(cs.is_satisfied()); 
    //     let worker = Worker::new();
    //     let setup_size = cs.n().next_power_of_two();
    //     let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(setup_size, &worker);
    //     let setup = cs.create_setup::<TestCircuit::<Bn256>>(&worker).unwrap();
    //     let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();
        
    //     let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
    //     inscribe_default_bitop_range_table(&mut cs).unwrap();
    //     let circuit = TestCircuit::<Bn256> {_marker: std::marker::PhantomData};
    //     circuit.synthesize(&mut cs).expect("must work");
    //     cs.finalize();
    //     assert!(cs.is_satisfied()); 
    //     let proof = cs.create_proof::<_, RollingKeccakTranscript<Fr>>(&worker, &setup, &crs, None).unwrap();
    //     let valid = verify::<_, _, RollingKeccakTranscript<Fr>>(&vk, &proof, None).unwrap();
    //     assert!(valid);
    // }
}



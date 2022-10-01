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

use bellman::CurveAffine;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{Zero, One};
use std::str::FromStr;

use crate::plonk::circuit::bigint_new::*;
use crate::plonk::circuit::curve_new::sw_projective::*;
use super::point_selection_tree::*;


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PointByScalarMulStrategy {
    Basic,
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScalarDecomposition {
    pub k1_is_negative: bool,
    pub k2_is_negative: bool,
    pub k1_modulus: BigUint,
    pub k2_modulus: BigUint
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurveCircuitParameters<E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    pub base_field_rns_params: RnsParameters<E, G::Base>,
    pub scalar_field_rns_params: RnsParameters<E, G::Scalar>,
    pub is_prime_order_curve: bool,
    pub point_by_scalar_mul_strategy: PointByScalarMulStrategy,

    fp2_offset_generator_x_c0: G::Base,
    fp2_offset_generator_x_c1: G::Base,
    fp2_offset_generator_y_c0: G::Base,
    fp2_offset_generator_y_c1: G::Base,

    fp2_pt_ord3_x_c0: G::Base,
    fp2_pt_ord3_x_c1: G::Base,
    fp2_pt_ord3_y_c0: G::Base,
    fp2_pt_ord3_y_c1: G::Base,
    
    _marker: std::marker::PhantomData<T>,

    // parameters related to endomorphism:
    // decomposition of scalar k as k = k1 + \lambda * k2 
    // where multiplication by \lambda transorms affine point P=(x, y) into Q=(\beta * x, -y)
    // scalars k1 and k2 have bitlength twice shorter than k
    // a1, b1, a2, b2 are auxiliary parameters dependent only on the curve, which are used actual decomposition
    // see "Guide to Elliptic Curve Cryptography" algorithm  3.74 for reference
    pub lambda: G::Scalar,
    pub beta: G::Base,
    pub a1: BigUint,
    pub a2: BigUint,
    pub minus_b1: BigUint,
    pub b2: BigUint,
}

impl<E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> CurveCircuitParameters<E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField {
    fn rounded_div(dividend: BigUint, divisor: BigUint) -> BigUint {
        (dividend + (divisor.clone() >> 1)) / divisor
    }

    pub fn get_endomorphism_bitlen_limit(&self) -> usize {
        // https://www.iacr.org/archive/crypto2001/21390189.pdf, lemma2:
        // The vector u = (k1, k2), has norm at most max(||v1||, ||v2||), where 
        // v1 = (a1, b1), v2 = (a2, b2)
        let v1_squared_norm = self.a1.clone() * self.a1.clone() + self.minus_b1.clone() * self.minus_b1.clone();
        let v2_squared_norm = self.a2.clone() * self.a2.clone() + self.b2.clone() * self.b2.clone();
        let max_squared_norm = BigUint::max(v1_squared_norm, v2_squared_norm);
        let limit = (max_squared_norm.bits() / 2) as usize;
        limit
    }

    pub fn calculate_decomposition(&self, num: G::Scalar) -> ScalarDecomposition {
        // Compute c1 = |b2 * k/n| and c2 = |−b1 * k/n|.
        // Compute k1 = k − c1 * a1 −c2 * a2 and k2 = −c1 * b1 − c2 * b2
        let n = repr_to_biguint::<G::Scalar>(&G::Scalar::char());
        let k = fe_to_biguint(&num);
        let limit = self.get_endomorphism_bitlen_limit();

        let c1 = Self::rounded_div(k.clone() * self.b2.clone(), n.clone()); 
        let c2 = Self::rounded_div(k.clone() * self.minus_b1.clone(), n.clone());

        let a1_as_fe = biguint_to_fe::<G::Scalar>(self.a1.clone());
        let a2_as_fe = biguint_to_fe::<G::Scalar>(self.a2.clone());
        let minus_b1_as_fe = biguint_to_fe::<G::Scalar>(self.minus_b1.clone());
        let b2_as_fe = biguint_to_fe::<G::Scalar>(self.b2.clone());
        let c1_as_fe = biguint_to_fe::<G::Scalar>(c1);
        let c2_as_fe = biguint_to_fe::<G::Scalar>(c2);

        let k1 = {
            let mut tmp0 = c1_as_fe.clone();
            tmp0.mul_assign(&a1_as_fe);
            let mut tmp1 = c2_as_fe.clone();
            tmp1.mul_assign(&a2_as_fe);
            
            let mut res = num;
            res.sub_assign(&tmp0);
            res.sub_assign(&tmp1);
            res
        };
        
        let k2 = {
            let mut tmp0 = c1_as_fe.clone();
            tmp0.mul_assign(&minus_b1_as_fe);
            let mut tmp1 = c2_as_fe.clone();
            tmp1.mul_assign(&b2_as_fe);
            
            let mut res = tmp0;
            res.sub_assign(&tmp1);
            res
        };

        let mut k1 = fe_to_biguint(&k1);
        let k1_is_negative = k1.bits() as usize > limit;
        if k1_is_negative {
            k1 = n.clone() - k1;
        }

        let mut k2 = fe_to_biguint(&k2);
        let k2_is_negative = k2.bits() as usize > limit;
        if k2_is_negative {
            k2 = n.clone() - k2;
        }

        ScalarDecomposition {
            k1_is_negative,
            k2_is_negative,
            k1_modulus: k1,
            k2_modulus: k2
        }
    }
}

use crate::bellman::pairing::bn256::Bn256;
type Bn256CircuitParameters<E> = CurveCircuitParameters<E, <Bn256 as Engine>::G1Affine, Bn256Extension2Params>; 
pub fn generate_optimal_circuit_params_for_bn256<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, base_field_limb_size: usize, scalar_field_limb_size: usize
) -> Bn256CircuitParameters<E>
{
    type Fq = <<Bn256 as Engine>::G1Affine as GenericCurveAffine>::Base;
    type Fr = <<Bn256 as Engine>::G1Affine as GenericCurveAffine>::Scalar;

    let fp2_offset_generator_x_c0 = Fq::from_str(
        "16300907393763553952797146753989960732368004674693012223284497678682995867793"
    ).expect("should parse");
    let fp2_offset_generator_x_c1 = Fq::zero();
    let fp2_offset_generator_y_c0 = Fq::zero();
    let fp2_offset_generator_y_c1 = Fq::from_str(
        "18847519929951292720903138501492801907098041246451137057597277895538377195039"
    ).expect("should parse");

    let fp2_pt_ord3_x_c0 = Fq::zero();
    let fp2_pt_ord3_x_c1 = Fq::zero();
    let fp2_pt_ord3_y_c0 = Fq::zero();
    let fp2_pt_ord3_y_c1 = Fq::from_str(
        "21888242871839275217838484774961031245859103671646299620740479376884814904650"
    ).expect("should parse"); 

    let lambda = Fr::from_str(
        "21888242871839275217838484774961031246154997185409878258781734729429964517155"
    ).expect("should parse");
    let beta = Fq::from_str(
        "21888242871839275220042445260109153167277707414472061641714758635765020556616"
    ).expect("should parse");

    let a1 = BigUint::from_str("147946756881789319000765030803803410728").expect("should parse");
    let a2 = BigUint::from_str("9931322734385697763").expect("should parse");
    let minus_b1 = BigUint::from_str("9931322734385697763").expect("should parse");
    let b2 = BigUint::from_str("147946756881789319010696353538189108491").expect("should parse");

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        point_by_scalar_mul_strategy: PointByScalarMulStrategy::Basic,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        _marker: std::marker::PhantomData::<Bn256Extension2Params>
    }
}


use super::secp256k1::PointAffine as SecpPointAffine;
type Secp256K1CircuitParameters<E> = CurveCircuitParameters<E, SecpPointAffine, Secp256K1Extension2Params>; 
pub fn generate_optimal_circuit_params_for_secp256k1<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, base_field_limb_size: usize, scalar_field_limb_size: usize
) -> Secp256K1CircuitParameters<E>
{
    use super::secp256k1::fq::Fq as Fq;
    use super::secp256k1::fr::Fr as Fr;

    let fp2_offset_generator_x_c0 = Fq::from_str(
        "78054183989958579898435060651083551759218714698759530613045865018582996959238"
    ).expect("should parse");
    let fp2_offset_generator_x_c1 = Fq::zero();
    let fp2_offset_generator_y_c0 = Fq::zero();
    let fp2_offset_generator_y_c1 = Fq::from_str(
        "61858051359164228581422701657130827979253603865681507703459123009171000168235"
    ).expect("should parse");

    let fp2_pt_ord3_x_c0 = Fq::zero();
    let fp2_pt_ord3_x_c1 = Fq::zero();
    let fp2_pt_ord3_y_c0 = Fq::zero();
    let fp2_pt_ord3_y_c1 = Fq::from_str(
        "64828261740814840065360381756190772627110652128289340260788836867053167272156"
    ).expect("should parse"); 

    let lambda = Fr::from_str(
        "78074008874160198520644763525212887401909906723592317393988542598630163514318"
    ).expect("should parse");
    let beta = Fq::from_str(
        "60197513588986302554485582024885075108884032450952339817679072026166228089408"
    ).expect("should parse");

    let a1 = BigUint::from_str("303414439467246543595250775667605759171").expect("should parse");
    let a2 = BigUint::from_str("64502973549206556628585045361533709077").expect("should parse");
    let minus_b1 = BigUint::from_str("64502973549206556628585045361533709077").expect("should parse");
    let b2 = BigUint::from_str("367917413016453100223835821029139468248").expect("should parse");

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        point_by_scalar_mul_strategy: PointByScalarMulStrategy::Basic,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        _marker: std::marker::PhantomData::<Secp256K1Extension2Params>
    }
}


use crate::bellman::pairing::bls12_381::Bls12;
type BLs12CircuitParameters<E> = CurveCircuitParameters<E, SecpPointAffine, Secp256K1Extension2Params>; 
pub fn generate_optimal_circuit_params_for_bls12<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, base_field_limb_size: usize, scalar_field_limb_size: usize
) -> Secp256K1CircuitParameters<E>
{
    use super::secp256k1::fq::Fq as Fq;
    use super::secp256k1::fr::Fr as Fr;

    let fp2_offset_generator_x_c0 = Fq::from_str(
        "1067264685030724708538788882656460381104931541603938723410358338973606906391679083715376977125266 \
        347261808406513360"
    ).expect("should parse");
    let fp2_offset_generator_x_c1 = Fq::zero();
    let fp2_offset_generator_y_c0 = Fq::from_str(
        "321012996715331830201056169306862715561405722782489933905452108492991173862920704991336014140647306 \
        8435860637374216"
    ).expect("should parse");
    let fp2_offset_generator_y_c1 = Fq::zero();
    
    let fp2_pt_ord3_x_c0 = Fq::zero();
    let fp2_pt_ord3_x_c1 = Fq::zero();
    let mut fp2_pt_ord3_y_c0 = Fq::one();
    fp2_pt_ord3_y_c0.double();
    let fp2_pt_ord3_y_c1 = Fq::zero(); 

    let lambda = Fr::from_str(
        "228988810152649578064853576960394133503"
    ).expect("should parse");
    let beta = Fq::from_str(
        "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350"
    ).expect("should parse");

    let a1 = BigUint::from_str("228988810152649578064853576960394133503").expect("should parse");
    let a2 = BigUint::one();
    let minus_b1 = BigUint::one();
    let b2 = BigUint::from_str("228988810152649578064853576960394133504").expect("should parse");

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        point_by_scalar_mul_strategy: PointByScalarMulStrategy::Basic,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        _marker: std::marker::PhantomData::<Secp256K1Extension2Params>
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
            // okay, first we should check if P is not a point of order 3:
            // if so, it is okay to mix with that point
            // we could also use https://hackmd.io/@yelhousni/bls12_subgroup_check
            unimplemented!();
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

    #[track_caller]
    pub fn pack<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, address: &Num<E>, address_width: usize
    ) -> Result<[Num<E>; 2], SynthesisError> {
        let (x, parity_flag) = self.point_compression(cs)?;
        let shifts = compute_shifts::<E::Fr>();
        let raw_limbs = x.get_raw_limbs_representation(cs)?;
        let limb_width = x.representation_params.binary_limb_width;
        let capacity = x.representation_params.native_field_modulus_bitlength;
            
        let mut result = [Num::<E>::zero(), Num::<E>::zero()];
        let mut offset = 0;
        let mut lc = LinearCombination::zero(); 
        
        for limb in raw_limbs.into_iter() {
            if offset + limb_width >= capacity {
                result[0] = lc.into_num(cs)?;
                lc = LinearCombination::zero(); 
                offset = 0;
            }  
            
            lc.add_assign_number_with_coeff(&limb, shifts[offset]);
            offset += limb_width;
        }
          
        lc.add_assign_boolean_with_coeff(&parity_flag, shifts[offset]); 
        offset += 1;
        lc.add_assign_number_with_coeff(address, shifts[offset]); 
        offset += address_width;
        assert!(offset < capacity);
        result[1] = lc.into_num(cs)?;

        Ok(result)
    }

    // given P = (x, y) returns normalized x and the parity bit of y
    #[track_caller]
    pub fn point_compression<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS
    ) -> Result<(FieldElement<'a, E, G::Base>, Boolean), SynthesisError> {
        let table =  cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME)?;
        let dummy = CS::get_dummy_variable();
        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        
        let mut two = E::Fr::one();
        two.double();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        self.normalize_coordinates(cs)?;
        let lowest_y_limb = &self.y.binary_limbs[0];
        
        let parity_flag = if lowest_y_limb.is_constant() {
            let repr = lowest_y_limb.get_value().unwrap().into_repr();
            Boolean::Constant(repr.is_odd())
        }
        else {
            let limb_width = self.y.representation_params.binary_limb_width;
            let rcd = constraint_bit_length_ext(cs,  &lowest_y_limb.term.num.get_variable(), limb_width)?;
            let a = rcd.get_vars()[0];
            let (parity_flag_wit, b_wit) = match a.get_value() {
                Some(a_wit) => {
                    let mut repr = a_wit.into_repr();
                    let parity_flag_wit = repr.is_odd();
                    repr.div2();
                    let b_wit = E::Fr::from_repr(repr).expect("should parse");
                    (Some(parity_flag_wit), Some(b_wit))
                }
                None => (None, None),
            };
        
            let parity_flag = AllocatedBit::alloc(cs, parity_flag_wit)?;
            let b = AllocatedNum::alloc(cs, || b_wit.grab())?;

            let a_xor_b = match (a.get_value(), b.get_value()) {
                (Some(a_val), Some(b_val)) => {
                    let res = table.query(&[a_val, b_val])?;
                    AllocatedNum::alloc(cs, || Ok(res[0]))?
                },  
                (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
            };

            // a = 2*b + parity_flag
            let vars = [a.get_variable(), b.get_variable(), a_xor_b.get_variable(), parity_flag.get_variable()];
            let coeffs = [minus_one, two, E::Fr::zero(), E::Fr::one()];
            cs.begin_gates_batch_for_step()?;
            cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
            
            let gate_term = MainGateTerm::new();
            let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
            for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
                gate_coefs[idx] = *coef;
            }

            let mg = CS::MainGate::default();
            cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
            cs.end_gates_batch_for_step()?;

            Boolean::from(parity_flag)
        };
        
        Ok((self.x.clone(), parity_flag))
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

    pub fn get_value(&self) -> Option<(G::Base, G::Base, G::Base, G::Base)> {
        self.x.get_value().zip(self.y.get_value()).map(|((x_c0, x_c1), (y_c0, y_c1))| (x_c0, x_c1, y_c0, y_c1) ) 
    }

    pub fn uninitialized(rns_params: &'a RnsParameters<E, G::Base>) -> Self {
        Self::constant(G::Base::zero(), G::Base::zero(), G::Base::zero(), G::Base::zero(), &rns_params)
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, x_c0_wit: Option<G::Base>, x_c1_wit: Option<G::Base>, 
        y_c0_wit: Option<G::Base>, y_c1_wit: Option<G::Base>,
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let x = Fp2::alloc(cs, x_c0_wit, x_c1_wit, rns_params)?;
        let y = Fp2::alloc(cs, y_c0_wit, y_c1_wit, rns_params)?;
        let point = AffinePointExt::<E, G, T> { x, y };
        point.enforce_if_on_curve(cs)?;

        Ok(point)
    } 

    #[track_caller]
    pub fn constant(
        x0: G::Base, x1: G::Base, y0: G::Base, y1: G::Base, rns_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        let x = Fp2::constant(x0, x1, rns_params);
        let y = Fp2::constant(y0, y1, rns_params);  
        AffinePointExt::<E, G, T> { x, y } 
    }

    #[track_caller]
    pub fn enforce_if_on_curve<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let rns_params = self.x.c0.representation_params;
        let a = Fp2::from(FieldElement::constant(G::a_coeff(), rns_params));
        let b = Fp2::from(FieldElement::constant(G::b_coeff(), rns_params));

        let mut lhs = self.y.square(cs)?;
        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let mut rhs = if a.c0.get_field_value().unwrap().is_zero() {
            x_cubed.add(cs, &b)?
        } else {
            let mut chain = Fp2Chain::new();
            chain.add_pos_term(&x_cubed).add_pos_term(&b);
            Fp2::mul_with_chain(cs, &self.x, &a, chain)?
        };

        Fp2::enforce_equal(cs, &mut lhs, &mut rhs)
    }

    #[track_caller]
    pub fn enforce_equal<CS>(cs: &mut CS, left: &mut Self, right: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Fp2::enforce_equal(cs, &mut left.x, &mut right.x)?;
        Fp2::enforce_equal(cs, &mut left.y, &mut right.y)
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

    #[track_caller]
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        let x = Fp2::conditionally_select(cs, &flag, &first.x, &second.x)?;
        let y = Fp2::conditionally_select(cs, &flag, &first.y, &second.y)?;
        Ok(AffinePointExt {x, y})
    }

    #[track_caller]
    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let x = self.x.clone();
        let y = self.y.negate(cs)?;
        Ok(AffinePointExt {x, y})
    }

    #[track_caller]
    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let x = self.x.clone();
        let y = self.y.conditionally_negate(cs, flag)?;
        Ok(AffinePointExt {x, y})
    }
}


// we are particularly interested in three curves: secp256k1, bn256 and bls12-281
// unfortunately, only bls12-381 has a cofactor
impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField 
{
    #[track_caller]
    pub fn mul_by_scalar_descending_ladder<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }
        
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
        let num_of_doubles = scalar_decomposition.len();
        let mut acc = AffinePoint::constant(G::one(), &self.circuit_params);
       
        for bit in scalar_decomposition.into_iter().rev() {
            acc = AffinePoint::double(&acc, cs)?;
            let acc_plus_point = acc.add_unequal_unchecked(cs, &self)?;
            acc = AffinePoint::conditionally_select(cs, &bit, &acc_plus_point, &acc)?;
        }

        let as_scalar_repr = biguint_to_repr::<G::Scalar>(BigUint::from(1u64) << num_of_doubles);
        let scaled_offset_wit = G::one().mul(as_scalar_repr).into_affine();
        let mut scaled_offset = AffinePoint::constant(scaled_offset_wit, &self.circuit_params);
        let result = acc.sub_unequal_unchecked(cs, &mut scaled_offset)?; 

        Ok(result)
    }
    

    #[track_caller]
    pub fn mul_by_scalar_descending_skew_ladder<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }
        
        let circuit_params = self.circuit_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
        let mut acc : AffinePoint<E, G, T> = self.clone();
        let mut y_negated = self.get_y().negate(cs)?;
        y_negated.reduce(cs)?;
      
        for bit in scalar_decomposition[1..].into_iter().rev() {
            let selected_y = FieldElement::conditionally_select(cs, &bit, &self.y, &y_negated)?;
            let mut tmp = unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), selected_y, circuit_params) };
            acc = AffinePoint::double(&acc, cs)?;
            acc = acc.add_unequal_unchecked(cs, &mut tmp)?;
        }

        let with_skew = acc.sub_unequal_unchecked(cs, self)?;
        let flag = scalar_decomposition.first().unwrap();
        let result = AffinePoint::conditionally_select(cs, flag, &acc, &with_skew)?;
        
        Ok(result)
    }


    #[track_caller]
    pub fn mul_by_scalar_descending_skew_ladder_with_endo<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }

        let params = self.circuit_params;
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
        let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
        let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
        let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
        let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

        // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
        let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
        let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&k1).add_neg_term(&scalar);
        let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
        FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

        let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
        let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
        let x_endo = point.get_x().mul(cs, &beta)?;
        let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

        let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
        let point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
        let offset_generator = AffinePoint::constant(G::one(), params);
        let mut acc = offset_generator.add_unequal_unchecked(cs, &point_plus_point_endo)?;
        let num_of_doubles = k1_decomposition[1..].len();
        let iter = k1_decomposition[1..].into_iter().zip(k2_decomposition[1..].into_iter()).rev().enumerate();

        for (_idx, (k1_bit, k2_bit)) in iter {
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
            acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
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
        let k1_bit = k1_decomposition.first().unwrap();
        let k2_bit = k2_decomposition.first().unwrap();
        let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
        let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &point, &point_plus_point_endo)?;
        tmp = AffinePoint::conditionally_select(cs, &k1_bit, &point_endo, &tmp)?;
        let skew_acc = acc.sub_unequal_unchecked(cs, &mut tmp)?;
        acc = AffinePoint::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
       
        let as_scalar_repr = biguint_to_repr::<G::Scalar>(BigUint::from(1u64) << num_of_doubles);
        let scaled_offset_wit = G::one().mul(as_scalar_repr).into_affine();
        let mut scaled_offset = AffinePoint::constant(scaled_offset_wit, params);
        let result = acc.sub_unequal_unchecked(cs, &mut scaled_offset)?; 

        Ok(result)
    }


    #[track_caller]
    pub fn mul_by_scalar_descending_skew_ladder_with_base_ext<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }
        
        let circuit_params = self.circuit_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;

        let offset_generator = AffinePointExt::constant(
            circuit_params.fp2_offset_generator_x_c0, circuit_params.fp2_offset_generator_x_c1,
            circuit_params.fp2_offset_generator_y_c0, circuit_params.fp2_offset_generator_y_c1,
            &circuit_params.base_field_rns_params
        );
        let mut acc = offset_generator.add_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;
        let mut y_negated = self.get_y().negate(cs)?;
        y_negated.reduce(cs)?;
        let num_of_doubles = scalar_decomposition[1..].len();
      
        for bit in scalar_decomposition[1..].into_iter().rev() {
            let selected_y = FieldElement::conditionally_select(cs, &bit, &self.y, &y_negated)?;
            let mut tmp = AffinePointExt::from(
                unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), selected_y, circuit_params) }
            );
            acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
        }

        let with_skew = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(self.clone()))?;
        let flag = scalar_decomposition.first().unwrap();
        acc = AffinePointExt::conditionally_select(cs, flag, &acc, &with_skew)?;
        
        let mut scaled_offset = offset_generator;
        for _ in 0..num_of_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

        let final_x = acc.get_x().c0;
        let final_y = acc.get_y().c0;
        let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        }); 
        // let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
        //     G::from_xy_unchecked(x, y)
        // });

       let result = AffinePoint { 
            x: final_x, 
            y: final_y, 
            value: final_value, 
            is_in_subgroup: self.is_in_subgroup, 
            circuit_params: self.circuit_params 
        };
        Ok(result)
    }

    
    #[track_caller]
    pub fn mul_by_scalar_descending_skew_ladder_with_endo_and_base_ext<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>, 
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }

        let params = self.circuit_params;
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
        let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
        let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
        let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
        let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

        // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
        let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
        let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&k1).add_neg_term(&scalar);
        let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
        FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

        let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
        let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
        let x_endo = point.get_x().mul(cs, &beta)?;
        let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

        let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
        let point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
        let offset_generator = AffinePointExt::constant(
            params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
            params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
            &params.base_field_rns_params
        );
        let mut acc = offset_generator.add_unequal_unchecked(
            cs, &AffinePointExt::from(point_plus_point_endo.clone())
        )?;
        let num_of_doubles = k1_decomposition[1..].len();
        let iter = k1_decomposition[1..].into_iter().zip(k2_decomposition[1..].into_iter()).rev().enumerate();

        for (_idx, (k1_bit, k2_bit)) in iter {
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
            let mut tmp = AffinePointExt::from(
                unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) }
            );
            acc = acc.double_and_add_unchecked(cs, &mut tmp)?;
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
        let k1_bit = k1_decomposition.first().unwrap();
        let k2_bit = k2_decomposition.first().unwrap();
        let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
        let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &point, &point_plus_point_endo)?;
        tmp = AffinePoint::conditionally_select(cs, &k1_bit, &point_endo, &tmp)?;
        let skew_acc = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(tmp))?;
        acc = AffinePointExt::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
       
        let mut scaled_offset = offset_generator;
        for _ in 0..num_of_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

        let final_x = acc.get_x().c0;
        let final_y = acc.get_y().c0;
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
    
    
    
    #[track_caller]
    pub fn safe_multiexp_affine<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self] 
    ) -> Result<Self, SynthesisError> {
        let params = points[0].circuit_params;
        let scalar_rns_params = &params.scalar_field_rns_params;
        let base_rns_params = &params.base_field_rns_params;
        let limit = params.get_endomorphism_bitlen_limit();

        struct PointAuxData<'a1, E1: Engine, G1: GenericCurveAffine + rand::Rand, T1: Extension2Params<G1::Base>> 
        where <G1 as GenericCurveAffine>::Base: PrimeField 
        {
            point: AffinePoint<'a1, E1, G1, T1>,
            point_endo: AffinePoint<'a1, E1, G1, T1>,
            point_plus_point_endo: AffinePoint<'a1, E1, G1, T1>,
            point_minus_point_endo: AffinePoint<'a1, E1, G1, T1>,
            point_scalar_decomposition: Vec<Boolean>,
            point_endo_scalar_decomposition: Vec<Boolean>
        }

        let mut points_aux_data = Vec::<PointAuxData::<E, G, T>>::with_capacity(scalars.len());
        for (scalar, point) in scalars.iter().zip(points.iter()) { 
            let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
                Some(x) => {
                    let dcmp = params.calculate_decomposition(x);
                    (
                        Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
                        Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
                    )
                },
                None => (None, None, None, None)
            };
            let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k1_abs_wit, limit, scalar_rns_params, true
            )?;
            let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k2_abs_wit, limit, scalar_rns_params, true
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

            let mut point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
            let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
            let x_endo = point.get_x().mul(cs, &beta)?;
            let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
            let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

            let point_scalar_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
            let point_endo_scalar_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
            let point_minus_point_endo = point_reg.sub_unequal_unchecked(cs, &mut point_endo)?;
            let point_plus_point_endo = point_reg.add_unequal_unchecked(cs, &point_endo)?;

            let point_aux_data = PointAuxData {
                point: point_reg, point_endo, point_plus_point_endo, point_minus_point_endo,
                point_scalar_decomposition, point_endo_scalar_decomposition
            };
            points_aux_data.push(point_aux_data);
        }
       
        let offset_generator = AffinePointExt::constant(
            params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
            params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
            &params.base_field_rns_params
        );
        let mut acc = offset_generator.clone();
        for point_aux_data in points_aux_data.iter() {
            acc = acc.add_unequal_unchecked(
                cs, &AffinePointExt::from(point_aux_data.point_plus_point_endo.clone())
            )?;
        }
        
        let num_of_doubles = points_aux_data[0].point_scalar_decomposition.len() - 1;
        let mut idx = num_of_doubles; 
        while idx > 0 {
            for (is_first, _is_last, data) in points_aux_data.iter().identify_first_last() {
                let k1_bit = data.point_scalar_decomposition[idx];
                let k2_bit = data.point_endo_scalar_decomposition[idx];
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
                    cs, &xor_flag, &data.point_minus_point_endo.get_x(), &data.point_plus_point_endo.get_x()
                )?;
                let tmp_y = FieldElement::conditionally_select(
                    cs, &xor_flag, &data.point_minus_point_endo.get_y(), &data.point_plus_point_endo.get_y()
                )?;
                let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
                let mut tmp = AffinePointExt::from(
                    unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) }
                );
                acc = if is_first { 
                    acc.double_and_add_unchecked(cs, &mut tmp)? 
                } else {
                    acc.add_unequal_unchecked(cs, &mut tmp)? 
                };
            }
            idx -= 1;
        }

        for data in points_aux_data.iter() {
            let k1_bit = data.point_scalar_decomposition[idx];
            let k2_bit = data.point_endo_scalar_decomposition[idx];
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
            let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
            let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &data.point, &data.point_plus_point_endo)?;
            tmp = AffinePoint::conditionally_select(cs, &k1_bit, &data.point_endo, &tmp)?;
            let skew_acc = acc.sub_unequal_unchecked(cs, &AffinePointExt::from(tmp))?;
            acc = AffinePointExt::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
        }
       
        let mut scaled_offset = offset_generator;
        for _ in 0..num_of_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?; 

        let final_x = acc.get_x().c0;
        let final_y = acc.get_y().c0;
        let final_value = final_x.get_field_value().zip(final_y.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        }); 

       let result = AffinePoint { 
            x: final_x, 
            y: final_y, 
            value: final_value, 
            is_in_subgroup: points[0].is_in_subgroup, 
            circuit_params: points[0].circuit_params 
        };
        Ok(result)
    }

    pub fn safe_multiexp_affine2<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
        assert_eq!(scalars.len(), points.len());
        let params = points[0].circuit_params;
        let scalar_rns_params = &params.scalar_field_rns_params;
        let base_rns_params = &params.base_field_rns_params;
        let limit = params.get_endomorphism_bitlen_limit();
        
        struct Multizip<T>(Vec<T>);
        
        impl<T> Iterator for Multizip<T>
        where T: Iterator,
        {
            type Item = Vec<T::Item>;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.iter_mut().map(Iterator::next).collect()
            }
        }

        let offset_generator = AffinePointExt::constant(
            params.fp2_offset_generator_x_c0, params.fp2_offset_generator_x_c1,
            params.fp2_offset_generator_y_c0, params.fp2_offset_generator_y_c1,
            &params.base_field_rns_params
        );
        let adj_offset = AffinePointExt::constant(
            params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
            params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
            &params.base_field_rns_params
        );

        let mut points_unrolled = Vec::with_capacity(points.len() << 1);
        let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
        for (is_first, _is_last, (scalar, point)) in scalars.iter().zip(points.iter()).identify_first_last() { 
            let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
                Some(x) => {
                    let dcmp = params.calculate_decomposition(x);
                    (
                        Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
                        Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
                    )
                },
                None => (None, None, None, None)
            };
            let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k1_abs_wit, limit, scalar_rns_params, true
            )?;
            let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k2_abs_wit, limit, scalar_rns_params, true
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

            let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
            let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
            let x_endo = point.get_x().mul(cs, &beta)?;
            let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
            let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

            let mut point_ext = AffinePointExt::<E, G, T>::from(point_reg);
            if is_first {
                point_ext = point_ext.add_unequal_unchecked(cs, &adj_offset)?;
            }
            let point_endo_ext = AffinePointExt::<E, G, T>::from(point_endo);
            points_unrolled.push(point_ext);
            points_unrolled.push(point_endo_ext);

            let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
            let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
            scalars_unrolled.push(k1_decomposition.into_iter());
            scalars_unrolled.push(k2_decomposition.into_iter());
        }

        println!("before acum");
        let selector_tree = SelectorTree::new(cs, &points_unrolled)?;
        println!("after acum");
        let mut acc = selector_tree.get_initial_accumulator();
        acc = acc.add_unequal_unchecked(cs, &offset_generator)?;

        for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
            if !is_last {
                acc = acc.double(cs)?;
                let to_add = selector_tree.select(cs, &bits)?;
                acc = acc.add_unequal_unchecked(cs, &to_add)?;
            }
            else {
                println!("before last");
                let to_add = selector_tree.select_last(cs, &bits)?;
                println!("after last");
                acc = acc.add_unequal_unchecked(cs, &to_add)?;
            }
        }

        let gate_count_start = cs.get_current_step_number();
        let num_of_doubles = limit - 1;
        let mut scaled_offset = offset_generator;
        for _ in 0..num_of_doubles {
            scaled_offset = scaled_offset.double(cs)?;
        }
        let gate_count_end = cs.get_current_step_number();
        assert_eq!(gate_count_end - gate_count_start, 0);
        acc = acc.sub_unequal_unchecked(cs, &scaled_offset)?;

        let is_defined_over_base_field = |point: &AffinePointExt<'a, E, G, T>| -> Option<bool> {
            point.get_value().map(|(_x_c0, x_c1, _y_c0, y_c1)| x_c1.is_zero() && y_c1.is_zero())
        };

        println!("before last check");

        // adj_offset is a point of order 3, hence one of acc, acc + adj_offset, acc - adj belong to E(F_p)
        let need_to_negate_wit = acc.get_value().map(|(x_c0, x_c1, y_c0, y_c1)| {
            let gate_count_start = cs.get_current_step_number();

            let mut tmp = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, base_rns_params);
            tmp = tmp.add_unequal_unchecked(cs, &adj_offset).expect("should synthesize");
            let flag = is_defined_over_base_field(&tmp).expect("should be some");    
               
            let gate_count_end = cs.get_current_step_number();
            assert_eq!(gate_count_end - gate_count_start, 0);
            !flag
        });

        println!("after last check");


        let need_to_negate = Boolean::Is(AllocatedBit::alloc(cs, need_to_negate_wit)?);
        let to_add = adj_offset.conditionally_negate(cs, &need_to_negate)?;
        let modified_acc = acc.add_unequal_unchecked(cs, &to_add)?;
        
        let cond_wit = is_defined_over_base_field(&modified_acc);
        let cond = Boolean::Is(AllocatedBit::alloc(cs, cond_wit)?);
        let res_ext = AffinePointExt::conditionally_select(cs, &cond, &modified_acc, &acc)?; 

        let mut final_x = res_ext.get_x();
        let mut final_y = res_ext.get_y();
        let final_value = final_x.c0.get_field_value().zip(final_y.c0.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        }); 
        let mut zero = FieldElement::<E, G::Base>::zero(base_rns_params);
        FieldElement::enforce_equal(cs, &mut final_x.c1, &mut zero)?;
        FieldElement::enforce_equal(cs, &mut final_y.c1, &mut zero)?;

        println!("THE VERY FINAL VALUE: {}", final_value.unwrap());


        let new = Self {
            x: final_x.c0,
            y: final_y.c0,
            value: final_value,
            is_in_subgroup: true,
            circuit_params: params
        };
        Ok(new)
    }
}


impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePoint<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField {
    pub fn mul_by_scalar_ascending_ladder_proj<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        let params = self.circuit_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;

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


    pub fn mul_by_scalar_ascending_skew_ladder_proj<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        let params = self.circuit_params;
        let mut scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
        scalar_decomposition.push(Boolean::constant(true));

        let point_negated = AffinePoint::negate(&self, cs)?;
        let bit = scalar_decomposition[0];
        let mut acc = ProjectivePoint::<E, G, T>::conditionally_select(
            cs, &bit, &ProjectivePoint::zero(params), &ProjectivePoint::<E, G, T>::from(point_negated)
        )?;
        let mut tmp : AffinePoint<_, _, _> = self.clone();
        
        for (_is_first, is_last, bit) in scalar_decomposition[1..].into_iter().identify_first_last() {
            let mut to_add = tmp.conditionally_negate(cs, &bit.not())?;
            acc = acc.add_mixed(cs, &mut to_add)?;
            if !is_last {   
                tmp = AffinePoint::double(&tmp, cs)?;
            }
        }
        
        Ok(acc)
    }


    pub fn mul_by_scalar_descending_skew_ladder_proj<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        let params = self.circuit_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs, None)?;
        let mut acc = ProjectivePoint::<E, G, T>::from(self.clone());
        let mut y_negated = self.get_y().negate(cs)?;
        y_negated.reduce(cs)?;
      
        for (_, is_last, bit) in scalar_decomposition.into_iter().rev().identify_first_last() {
            if !is_last {  
                acc = acc.double(cs)?;
                let selected_y = FieldElement::conditionally_select(cs, &bit, &self.y, &y_negated)?;
                let mut tmp = unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), selected_y, params) };
                acc = acc.add_mixed(cs, &mut tmp)?;
            }
            else {
                let mut tmp = unsafe { AffinePoint::from_xy_unchecked(self.x.clone(), y_negated.clone(), params) };
                let skewed_acc = acc.add_mixed(cs, &mut tmp)?;
                acc = ProjectivePoint::conditionally_select(cs, &bit, &acc, &skewed_acc)?;
            }
        }
        
        Ok(acc)
    }


    pub fn mul_by_scalar_descending_skew_ladder_with_endo_proj<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        let params = self.circuit_params;
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
        let mut k1_abs = FieldElement::alloc_for_known_bitwidth(cs, k1_abs_wit, limit, scalar_rns_params, true)?;
        let mut k2_abs = FieldElement::alloc_for_known_bitwidth(cs, k2_abs_wit, limit, scalar_rns_params, true)?;
        let k1_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k1_flag_wit)?);
        let k2_is_negative_flag = Boolean::Is(AllocatedBit::alloc(cs, k2_flag_wit)?);

        // constraint that scalar = (k1_sign) * k1_abs + lambda * (k2_sign) * k2_abs
        let k1 = k1_abs.conditionally_negate(cs, &k1_is_negative_flag)?;
        let k2 = k2_abs.conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&k1).add_neg_term(&scalar);
        let lambda = FieldElement::constant(params.lambda.clone(), scalar_rns_params);
        FieldElement::constraint_fma(cs, &k2, &lambda, chain)?;

        let mut point = self.conditionally_negate(cs, &k1_is_negative_flag)?;
        let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
        let x_endo = point.get_x().mul(cs, &beta)?;
        let y_endo = self.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
        let mut point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

        let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
        let point_minus_point_endo = point.sub_unequal_unchecked(cs, &mut point_endo)?;
        let point_plus_point_endo = point.add_unequal_unchecked(cs, &point_endo)?;
       
        let mut acc = ProjectivePoint::<E, G, T>::from(point_plus_point_endo.clone());
        let iter = k1_decomposition.into_iter().zip(k2_decomposition.into_iter()).rev().identify_first_last();

        for (_, is_last, (k1_bit, k2_bit)) in iter {
            if !is_last {
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
                acc = acc.double(cs)?;
                let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
                let selected_x = FieldElement:: conditionally_select(
                    cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
                )?;
                let tmp_y = FieldElement::conditionally_select(
                    cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
                )?;
                let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
                let mut tmp = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) };
                acc = acc.add_mixed(cs, &mut tmp)?;
            }
            else {
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
                let tmp0 = ProjectivePoint::conditionally_select(
                    cs, &k2_bit, &ProjectivePoint::zero(params), &ProjectivePoint::from(point_endo.clone())
                )?;
                let tmp1 = ProjectivePoint::from(AffinePoint::conditionally_select(
                    cs, &k2_bit, &point, &point_plus_point_endo
                )?);
                let mut point_to_sub = ProjectivePoint::conditionally_select(cs, &k1_bit, &tmp0, &tmp1)?;
                acc = acc.sub(cs, &mut point_to_sub)?;
            }
        }
        
        Ok(acc)
    }


    pub fn safe_multiexp_projective<CS: ConstraintSystem<E>>(
        cs: &mut CS, scalars: &[FieldElement<'a, E, G::Scalar>], points: &[Self]
    ) -> Result<ProjectivePoint<'a, E, G, T>, SynthesisError> {
        assert_eq!(scalars.len(), points.len());
        let params = points[0].circuit_params;
        let scalar_rns_params = &params.scalar_field_rns_params;
        let base_rns_params = &params.base_field_rns_params;
        let limit = params.get_endomorphism_bitlen_limit();
        
        struct Multizip<T>(Vec<T>);
        
        impl<T> Iterator for Multizip<T>
        where T: Iterator,
        {
            type Item = Vec<T::Item>;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.iter_mut().map(Iterator::next).collect()
            }
        }

        let mut points_unrolled = Vec::with_capacity(points.len() << 1);
        let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
        for (scalar, point) in scalars.iter().zip(points.iter()) { 
            let (k1_flag_wit, k1_abs_wit, k2_flag_wit, k2_abs_wit) = match scalar.get_field_value() {
                Some(x) => {
                    let dcmp = params.calculate_decomposition(x);
                    (
                        Some(dcmp.k1_is_negative), Some(dcmp.k1_modulus), 
                        Some(dcmp.k2_is_negative), Some(dcmp.k2_modulus)
                    )
                },
                None => (None, None, None, None)
            };
            let mut k1_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k1_abs_wit, limit, scalar_rns_params, true
            )?;
            let mut k2_abs = FieldElement::alloc_for_known_bitwidth(
                cs, k2_abs_wit, limit, scalar_rns_params, true
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

            let point_reg = point.conditionally_negate(cs, &k1_is_negative_flag)?;
            let beta = FieldElement::constant(params.beta.clone(), base_rns_params);
            let x_endo = point.get_x().mul(cs, &beta)?;
            let y_endo = point.get_y().conditionally_negate(cs, &k2_is_negative_flag)?;
            let point_endo = unsafe { AffinePoint::from_xy_unchecked(x_endo, y_endo, params) };

            let point_proj = ProjectivePoint::<E, G, T>::from(point_reg);
            let point_endo_proj = ProjectivePoint::<E, G, T>::from(point_endo);
            points_unrolled.push(point_proj);
            points_unrolled.push(point_endo_proj);

            let k1_decomposition = k1_abs.decompose_into_binary_representation(cs, Some(limit))?;
            let k2_decomposition = k2_abs.decompose_into_binary_representation(cs, Some(limit))?;
            scalars_unrolled.push(k1_decomposition.into_iter());
            scalars_unrolled.push(k2_decomposition.into_iter());
        }

        let selector_tree = SelectorTree::new(cs, &points_unrolled)?;
        let mut acc = selector_tree.get_initial_accumulator();

        for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
            if !is_last {
                acc = acc.double(cs)?;
                let to_add = selector_tree.select(cs, &bits)?;
                acc = acc.add(cs, &to_add)?;
            }
            else {
                let to_add = selector_tree.select_last(cs, &bits)?;
                acc = acc.add(cs, &to_add)?;
            }
        }

        Ok(acc)
    }


    
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1, G1Affine};
    use crate::bellman::pairing::bls12_381::Bls12;
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
        let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
        let mut rng = rand::thread_rng();

        let a: G1Affine = rng.gen();
        let b: G1Affine = rng.gen();
        let mut tmp = bellman::CurveAffine::into_projective(&a);
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
        circuit_params: CurveCircuitParameters<E, G, T>
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
            let mut result = a.mul_by_scalar_descending_ladder(cs, &mut scalar)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending ladder: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let mut result = a.mul_by_scalar_descending_skew_ladder(cs, &mut scalar)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending skew ladder: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let mut result = a.mul_by_scalar_descending_skew_ladder_with_endo(cs, &mut scalar)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending skew ladder with_endo: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let mut result = a.mul_by_scalar_descending_skew_ladder_with_base_ext(cs, &mut scalar)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending skew ladder with base ext: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let mut result = a.mul_by_scalar_descending_skew_ladder_with_endo_and_base_ext(cs, &mut scalar)?;
            let naive_mul_end = cs.get_current_step_number();
            println!(
                "num of gates for descending skew ladder with endo and base ext: {}", naive_mul_end - naive_mul_start
            );
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            
            let naive_mul_start = cs.get_current_step_number();
            let result = a.mul_by_scalar_ascending_ladder_proj(cs, &mut scalar)?;
            let mut result = unsafe { result.convert_to_affine(cs)? };
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for ascending ladder proj: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let result = a.mul_by_scalar_ascending_skew_ladder_proj(cs, &mut scalar)?;
            let mut result = unsafe { result.convert_to_affine(cs)? };
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for ascending skew ladder proj: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let result = a.mul_by_scalar_descending_skew_ladder_proj(cs, &mut scalar)?;
            let mut result = unsafe { result.convert_to_affine(cs)? };
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending skew ladder proj: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let result = a.mul_by_scalar_descending_skew_ladder_with_endo_proj(cs, &mut scalar)?;
            let mut result = unsafe { result.convert_to_affine(cs)? };
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for descending skew ladder with endo proj: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            Ok(())
        }
    }

    #[test]
    fn test_scalar_multiplication_for_bn256() {
        const LIMB_SIZE: usize = 80;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestCircuit { circuit_params };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_generic_projective_double_add() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
        let mut rng = rand::thread_rng();

        let mut a = G1::zero();
        let mut b = G1::zero();
        for out in std::iter::once(&mut a).chain(std::iter::once(&mut b)) { 
            let affine_point: G1Affine = rng.gen();
            let (mut x, mut y) = GenericCurveAffine::into_xy_unchecked(affine_point);
            let z : Fq = rng.gen();
            x.mul_assign(&z);
            y.mul_assign(&z);
            
            let proj_point = G1::from_xyz_checked(x, y, z).expect("should be a valid point");
            *out = proj_point;
        }
        let mut result = a.clone();
        result.double(); 
        result.add_assign(&b);

        let a = ProjectivePoint::alloc(&mut cs, Some(a), &params).unwrap();
        let mut b = ProjectivePoint::alloc(&mut cs, Some(b), &params).unwrap();
        let mut actual_result = ProjectivePoint::alloc(&mut cs, Some(result), &params).unwrap();
        
        let naive_mul_start = cs.get_current_step_number();
        let mut result = ProjectivePoint::double(&a, &mut cs).unwrap(); 
        result = result.add(&mut cs, &mut b).unwrap();
        let naive_mul_end = cs.get_current_step_number();
        println!("num of gates: {}", naive_mul_end - naive_mul_start);

        ProjectivePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_generic_affine_extended_double_add() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
        let rns_params = &params.base_field_rns_params;

        let a_x_c0 = "11947046220310406338075336430452637192462772637241719407011734688739628070508";
        let a_x_c1 = "10557742219851096102260847081504953836102098067687282141689259525204118168143";
        let a_y_c0 = "15601064320065192494908094207408122343972055839928949425916220757362334086123";
        let a_y_c1 = "8529668414453473015102015524644323833697434755595850489456056849073813231365";
        let a_coefs = [&a_x_c0, &a_x_c1, &a_y_c0, &a_y_c1];

        let b_x_c0 = "220307984863270321646848220250400852276700881024772566232775081293241238563";
        let b_x_c1 = "1268657104210478535811095545301172618324930929631779260627009638542643809713";
        let b_y_c0 = "14716094244763148080513574234943212664563830050269302711516770265264441206811";
        let b_y_c1 = "1767762926323305702692527140415867669545860126912362251081259289072812848508";
        let b_coefs = [&b_x_c0, &b_x_c1, &b_y_c0, &b_y_c1];

        let c_x_c0 = "14502852985533014211323301556586986708073645991817525233238442508152308472745";
        let c_x_c1 = "3731688454144978548314047313025143811107288207224347116507836166136690390974";
        let c_y_c0 = "3341290380766155696716470666946884673121015452733721707932930112416013276659";
        let c_y_c1 = "5650743550923202600541315224154807569595826295523387795464783550769874508672";
        let c_coefs = [&c_x_c0, &c_x_c1, &c_y_c0, &c_y_c1];

        let mut a = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
        let mut b = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
        let mut c = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
                
        let iter = std::iter::once(&mut a).chain(std::iter::once(&mut b)).chain(std::iter::once(&mut c)).zip(
            std::iter::once(&a_coefs).chain(std::iter::once(&b_coefs)).chain(std::iter::once(&c_coefs))
        );

        for (out, coeffs) in iter  { 
            let x_c0 = Fq::from_str(coeffs[0]);
            let x_c1 = Fq::from_str(coeffs[1]);
            let y_c0 = Fq::from_str(coeffs[2]);
            let y_c1 = Fq::from_str(coeffs[3]);
            let point = AffinePointExt::alloc(&mut cs, x_c0, x_c1, y_c0, y_c1, rns_params).unwrap();
            *out = point;
        }

        let naive_mul_start = cs.get_current_step_number();
        let mut result = a.double_and_add_unchecked(&mut cs, &mut b).unwrap(); 
        let naive_mul_end = cs.get_current_step_number();
        println!("num of gates: {}", naive_mul_end - naive_mul_start);

        AffinePointExt::enforce_equal(&mut cs, &mut result, &mut c).unwrap();
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


    struct TestMultiexpCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>,
        num_of_points: usize
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestMultiexpCircuit<E, G, T> 
    where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
    {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }
    
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut rng = rand::thread_rng();
            let mut points = Vec::with_capacity(self.num_of_points);
            let mut scalars = Vec::with_capacity(self.num_of_points);

            let mut result_wit_proj = G::Projective::zero();
            for _ in 0..self.num_of_points {
                let scalar_wit : G::Scalar = rng.gen();
                let point_wit : G = rng.gen();

                let mut tmp = point_wit.into_projective();
                tmp.mul_assign(scalar_wit);
                result_wit_proj.add_assign(&tmp);

                let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
                let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;

                points.push(point);
                scalars.push(scalar);
            }

            let result_wit = result_wit_proj.into_affine();
            println!("ACTUAL VALUE: {}", result_wit);
            let mut actual_result = AffinePoint::alloc(cs, Some(result_wit), &self.circuit_params)?;
           

            let naive_mul_start = cs.get_current_step_number();
            let mut result = AffinePoint::safe_multiexp_affine(cs, &scalars, &points)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for affine multiexp var1: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let naive_mul_start = cs.get_current_step_number();
            let mut result = AffinePoint::safe_multiexp_affine2(cs, &scalars, &points)?;
            let naive_mul_end = cs.get_current_step_number();
            println!("num of gates for affine multiexp var2: {}", naive_mul_end - naive_mul_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;


            // let naive_mul_start = cs.get_current_step_number();
            // let result = AffinePoint::safe_multiexp_projective(cs, &scalars, &points)?;
            // let mut result = unsafe { result.convert_to_affine(cs)? };
            // let naive_mul_end = cs.get_current_step_number();
            // println!("num of gates for proj multiexp: {}", naive_mul_end - naive_mul_start);
            // AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            Ok(())
        }
    }

    #[test]
    fn test_multiexp_scalar_multiplication_for_bn256() {
        const LIMB_SIZE: usize = 80;
        const NUM_OF_POINTS: usize = 3;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestMultiexpCircuit { circuit_params, num_of_points: NUM_OF_POINTS };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }
}


// if x = [x_0, x_1, ..., x_n] = /sum x_i 2^i - binary representation of x: x_i /in {0, 1}
// then x = [y_-1, y_0, y_1, ..., y_n] - skewed naf representation: where y_i /in {0, 1}
// x = -y_-1 + /sum_{i >= 1} (1 - 2* y_i) 2^i
// algorithm for construction of skewed representation: 
// for -1 <= y < n: y_i = ~x_{i+1} = 1 - x_{i+1} and y_n = 0 (always)
// indeed:
// y = -y_-1 + /sum (1 - 2* y_i) 2^i = x_0 - 1 + /sum (2* x_{i+1} - 1) 2^i +2^n = 
// = x - 1 - \sum_{i=0}^{n-1} 2^i + 2^n = x - 1 - (2^n - 1) + 2^n = x

// if x is simultaneously split into chunks: x = [x_ch_0, x_ch_1, ..., x_ch_k] of length l
// then we split y = [y_-1, y_0, y_1, ..., y_n] into chunks of l bits length 
// and we would have the following relations between corresponding chunks of x and y:
// y_ch_0 = x_ch_0 - 2^l
// for every intermidiate chunk (every chunk between least significant and most sigificant chunks):
// y_ch_i = x_ch_i - 2^l + 1
// y_ch_l = x_ch_k + 1



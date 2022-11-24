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
use num_traits::*;
use std::str::FromStr;
use crate::plonk::circuit::bigint::*;
use plonk::circuit::curve::ProjectivePoint;
use plonk::circuit::utils::from_silverman_basis;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MultiexpStrategy {
    SelectionTree,
    WaksmanBasedRam,
    HashSetsBasedRam
}

impl std::fmt::Display for MultiexpStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MultiexpStrategy::SelectionTree => write!(f, "selection table"),
            MultiexpStrategy::WaksmanBasedRam => write!(f, "waksman based ram"),
            MultiexpStrategy::HashSetsBasedRam => write!(f, "hash-sets based ram")
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultiExpGeometry {
    pub strategy: MultiexpStrategy,
    pub width: usize,
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

    pub fp2_offset_generator_x_c0: G::Base,
    pub fp2_offset_generator_x_c1: G::Base,
    pub fp2_offset_generator_y_c0: G::Base,
    pub fp2_offset_generator_y_c1: G::Base,

    pub fp2_pt_ord3_x_c0: G::Base,
    pub fp2_pt_ord3_x_c1: G::Base,
    pub fp2_pt_ord3_y_c0: G::Base,
    pub fp2_pt_ord3_y_c1: G::Base,
    
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

    pub opt_multiexp_geometry: MultiExpGeometry
}

impl<E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> CurveCircuitParameters<E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField {
    fn rounded_div(dividend: BigUint, divisor: BigUint) -> BigUint {
        (dividend + (divisor.clone() >> 1)) / divisor
    }

    pub fn get_opt_multiexp_geometry(&self) -> MultiExpGeometry {
        self.opt_multiexp_geometry
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

    let opt_multiexp_geometry = MultiExpGeometry { 
        width: 4, strategy: MultiexpStrategy::SelectionTree
    };

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        opt_multiexp_geometry,
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

    let opt_multiexp_geometry = MultiExpGeometry { 
        width: 4, strategy: MultiexpStrategy::SelectionTree
    };

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        opt_multiexp_geometry,
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
        "1067264685030724708538788882656460381104931541603938723410358338973606906391679083715376977125266347261808406513360"
    ).expect("should parse");
    let fp2_offset_generator_x_c1 = Fq::zero();
    let fp2_offset_generator_y_c0 = Fq::from_str(
        "3210129967153318302010561693068627155614057227824899339054521084929911738629207049913360141406473068435860637374216"
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

    let opt_multiexp_geometry = MultiExpGeometry { 
        width: 4, strategy: MultiexpStrategy::SelectionTree
    };

    CurveCircuitParameters {
        base_field_rns_params: RnsParameters::<E, Fq>::new_optimal(cs, base_field_limb_size),
        scalar_field_rns_params: RnsParameters::<E, Fr>::new_optimal(cs, scalar_field_limb_size),
        is_prime_order_curve: true,
        fp2_offset_generator_x_c0,
        fp2_offset_generator_x_c1,
        fp2_offset_generator_y_c0,
        fp2_offset_generator_y_c1,
        fp2_pt_ord3_x_c0,
        fp2_pt_ord3_x_c1,
        fp2_pt_ord3_y_c0,
        fp2_pt_ord3_y_c1,
        lambda, beta, a1, a2, minus_b1, b2,
        opt_multiexp_geometry,
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
        let circuit_params = params;
        let new = Self { x, y, value, circuit_params};

        if require_checks {
            let before = cs.get_current_step_number();
            new.enforce_if_on_curve(cs)?;
            let after = cs.get_current_step_number();
            println!("before {}, after {}", before, after);
            new.enforce_if_in_subgroup(cs)?;
        }
        Ok((new, x_decomposition, y_decomposition))
    }

    pub unsafe fn from_xy_unchecked(
        x: FieldElement<'a, E, G::Base>,
        y: FieldElement<'a, E, G::Base>,
        params: &'a CurveCircuitParameters<E, G, T>,
    ) -> Self {
        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_checked(x, y).expect("should be on curve"))
            },
            _ => {
                None
            }
        };

        let new = Self {x, y, value, circuit_params: params };
        new
    }

    pub fn constant(value: G, params: &'a CurveCircuitParameters<E, G, T>) -> Self {
        assert!(!value.is_zero());
        let (x, y) = value.into_xy_unchecked();
        let x = FieldElement::constant(x, &params.base_field_rns_params);
        let y = FieldElement::constant(y, &params.base_field_rns_params);
        let new = Self { x, y, value: Some(value), circuit_params: params };

        new
    }

    // uninitialized point may be also treated as point at infitnity: 
    // it has y_coordinate = 0 and there are no such points on the curve until |ord(E)| is divisible by 2
    pub fn uninitialized(params: &'a CurveCircuitParameters<E, G, T>) -> Self {
        let rns_params = &params.base_field_rns_params;
        let zero = FieldElement::zero(rns_params);
        Self { 
            x: zero.clone(), 
            y: zero.clone(), 
            value: Some(G::zero()), 
            circuit_params: params 
        }
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
            // https://eprint.iacr.org/2019/814.pdf
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
                let (x1, _y1) = first.into_xy_unchecked();
                let (x2, _y2) = second.into_xy_unchecked();
                assert!(x1 != x2, "can't add points with the same x cooridnate");
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
    pub fn sub_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                let (x1, _y1) = first.into_xy_unchecked();
                let (x2, _y2) = second.into_xy_unchecked();
                assert!(x1 != x2, "can't sub points with the same x cooridnate");
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
            circuit_params: self.circuit_params
        };
        Ok(new)
    }

    // doubles self and adds other
    #[track_caller]
    pub fn double_and_add_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better
        // we can also try https://eprint.iacr.org/2015/1060.pdf
        // only check that x - x' != 0 and go into the unchecked routine
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.double_and_add_unequal_unchecked(cs, &other)
    }

    #[track_caller]
    pub fn double_and_add_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
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

    // we assume that the limb fits into range check granularity
    fn get_parity_bit<CS>(cs: &mut CS, x: &Term<E>, width: usize) -> Result<Boolean, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let parity_flag = if x.is_constant() {
            let repr = x.get_value().unwrap().into_repr();
            Boolean::Constant(repr.is_odd())
        }
        else {
            let table =  cs.get_table(BITWISE_LOGICAL_OPS_TABLE_NAME)?;
            let default_granularity = (crate::log2_floor(table.size()) / 2) as usize;
            let dummy = CS::get_dummy_variable();
            let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
            
            let mut two = E::Fr::one();
            two.double();
            let mut minus_one = E::Fr::one();
            minus_one.negate();

            let a = if width > default_granularity {
                let rcd = constraint_bit_length_ext(cs,  &x.get_variable(), width)?;
                rcd.get_vars()[0]
            } else {
                x.get_variable()
            };
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

        Ok(parity_flag)
    }

    // given P = (x, y) returns normalized x and the parity bit of y
    #[track_caller]
    pub fn point_compression<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS
    ) -> Result<(FieldElement<'a, E, G::Base>, Boolean), SynthesisError> {
        self.normalize_coordinates(cs)?;
        let lowest_y_limb = &self.y.binary_limbs[0];
        let parity_flag = Self::get_parity_bit(
            cs, &lowest_y_limb.term, self.y.representation_params.binary_limb_width
        )?;
        
        Ok((self.x.clone(), parity_flag))
    }
    
    pub fn halving<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let wit = self.get_value().map(|x| {
            // if x = 2 * y and order of group is n - odd prime, then:
            // (n-1)/2 * x = (n-1) * y = -y
            let mut scalar = <G::Scalar as PrimeField>::char();
            scalar.div2();
            let mut res = x.mul(scalar).into_affine();
            res.negate();
            res
        });

        let halved = AffinePoint::alloc(cs, wit, self.circuit_params)?;
        let mut initial = halved.double(cs)?;
        AffinePoint::enforce_equal(cs, self, &mut initial)?;
        
        Ok(halved)
    }
    
    // elliptic point addtion is not exception free: it is not possible if x = x'
    // this function checks if x = x' and in this case it returns some garbage result and flag indicating
    // that result is meaningless, if addtio is possible withput exception then this function simply does
    // the operation and returned is_garbage flag is false
    pub fn prudent_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<(Self, Boolean), SynthesisError>
    where CS: ConstraintSystem<E> {
        let garbage_flag = FieldElement::equals(cs, &mut self.x, &mut other.x)?;
        let mut tmp = other.clone();
        tmp.x = tmp.get_x().conditionally_increment(cs, &garbage_flag)?;
        tmp.value = tmp.get_value().map(|x| {
            if garbage_flag.get_value().unwrap_or(false) {
                G::zero()
            } else {
                x
            }
        });
        let result = self.add_unequal_unchecked(cs, &tmp)?;
        Ok((result, garbage_flag))
    }

    pub fn prudent_sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<(Self, Boolean), SynthesisError>
    where CS: ConstraintSystem<E> {
        let garbage_flag = FieldElement::equals(cs, &mut self.x, &mut other.x)?;
        let mut tmp = other.clone();
        tmp.x = tmp.get_x().conditionally_increment(cs, &garbage_flag)?;
        tmp.value = tmp.get_value().map(|x| {
            if garbage_flag.get_value().unwrap_or(false) {
                G::zero()
            } else {
                x
            }
        });
        let result = self.sub_unequal_unchecked(cs, &tmp)?;
        Ok((result, garbage_flag))
    }
    /*
    Technique for checking that a point P exists within G1.
    We use the LLL algorithm to find the subgroup check:
    [(z^2 − 1)/3](2σ(P) − P − σ^2(P)) − σ^2(P) = inf
    with using only trivial group operations and a scalar multiplication by (z^2 − 1)/3, 
    which is half the size of q and has low Hamming weight.

    Sourse: https://eprint.iacr.org/2019/814.pdf
    */
    pub fn fast_subgroup_checks<CS>(self, cs: &mut CS)-> Result<Boolean, SynthesisError>
    where CS: ConstraintSystem<E> {

        let params = self.clone().circuit_params;
        let base_rns_params = &params.base_field_rns_params;
        let beta = FieldElement::constant(params.beta, base_rns_params);

        let point_from_aff_to_proj = ProjectivePoint::from(self.clone());

        // The value z = -0xd201000000010000 gives the largest qnand the lowest Hamming weight meeting these criteria.
        // in our case, it is not necessary to take a negative constant
        let z_parametr = BigUint::from_str("15132376222941642752").unwrap();
        let three = BigUint::from_str("3").unwrap();

        // (z^2 − 1)/3
        let wit_scalar = (pow(z_parametr, 2) - BigUint::one())/three;
        let scalar_ff = G::Scalar::from_str(&wit_scalar.to_str_radix(10)).unwrap();

        let scalar_with_minus_one = [
        1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
        0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
        0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1];

        assert_eq!(from_silverman_basis(scalar_with_minus_one.to_vec()), wit_scalar);

        let endo_x = point_from_aff_to_proj.get_x().mul(cs, &beta)?;
        let endo_exp2_x = endo_x.mul(cs, &beta)?;

        let endo_point = ProjectivePoint::from_coordinates_unchecked(
            endo_x, 
            point_from_aff_to_proj.get_y(), 
            point_from_aff_to_proj.get_z(), 
            point_from_aff_to_proj.circuit_params
        );
        let endo_point_exp2 = ProjectivePoint::from_coordinates_unchecked(
            endo_exp2_x, 
            point_from_aff_to_proj.get_y(), 
            point_from_aff_to_proj.get_z(), 
            point_from_aff_to_proj.circuit_params
        );

        //(2σ(P) − P − σ^2(P))
        let mut equation = endo_point.double(cs)?;
        equation.sub(cs, &point_from_aff_to_proj)?;
        equation.sub(cs, &endo_point_exp2)?;
        let reserv = equation.clone();

        equation.double_and_add_const_scalar_for_ternaryexp(cs, scalar_with_minus_one.to_vec())?;

        let mut actual_result;
        if let Some(witness) = reserv.get_value(){
            let mut witness = witness.into_projective();
            witness.mul_assign(scalar_ff);
            actual_result = ProjectivePoint::from(
                AffinePoint::alloc(cs, Some(witness.into_affine()), &params).unwrap()
            );
        } else{
            actual_result = ProjectivePoint::from(
                AffinePoint::alloc(cs, None, &params).unwrap()
            );
        }

        let mut cur_point = actual_result.double(cs)?;
        cur_point.add(cs, &actual_result)?;
        ProjectivePoint::enforce_equal(cs, &mut cur_point, &mut equation)?;

        // do not forget about − σ^2(P)
        actual_result = actual_result.sub(cs, &endo_point_exp2)?;


        let if_is = ProjectivePoint::equals(cs, &mut actual_result, &mut ProjectivePoint::zero(&params))?;

        Ok(if_is)
    }
}

pub fn from_dec_to_vecbool(decimal: BigUint)-> Vec<Option<bool>>{
    let str: &str = &format!("{decimal:b}");
    let char: Vec<char> = str.chars().collect::<Vec<_>>();
    let mut vec_bool = vec![];

    for i in char.iter(){
        let bool = *i == '1';
        vec_bool.push(Some(bool));
    }
    vec_bool

}



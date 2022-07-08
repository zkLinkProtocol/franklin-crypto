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

#[derive(Clone, Debug)]
pub struct AffinePoint<'a, E: Engine, G: GenericCurveAffine> where <G as GenericCurveAffine>::Base: PrimeField {
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    pub value: Option<G>,
}

impl<'a, E: Engine, G: GenericCurveAffine> AffinePoint<'a, E, G> where <G as GenericCurveAffine>::Base: PrimeField {
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<G>, params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let (new, _x_decomposition, _y_decomposition) = Self::alloc_ext(cs, value, params)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<G>, params: &'a RnsParameters<E, G::Base>
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

        let (x, x_decomposition) = FieldElement::alloc_ext(cs, x, params)?;
        let (y, y_decomposition) = FieldElement::alloc_ext(cs, y, params)?;
        let new = Self { x, y, value};

        Ok((new, x_decomposition, y_decomposition))
    }

    pub unsafe fn from_xy_unchecked(
        x: FieldElement<'a, E, G::Base>,
        y: FieldElement<'a, E, G::Base>,
    ) -> Self {
        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => {
                Some(G::from_xy_unchecked(x, y))
            },
            _ => {
                None
            }
        };

        let new = Self {x, y, value };
        new
    }

    pub fn constant(value: G, params: &'a RnsParameters<E, G::Base>) -> Self {
        assert!(!value.is_zero());
        let (x, y) = value.into_xy_unchecked();
        let x = FieldElement::constant(x, params);
        let y = FieldElement::constant(y, params);
        let new = Self { x, y, value: Some(value) };

        new
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

    pub fn enforce_if_normalized<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.x.enforce_if_normalized(cs)?;
        self.y.enforce_if_normalized(cs)
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
            value: new_value
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
            value: new_value
        };

        Ok(new)
    }

    pub fn select<CS>(cs: &mut CS, flag: &Boolean, first: &Self, second: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let first_value = first.get_value();
        let second_value = second.get_value();
        let x = FieldElement::select(cs, flag, &first.x, &second.x)?;
        let y = FieldElement::select(cs, flag, &first.y, &second.y)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None
        };
        let selected = AffinePoint { x, y, value };

        Ok(selected)
    }

    #[track_caller]
    pub fn is_on_curve_for_zero_a<CS: ConstraintSystem<E>>(&self, cs: &mut CS, curve_b: G::Base
    ) -> Result<Boolean, SynthesisError> {
        let params = &self.x.representation_params;
        assert_eq!(curve_b, G::b_coeff());
        let b = FieldElement::constant(curve_b, params);

        let mut lhs = self.y.square(cs)?;
        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let mut rhs = x_cubed.add(cs, &b)?;

        FieldElement::equals(cs, &mut lhs, &mut rhs)
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
        let other_x_minus_this_x = other.x.add(cs, &self.x)?;
        let chain = FieldElementsChain::new().add_pos_term(&other.y).add_neg_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, &chain, &other_x_minus_this_x)?;
        
        // lambda^2 + (-x' - x)
        let chain = FieldElementsChain::new().add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, &chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.x.sub(cs, &new_x)?;
        let chain = FieldElementsChain::new().add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, &chain)?;

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
            value: new_value
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
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;

        let other_x_minus_this_x = other.x.add(cs, &self.x)?;
        let chain = FieldElementsChain::new().add_pos_term(&other.y).add_pos_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, &chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let chain = FieldElementsChain::new().add_neg_term(&self.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, &chain)?;

        // lambda * -(x - new_x) + (- y)
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let chain = FieldElementsChain::new().add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &new_x_minus_this_x, &chain)?;

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
            value: new_value
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
        let chain = FieldElementsChain::new().add_pos_term(&other.y).add_neg_term(&self.y); 
        let lambda = FieldElement::div_with_chain(cs, &chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let chain = FieldElementsChain::new().add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, &chain)?;
        
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let two_y = self.y.double(cs)?;
        let t0 = two_y.div(cs, &new_x_minus_this_x)?;
        let t1 = lambda.add(cs, &t0)?;
        let chain = FieldElementsChain::new().add_neg_term(&self.x).add_neg_term(&new_x);
        let new_x = t1.square_with_chain(cs, &chain)?;

        let new_x_minus_x= new_x.sub(cs, &self.x)?;
        let chain = FieldElementsChain::new().add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &t1, &new_x_minus_x, &chain)?;

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
            value: new_value
        };
        Ok(new)
    }

    #[track_caller]
    pub fn mul_by_scalar<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, scalar: &RangeCheckDecomposition<E>, bit_limit: Option<usize>
    ) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_total_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
       
        let params = self.x.representation_params;
        let this_value = self.get_value();
        let this_copy = self.clone();

        // scalar is not constant, so we first decompose it
        let entries = decompose_into_skewed_representation(cs, &scalar)?;
        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"
        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log::<E>(
            &crate::constants::MULTIEXP_DST[..], 
            1
        )[0];

        let generator = Self::constant(offset_generator, params);

        let (mut acc, (this, _)) = self.add_unequal(cs, generator)?;

        let mut x = this.x;
        let y = this.y;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];

        let mut num_doubles = 0;

        let (minus_y, y) = y.negated(cs)?;

        for e in entries_without_first_and_last.iter() {
            let (selected_y, _) = FieldElement::select(cs, e, minus_y.clone(), y.clone())?;  
  
            let t_value = match (this_value, e.get_value()) {
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
                x: x,
                y: selected_y,
                value: t_value
            };

            let (new_acc, (_, t)) = acc.double_and_add(cs, t)?;

            num_doubles += 1;
            acc = new_acc;
            x = t.x;
        }

        let (with_skew, (acc, this)) = acc.sub_unequal(cs, this_copy)?;

        let last_entry = entries.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;

        let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
            (Some(s_value), Some(a_value), Some(b)) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            },
            _ => None
        };

        let (final_acc_x, _) = FieldElement::select(cs, last_entry, with_skew_x, acc_x)?;
        let (final_acc_y, _) = FieldElement::select(cs, last_entry, with_skew_y, acc_y)?;

        let shift = BigUint::from(1u64) << num_doubles;
        let as_scalar_repr = biguint_to_repr::<E::Fr>(shift);
        let offset_value = offset_generator.mul(as_scalar_repr).into_affine();
        let offset = Self::constant(offset_value, params);

        let result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value
        };

        let (result, _) = result.sub_unequal(cs, offset)?;

        Ok((result, this))
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

// in terms of cost in constraints computing skewed_wnaf is the same as computing traditional 
// binary representation
#[track_caller]
fn compute_skewed_naf_representation(value: &Option<BigUint>, bit_limit: usize) -> Vec<Option<bool>> {
    assert!(bit_limit > 0);
    if value.is_none() {
        return vec![None; bit_limit+1];
    }

    let value = value.as_ref().unwrap();
    let mut bits = Vec::with_capacity(bit_limit+1);
    for i in 0..bit_limit as u64 {
        let b = value.bit(i);
        bits.push(Some(!b));
    }
    bits.push(Some(false));
    bits
}

#[track_caller]
fn construct_skewed_bit_term<E: Engine>(c: &Boolean, two: &E::Fr) -> Term<E> {
    // for bit c construct 1 - 2 * c
    let mut contribution = Term::from_boolean(c);
    contribution.scale(two);
    contribution.negate();
    contribution.add_constant(&E::Fr::one());
    contribution
}


#[track_caller]
pub fn decompose_into_skewed_representation<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, decomposition: RangeCheckDecomposition<E>
) -> Result<Vec<Boolean>, SynthesisError> {
    let num_of_chunks = decomposition.get_num_chunks();
    let chunk_bitlen = decomposition.get_chunk_bitlen();
    let total_bitlen = chunk_bitlen * num_of_chunks;
    let is_single_chunk = num_of_chunks == 1;
    
    let bit_values = compute_skewed_naf_representation(&decomposition.get_total_value(), total_bitlen);
    let mut bits = Vec::<Boolean>::with_capacity(bit_values.len());
    for (_is_first, is_last, bit) in bit_values.into_iter().identify_first_last() {
        let elem = if is_last { 
            Boolean::Constant(bit.unwrap()) 
        } else {
            Boolean::from(AllocatedBit::alloc(cs, bit)?)
        };

        bits.push(elem)
    }

    let shifts = compute_shifts::<E::Fr>();
    let two = shifts[1].clone();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let mut limb_shift_negated = shifts[chunk_bitlen]; 
    limb_shift_negated.negate();

    for (chunk_idx, chunk) in decomposition.get_vars().iter().enumerate() {   
        let is_first = chunk_idx == 0;
        let is_last = chunk_idx == num_of_chunks - 1;
        let mut start_offset = chunk_idx * chunk_bitlen;
        let mut end_offset = (chunk_idx + 1) * chunk_bitlen;  

        let mut reconstructed = Term::<E>::zero();
        if is_first {
            // add y_{-1}
            let skew_bit = bits[0];
            // we only subtract if true
            let mut contribution = Term::from_boolean(&skew_bit);
            contribution.negate();
            reconstructed = reconstructed.add(cs, &contribution)?;
            start_offset += 1;
        }
        if is_last {
            end_offset += 1;
        }

        let bits_slice = &bits[start_offset..end_offset];
        let mut chunks = bits_slice.chunks_exact(2);

        // we should add +1 if bit is false or add -1 if bit is true,
        // so we make false = 0 -> 1 - 2*0 = 1
        // true = 1 -> 1 - 2*1 = -1
        for c in &mut chunks {
            reconstructed.scale(&two);
            reconstructed.scale(&two);

            let mut high_contribution = construct_skewed_bit_term::<E>(&c[0], &two);
            high_contribution.scale(&two);
            let low_contribution = construct_skewed_bit_term::<E>(&c[1], &two);
            reconstructed = reconstructed.add_multiple(cs, &[high_contribution, low_contribution])?;
        }

        let remainder = chunks.remainder();
        if remainder.len() == 1 {
            let last = &remainder[0];
            reconstructed.scale(&two);
            let contribution = construct_skewed_bit_term::<E>(&last, &two);
            reconstructed = reconstructed.add(cs, &contribution)?;
        }
        
        // y_ch_0 = x_ch_0 - 2^l
        // for every intermidiate chunk: y_ch_i = x_ch_i - 2^l + 1
        // y_ch_l = x_ch_k + 1
        // this is equal to the following: 
        // if not first_limb: y_ch += 1, if not last limb: y_ch -= 2^l
        if !is_single_chunk && !is_first {
            let contribution = Term::from_constant(E::Fr::one());
            reconstructed.add(cs, &contribution)?;
        }
        if !is_single_chunk && !is_last {
            let contribution = Term::from_constant(limb_shift_negated);
            reconstructed.add(cs, &contribution)?;
        }

        let as_num = reconstructed.collapse_into_num(cs)?;
        let v = as_num.get_variable();
        v.enforce_equal(cs, chunk)?;
    }

    Ok(bits)
}

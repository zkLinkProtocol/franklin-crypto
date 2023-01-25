use super::*;
use super::bigint::*;
use bellman::CurveProjective;
use num_traits::{Zero, One};
use num_integer::Integer;
use num_derive::FromPrimitive;    
use num_traits::FromPrimitive;
use std::ops::ControlFlow;
use std::os::raw;

use num_bigint::BigUint;
use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use crate::plonk::circuit::byte::Byte;
use crate::plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;
use crate::plonk::circuit::SomeArithmetizable;

use std::sync::Once;
static INIT_IS_ZERO_CHECK: Once = Once::new();
static mut USE_OPT_IS_ZERO_CHECK: bool = false;
static INIT_ENFORCE_EQUAL_CHECK: Once = Once::new();
static mut NUM_BINARY_LIMBS_FOR_ENFORCE_EQUAL_CHECK: usize = 0;

// TODO and NB: the code here is very tight and dense. Every line should be carefully reviewed and double checked

// this variable is used in fma implementation: it is set to the maximal numver of bits on which 
// new_of * shift + /sum_{i+j = k} a[i] * b[j] + \sum addition_elements[k] may overflow the limb width border
// NB: this value is chosen more or less randomly - may be it is better to add some heuristics here
const MAX_INTERMIDIATE_OVERFLOW_WIDTH : usize = 16;
const EXPECTED_NUM_LIMBS_PER_FMA_CYCLE : usize = 2;

// TODO: coarsely is completely unnecessary - get rid of it everywhere!
// There is no problem to pay for one addtional constraint on exact allocation
// TODO: track also if value is normalized

fn get_max_possible_value_for_bit_width(bitwidth: usize) -> BigUint {
    (BigUint::one() << bitwidth) - BigUint::one()
}

// constructs a term t which attests equality of x and y: t is equal to zero if x == y and (x-y)^{-1} otherwise
// required for enforce_zero and equals family of functions
// if flag is set then certificate witness will be zero independent of values of x and y
fn construct_equality_certificate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, x: &Term<E>, y: &Term<E>, flag: bool
) -> Result<Term<E>, SynthesisError>  
{
    let cert_wit = match (x.get_value(), y.get_value()) {
        (Some(x_wit), Some(y_wit)) => {
            let mut tmp = x_wit.clone();
            tmp.sub_assign(&y_wit);
            let res = tmp.inverse().unwrap_or(E::Fr::zero());
            Some(res)
        },
        _ => None,
    };
    let cert_wit = if flag { Some(E::Fr::zero()) } else { cert_wit };

    let all_are_const = x.is_constant() && y.is_constant();
    let cert = if all_are_const { Term::from_constant(cert_wit.unwrap()) } else { Term::allocate(cs, cert_wit)? };

    Ok(cert)
}


// Parameters of the RNS representation of extrinsic (non-native field element)
// Every FieldElement is (by CRT) uniquely represented as a tuple of two residues x_0, x_1 such that
// x = x_0 (mod T = 2^t), x = x_1 (mod E::Fr)
// binary limb representation is of the form:
//      most significat limb is of the form: [cap_bits | msl_bits] 
//      other num_binary_lims - 1 (regular) limbs are of the form: [cap_bits | limb_bits]
// where all of msl_width, capacity_width and limb_width are multiples of range check granularity
// ordinary limb may occupy up to cap_bits + limb_width
// let max_binary_bitlen = (n - 1) * limb_bits + msl_bits + cap_bits
// we chose t to be large enough, so that: 2^(2 * max_binary_bitlen) < native_modulus * 2^t
// this is mostly expolited internally by fma function to prevent overflow modulo T * native_modulus 
// overflow bug is described in: https://hackmd.io/@kilic/S1wze9Ert
// NB: 
//      it seems that we may have better control by introducing msl_capacity_width 
//      which can be different from reg_capacity_width   
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsParameters<E: Engine, F: PrimeField>{
    allow_individual_limb_overflow: bool,
    allow_coarse_allocation_for_temp_values: bool,

    range_check_strategy: RangeConstraintStrategy,
    range_check_granularity: usize,

    pub(crate) num_binary_limbs: usize,
    pub(crate) binary_limb_width: usize,
    msl_width: usize, // hereinafter msl stands for Most Significant Limb

    native_field_modulus: BigUint,
    pub(crate) native_field_modulus_bitlength: usize,
    represented_field_modulus: BigUint,
    pub(crate) represented_field_modulus_bitlength: usize,
    shift_left_by_limb_constant: E::Fr, // is equal to (1 << binary_limb_width)
    
    // these fields are required only for "if_zero" method
    f_char_mod_fr_char: E::Fr, // represented_module % Fr 
    f_char_mod_binary_shift: E::Fr, // represented_module % (1 << binary_limb_width)
    
    // just some random very large value that raw binary value would never overflow
    // we let infty to be 2^t = binary_RNS_module, where t = modulus_bitlen * 2 
    infty: BigUint,

    max_ordinary_limb_val_on_alloc: BigUint,
    max_msl_val_on_alloc_coarsely: BigUint,
    max_msl_val_on_alloc_strict: BigUint,

    _marker_engine: std::marker::PhantomData<E>,
    _marker_fr: std::marker::PhantomData<F>
}

impl<'a, E: Engine, F: PrimeField> RnsParameters<E, F>{
    pub fn new_optimal<CS: ConstraintSystem<E>>(cs: &mut CS, limb_size: usize) -> Self 
    {
        let allow_individual_limb_overflow = true;
        let allow_coarse_allocation_for_temp_values = true;

        let strategy = get_optimal_strategy(cs);
        let range_check_granularity = strategy.get_range_check_granularity();
        assert!(limb_size % range_check_granularity == 0, "limb size is not a multiple of range check quant");

        let native_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let native_field_modulus_bitlength = native_field_modulus.bits() as usize;
        let represented_field_modulus = repr_to_biguint::<F>(&F::char());
        let represented_field_modulus_bitlength = represented_field_modulus.bits() as usize;
        let num_binary_limbs = (represented_field_modulus_bitlength + limb_size - 1) / limb_size;     
        
        let rem = represented_field_modulus_bitlength % limb_size;
        let msl_width = if rem == 0 { limb_size } else { rem };

        let shift = BigUint::one() << limb_size;
        let shift_left_by_limb_constant = biguint_to_fe::<E::Fr>(shift.clone());
        
        let f_char_mod_fr_char = biguint_to_fe::<E::Fr>(represented_field_modulus.clone());
        let f_char_mod_binary_shift = biguint_to_fe::<E::Fr>(represented_field_modulus.clone() % shift);
       
        // we chose t to be large enough, so that: 2^(2 * max_binary_bitlen) < native_field_modulus * 2^t
        let t = represented_field_modulus_bitlength * 2usize;
        let infty = BigUint::one() << t;

        let max_ordinary_limb_val_on_alloc = get_max_possible_value_for_bit_width(limb_size);
        let max_msl_val_on_alloc_coarsely = get_max_possible_value_for_bit_width(msl_width);
        let max_msl_val_on_alloc_strict = represented_field_modulus.clone() >> ((num_binary_limbs - 1) * limb_size);
        
        RnsParameters::<E, F> {
            allow_individual_limb_overflow,
            allow_coarse_allocation_for_temp_values,
            num_binary_limbs,
            range_check_strategy: strategy,
            range_check_granularity,
            binary_limb_width: limb_size,
            msl_width,
            native_field_modulus,
            native_field_modulus_bitlength,
            represented_field_modulus,
            represented_field_modulus_bitlength,
            shift_left_by_limb_constant,
            f_char_mod_fr_char,
            f_char_mod_binary_shift,
            infty,
            max_ordinary_limb_val_on_alloc,
            max_msl_val_on_alloc_coarsely,
            max_msl_val_on_alloc_strict,
            _marker_engine: std::marker::PhantomData::<E>,
            _marker_fr: std::marker::PhantomData::<F>
        }
    }
}


// Simple term and bit counter/max value counter that we can update
#[derive(Clone, Debug)]
pub struct Limb<E: Engine> {
    pub term: Term<E>,
    pub max_value: BigUint
}

impl<E: Engine> Limb<E> {
    pub fn new(term: Term<E>, max_value: BigUint) -> Self {
        Self { term, max_value }
    }

    pub fn constant_from_biguint(value: BigUint) -> Self {
        let v = biguint_to_fe(value.clone());
        let term = Term::<E>::from_constant(v);
        Self { term, max_value: value }
    }

    pub fn constant_from_field_value(value: E::Fr) -> Self {
        let term = Term::<E>::from_constant(value);
        Self {
            term,
            max_value: fe_to_biguint(&value)
        }
    }

    pub fn max_value(&self) -> BigUint {
        if self.is_constant() { self.get_value_as_biguint().unwrap() } else { self.max_value.clone() }
    }

    pub fn get_value_as_biguint(&self) -> Option<BigUint> {
        some_fe_to_biguint(&self.term.get_value())
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.term.get_value()
    }

    pub fn zero() -> Self {
        Limb::<E> {
            term: Term::<E>::zero(),
            max_value: BigUint::zero()
        }
    }

    pub fn one() -> Self {
        Limb::<E> {
            term: Term::<E>::from_constant(E::Fr::one()),
            max_value: BigUint::one()
        }
    }

    pub fn is_constant(&self) -> bool {
        self.term.is_constant()
    }

    pub fn get_max_bitlen(&self) -> usize {
        self.max_value().bits() as usize
    }

    pub fn circuit_eq(&self, other: &Self) -> bool {
        self.term.circuit_eq(&other.term)
    }
}


fn get_limbs_in_diapason<'a, E: Engine>(
    x: &'a Vec<Limb<E>>, start: usize, end: usize
) -> impl Iterator<Item = (usize, &'a Limb<E>)> + 'a {
    let iter = x.iter().enumerate().filter(move |(i, _x)| { *i >= start && *i < end});
    iter
}

fn get_limbs_product_in_diapason<'a, E: Engine>(
    x: &'a Vec<Limb<E>>, y: &'a Vec<Limb<E>>, start: usize, end: usize
) -> impl Iterator<Item = (usize, &'a Limb<E>, &'a Limb<E>)> + 'a {
    let iter = itertools::iproduct!(x.iter().enumerate(), y.iter().enumerate()).filter_map(move |x| {
        let ((i, x_limb), (j, y_limb)) = x;
        if i + j >= start && i + j < end {
            Some((i + j, x_limb, y_limb))
        }
        else {
            None
        }
    });
    
    iter
}


#[repr(u8)]
#[derive(Clone, Debug, PartialEq)]
#[derive(FromPrimitive)]
pub enum ReductionStatus {
    // we say that FieldElement x is normalized if there are no overflowed chunks and 0 <= x < F::chat
    // the only way to make nonconstant x normalized is to explicitely call normalize function on it
    // NB: even freshly allocated elements are not normalized! (except for unsafe unchecked allocation)
    // all constants are always in normalized form  
    Normalized,
    // FieldElement x is in Loose reduction status if there are no oberflowed chunks and 0 <= x < ceil[log_2(F::char)]
    // in other words x may be greater than F::Char but doesn't have more bits in representation
    // freshly allocated FieldElements are loosely reduced, results of mul, div, inverse, and fma are also in this form
    Loose,
    // results of addition, subtraction and negation are in this form
    Unreduced
}

impl Copy for ReductionStatus {}


#[derive(Clone, Debug)]
pub struct FieldElement<'a, E: Engine, F: PrimeField>{
    pub binary_limbs: Vec<Limb<E>>,
    base_field_limb: Term<E>,
    pub(crate) representation_params: &'a RnsParameters<E, F>,
    value: Option<F>,
    reduction_status: ReductionStatus,
}

impl<'a, E: Engine, F: PrimeField> PartialEq for FieldElement<'a, E, F>{
    fn eq(&self, other: &Self) -> bool {
        assert!(Self::check_params_equivalence(self, other));
        let are_equal = self.binary_limbs.iter().zip(other.binary_limbs.iter()).all(|(a, b)| {
            a.term == b.term
        });
        are_equal && self.base_field_limb == other.base_field_limb
    }
}
impl<'a, E: Engine, F: PrimeField> Eq for FieldElement<'a, E, F> {}


impl<'a, E: Engine, F: PrimeField> std::fmt::Display for FieldElement<'a, E, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FieldElement {{ ")?;
        write!(f, "Modulus = {}, ", F::char())?;
        write!(f, "Value = {:?}, ", self.get_field_value())?;
        if let Some(v) = self.get_raw_value() {
            write!(f, "Value from binary limbs = {}, ", v.to_str_radix(16))?;
        } else {
            write!(f, "Value from binary limbs = None, ")?;
        }
        for (i, l) in self.binary_limbs.iter().enumerate() {
            write!(
                f, "Limb {}: value = {:?}, max_value = {}, bits = {}, ", 
                i, l.term.get_value(), l.max_value.to_str_radix(16), l.max_value.bits()
            )?;
        }
        write!(f, "Base field limb value = {:?} ", self.base_field_limb.get_value())?;
        writeln!(f, "}}")
    }
}


pub struct FieldElementsChain<'a, E: Engine, F: PrimeField> {
    pub elems_to_add: Vec<FieldElement<'a, E, F>>,
    pub elems_to_sub: Vec<FieldElement<'a, E, F>> 
}

impl<'a, E: Engine, F: PrimeField> FieldElementsChain<'a, E, F> {
    pub fn new() -> Self {
        FieldElementsChain::<E, F> {
            elems_to_add: vec![],
            elems_to_sub: vec![] 
        }
    }
    
    pub fn add_pos_term(&mut self, elem: &FieldElement<'a, E, F>) -> &mut Self {
        self.elems_to_add.push(elem.clone());
        self
    } 

    pub fn add_neg_term(&mut self, elem: &FieldElement<'a, E, F>) -> &mut Self {
        self.elems_to_sub.push(elem.clone());
        self
    }

    pub fn is_constant(&self) -> bool {
        self.elems_to_add.iter().chain(self.elems_to_sub.iter()).all(|x| x.is_constant())
    }

    pub fn get_field_value(&self) -> Option<F> {
        let pos_total_sum = self.elems_to_add.iter().fold(Some(F::zero()), |acc, x| acc.add(&x.get_field_value()));
        let neg_total_sum = self.elems_to_sub.iter().fold(Some(F::zero()), |acc, x| acc.add(&x.get_field_value()));
        pos_total_sum.sub(&neg_total_sum)
    }

    pub fn get_maximal_positive_stored_value(&self) -> BigUint {
        self.elems_to_add.iter().fold(BigUint::zero(), |acc, x| acc + x.get_maximal_possible_stored_value())
    } 

    pub fn get_maximal_negative_stored_value(&self) -> BigUint {
        self.elems_to_sub.iter().fold(BigUint::zero(), |acc, x| acc + x.get_maximal_possible_stored_value())
    }

    pub fn negate(self) -> Self {
        let FieldElementsChain { elems_to_add, elems_to_sub } = self;
        FieldElementsChain {
            elems_to_add: elems_to_sub,
            elems_to_sub: elems_to_add
        }
    } 

    fn add_raw_value_to_accumulator(&self, init_acc_val: Option<BigUint>) -> Option<BigUint> {
        if init_acc_val.is_none() {
            return None;
        }

        let final_acc_value = self.elems_to_add.iter().map(|x| (x, true)).chain(
            self.elems_to_sub.iter().map(|x| (x, false))
        ) .try_fold(init_acc_val.unwrap(), |prev, (x, is_pos_term)| {
            if let Some(val) = x.get_raw_value() {
                let next = match is_pos_term { 
                    true => prev + val,
                    false => {
                        assert!(prev >= val);
                        prev - val
                    },
                };
                ControlFlow::Continue(next)
            } else {
                ControlFlow::Break(prev)
            }
        });
        match final_acc_value {
            ControlFlow::Break(_) => None,
            ControlFlow::Continue(x) => Some(x)
        }
    } 

    pub fn len(&self) -> usize {
        self.elems_to_add.len() + self.elems_to_sub.len()
    }
}


pub fn split_into_limbs<E: Engine, F: PrimeField>(value: F, params: &RnsParameters<E, F>) -> (Vec<E::Fr>, E::Fr) 
{
    let value_as_bigint = fe_to_biguint(&value);
    let binary_limb_values = split_into_fixed_number_of_limbs(
        value_as_bigint, params.binary_limb_width, params.num_binary_limbs
    );
    assert_eq!(binary_limb_values.len(), params.num_binary_limbs);

    let base_limb = fe_to_biguint(&value) % &params.native_field_modulus;
    let base_limb = biguint_to_fe::<E::Fr>(base_limb);

    let binary_limbs: Vec<E::Fr> = binary_limb_values.into_iter().map(|el| biguint_to_fe::<E::Fr>(el)).collect();
    assert_eq!(binary_limbs.len(), params.num_binary_limbs);

    return (binary_limbs, base_limb);
}

pub fn value_to_limbs<E, F>(value: Option<F>, params: &RnsParameters<E, F>) -> (Vec<Option<E::Fr>>, Option<E::Fr>) 
where E: Engine, F: PrimeField
{
    let num_limbs = params.num_binary_limbs;

    match value {
        Some(value) => {
            let (binary_limbs, base_limb) = split_into_limbs(value, params);
            let binary_limbs: Vec<Option<E::Fr>> = binary_limbs.into_iter().map(|el| Some(el)).collect();
            assert_eq!(binary_limbs.len(), params.num_binary_limbs);
            return (binary_limbs, Some(base_limb));
        },
        None => {
            return (vec![None; num_limbs], None);
        }
    }
}

#[track_caller]
pub fn slice_some_into_limbs_non_exact(
    value: Option<BigUint>, max_width: usize, limb_width: usize
) -> (Vec<Option<BigUint>>, usize) 
{
    let rem = max_width % limb_width;
    let msl_bit_width = if rem == 0 { limb_width } else { rem };
    let num_limbs = (max_width + limb_width - 1) / limb_width;
    let limbs = split_some_into_fixed_number_of_limbs(value, limb_width, num_limbs);
    
    (limbs, msl_bit_width)
}

#[track_caller]
pub fn slice_into_limbs_non_exact(value: BigUint, total_width: usize, limb_width: usize) -> (Vec<BigUint>, usize) {
    // here msl stands for Most Significant Limb
    let (chunks, msl_width) = slice_some_into_limbs_non_exact(Some(value), total_width, limb_width);
    let chunks : Vec<BigUint> = chunks.into_iter().map(|x| x.unwrap()).collect();
    (chunks, msl_width) 
} 


impl<'a, E: Engine, F: PrimeField> FieldElement<'a, E, F> {
    // check that self and other are actuall the same circuit variables!
    #[track_caller]
    pub fn circuit_eq(&self, other: &Self) -> bool {
        let mut is_circuit_eq = self.base_field_limb.circuit_eq(&other.base_field_limb);
        for (a, b) in self.binary_limbs.iter().zip(other.binary_limbs.iter()) {
            is_circuit_eq &= a.circuit_eq(b)
        }
        is_circuit_eq
    }

    // we do not do the range check for the limbs: 
    // this function assumes that every limb is at most params.binary_limb_bitwidth bits long
    // and the maximal_stored_value < F::char
    #[track_caller]
    pub unsafe fn alloc_from_limbs_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS, raw_limbs: &[Num<E>], params: &'a RnsParameters<E, F>, is_normalized: bool
    ) -> Result<Self, SynthesisError> {
        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);
        let msl_max_val = &params.max_msl_val_on_alloc_strict;
        let ord_max_val = &params.max_ordinary_limb_val_on_alloc;

        let mut base_field_lc = LinearCombination::zero();
        let shift_constant = params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        for (_is_first, is_last, raw_limb) in raw_limbs.iter().identify_first_last() {
            let limb = match raw_limb {
                Num::Constant(cnst) => Limb::<E>::constant_from_field_value(*cnst),
                Num::Variable(var) => {
                    let term = Term::<E>::from_allocated_num(var.clone());
                    let max_value = if is_last { msl_max_val.clone() } else { ord_max_val.clone() };
                    let limb = Limb::<E>::new(term, max_value.clone());
                    limb
                }
            };
            binary_limbs_allocated.push(limb);

            base_field_lc.add_assign_number_with_coeff(raw_limb, current_constant);
            current_constant.mul_assign(&shift_constant);
        }
        binary_limbs_allocated.resize(params.num_binary_limbs, Limb::zero());
        
        let base_field_limb_num = base_field_lc.into_num(cs)?;
        let base_field_term = Term::<E>::from_num(base_field_limb_num);

        let total_value = raw_limbs.iter().rev().fold(Some(BigUint::zero()), |acc, &x| {
            match (acc, x.get_value()) {
                (Some(mut acc), Some(fr)) => {
                    acc <<= params.binary_limb_width;
                    acc += fe_to_biguint(&fr);
                    Some(acc)
                },
                (_, _) => None,
            }
        }).map(|x| biguint_to_fe::<F>(x));
        
        let reduction_status = if is_normalized { ReductionStatus::Normalized } else { ReductionStatus::Unreduced };
        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: total_value,
            reduction_status
        };
        
        Ok(new)
    }

    #[track_caller]
    fn alloc_impl<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, params: &'a RnsParameters<E, F>, 
        coarsely: bool, granularity: Option<usize>
    ) -> Result<(Self, RangeCheckDecomposition<E>), SynthesisError> {
        assert!(bit_width > 0);
        if let Some(v) = value.as_ref() {
            assert!(v.bits() as usize <= bit_width);
        }

        let mut decompositions : Vec<RangeCheckDecomposition<E>> = vec![];
        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);

        let mut base_field_lc = LinearCombination::<E>::zero();
        let shift_constant = params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        let (limb_values, msl_width) = slice_some_into_limbs_non_exact(
            value.clone(), bit_width, params.binary_limb_width
        );
        let msl_width_padded = if coarsely { round_up(msl_width, params.range_check_granularity) } else { msl_width };
        let msl_max_val = get_max_possible_value_for_bit_width(msl_width_padded);

        for (_is_first, is_last, value) in limb_values.into_iter().identify_first_last() 
        {
            let value_as_fe = some_biguint_to_fe::<E::Fr>(&value);
            let a = AllocatedNum::alloc(cs, || Ok(*value_as_fe.get()?))?;

            let max_value = if is_last { msl_max_val.clone() } else { params.max_ordinary_limb_val_on_alloc.clone() };
            let bitlength = if is_last { msl_width } else { params.binary_limb_width };
            let decomposition = constraint_bit_length_ext_with_strategy(
                cs, &a, bitlength, params.range_check_strategy, coarsely, granularity
            )?;
            decompositions.push(decomposition);

            let term = Term::<E>::from_allocated_num(a.clone());
            let limb = Limb::<E>::new(term, max_value);

            binary_limbs_allocated.push(limb);

            base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
            current_constant.mul_assign(&shift_constant);
        }
        if binary_limbs_allocated.len() < params.num_binary_limbs {
            binary_limbs_allocated.resize(params.num_binary_limbs, Limb::zero());
        }
        
        let base_field_limb_num = base_field_lc.into_num(cs)?;
        let base_field_term = Term::<E>::from_num(base_field_limb_num);
        let field_value = value.map(|x| biguint_to_fe::<F>(x));
        
        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: field_value,
            reduction_status: ReductionStatus::Loose
        };
        let total_decomposition = RangeCheckDecomposition::combine(&decompositions);
        
        Ok((new, total_decomposition))
    }

    // coarsely allocate from bytes
    // #[track_caller]
    // fn from_bytes<CS: ConstraintSystem<E>>(
    //     cs: &mut CS, bytes: Vec<Byte<E>>, params: &'a RnsParameters<E, F>, 
    // ) -> Result<(Self, RangeCheckDecomposition<E>), SynthesisError> {
    //     let total_num_nonzero_bytes = (params.represented_field_modulus_bitlength + 7) / 8;
    //     let bytes_per_limb = params.binary_limb_width / 8;
    //     assert_eq!(params.binary_limb_width % 8, 0);

    //     let mut idx = 0;
    //     let mut value = Some(BigUint::zero());
    //     let mut base_field_lc = LinearCombination::<E>::zero();
    //     let byte_offset = u64_to_fe(8);

    //     for byte in bytes.iter().skip(total_num_nonzero_bytes) {
    //         Num::enforce_equal(cs, &mut byte.inner, &Num::zero());
    //     }
    //     while idx < total_num_nonzero_bytes {
    //         let slice_len = std::min(bytes_per_limb, total_num_nonzero_bytes - i);
    //         let mut binary_limb_lc = LinearCombination::zero();
    //         for (idx, byte) in bytes[idx..idx+slice_len].iter().enumerate() {

    //         }
    //     }
      



    //     let shift_constant = params.shift_left_by_limb_constant;
    //     let mut current_constant = E::Fr::one();

    //     let (limb_values, msl_width) = slice_some_into_limbs_non_exact(
    //         value.clone(), bit_width, params.binary_limb_width
    //     );
    //     let msl_width_padded = if coarsely { round_up(msl_width, params.range_check_granularity) } else { msl_width };
    //     let msl_max_val = get_max_possible_value_for_bit_width(msl_width_padded);

    //     for (_is_first, is_last, value) in limb_values.into_iter().identify_first_last() 
    //     {
    //         let value_as_fe = some_biguint_to_fe::<E::Fr>(&value);
    //         let a = AllocatedNum::alloc(cs, || Ok(*value_as_fe.get()?))?;

    //         let max_value = if is_last { msl_max_val.clone() } else { params.max_ordinary_limb_val_on_alloc.clone() };
    //         let bitlength = if is_last { msl_width } else { params.binary_limb_width };
    //         let decomposition = constraint_bit_length_ext_with_strategy(
    //             cs, &a, bitlength, params.range_check_strategy, coarsely, granularity
    //         )?;
    //         decompositions.push(decomposition);

    //         let term = Term::<E>::from_allocated_num(a.clone());
    //         let limb = Limb::<E>::new(term, max_value);

    //         binary_limbs_allocated.push(limb);

    //         base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
    //         current_constant.mul_assign(&shift_constant);
    //     }
    //     if binary_limbs_allocated.len() < params.num_binary_limbs {
    //         binary_limbs_allocated.resize(params.num_binary_limbs, Limb::zero());
    //     }
        
    //     let base_field_limb_num = base_field_lc.into_num(cs)?;
    //     let base_field_term = Term::<E>::from_num(base_field_limb_num);
    //     let field_value = value.map(|x| biguint_to_fe::<F>(x));
        
    //     let new = Self {
    //         binary_limbs: binary_limbs_allocated,
    //         base_field_limb: base_field_term,
    //         representation_params: params,
    //         value: field_value,
    //         reduction_status: ReductionStatus::Loose
    //     };
    //     let total_decomposition = RangeCheckDecomposition::combine(&decompositions);
        
    //     Ok((new, total_decomposition))
    // }

    // NB: we do not check for normalization on allocation
    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (new, _decomposition) = Self::alloc_ext(cs, value, params)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>
    ) -> Result<(Self, RangeCheckDecomposition<E>), SynthesisError>  
    {
        let bit_width = params.represented_field_modulus_bitlength;
        let value_as_biguint = value.map(|x| fe_to_biguint(&x));
        Self::alloc_impl(cs, value_as_biguint, bit_width, params, false, None)
    }

    #[track_caller]
    pub(crate) fn alloc_for_known_bitwidth<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, params: &'a RnsParameters<E, F>, coarsely: bool
    ) -> Result<Self, SynthesisError> {
        let (val, _decomposition) = Self::alloc_impl(cs, value, bit_width, params, coarsely, None)?;
        Ok(val)
    }

    #[track_caller]
    pub(crate) fn alloc_for_known_bitwidth_with_custom_range_check_granularity<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, 
        params: &'a RnsParameters<E, F>, granularity: usize
    ) -> Result<(Self, RangeCheckDecomposition<E>), SynthesisError> {
        assert_eq!(params.binary_limb_width % granularity, 0);
        Self::alloc_impl(cs, value, bit_width, params, false, Some(granularity))
    }

    pub(crate) fn split_const_into_limbs(value: BigUint, params: &'a RnsParameters<E, F>) -> Vec<Limb<E>> {
        let binary_limb_values = split_into_fixed_number_of_limbs(
            value, params.binary_limb_width, params.num_binary_limbs
        );
        let mut binary_limbs = Vec::with_capacity(binary_limb_values.len());
        for l in binary_limb_values.into_iter()
        {
            let f = biguint_to_fe(l.clone());
            let term = Term::<E>::from_constant(f);
            let limb = Limb::<E>::new(term, l);
            binary_limbs.push(limb);
        }
        binary_limbs
    }

    pub fn constant(v: F, params: &'a RnsParameters<E, F>) -> Self {
        let value = fe_to_biguint(&v);
        let base_limb_value = value.clone() % &params.native_field_modulus;
        let base_limb = biguint_to_fe::<E::Fr>(base_limb_value.clone());
        let base_limb = Term::<E>::from_constant(base_limb);
        assert_eq!(fe_to_biguint(&v) % &params.native_field_modulus, fe_to_biguint(&base_limb.get_value().unwrap()));
        let binary_limbs_allocated = Self::split_const_into_limbs(value, params);

        Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_limb,
            representation_params: params,
            value: Some(v),
            reduction_status: ReductionStatus::Normalized
        }
    }

    pub fn zero(
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let zero_limb = Limb::zero();
        let binary_limbs = vec![zero_limb.clone(); params.num_binary_limbs];
    
        Self {
            binary_limbs: binary_limbs,
            base_field_limb: Term::<E>::from_constant(E::Fr::zero()),
            representation_params: params,
            value: Some(F::zero()),
            reduction_status: ReductionStatus::Normalized
        }
    }

    pub fn one(
        params: &'a RnsParameters<E, F>
    ) -> Self {
        let one_limb = Limb::one();
        let zero_limb = Limb::zero();

        let mut binary_limbs = Vec::with_capacity(params.num_binary_limbs);
        binary_limbs.push(one_limb);
        binary_limbs.resize(params.num_binary_limbs, zero_limb.clone());
    
        Self {
            binary_limbs: binary_limbs,
            base_field_limb: Term::<E>::from_constant(E::Fr::one()),
            representation_params: params,
            value: Some(F::one()),
            reduction_status: ReductionStatus::Normalized
        }
    }

    // return current value unreduced
    pub fn get_raw_value(&self) -> Option<BigUint> {
        let shift = self.representation_params.binary_limb_width;
        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            if let Some(l) = l.get_value_as_biguint() {
                result <<= shift;
                result += l;
            } else {
                return None;
            }
        }
        Some(result)
    }

    pub fn get_field_value(&self) -> Option<F> {
        self.value
    }

    pub fn is_constant(&self) -> bool {
        for l in self.binary_limbs.iter() {
            if !l.is_constant() {
                return false;
            }
        }
        self.base_field_limb.is_constant()
    }

    // return maximum value based on maximum limb values
    pub fn get_maximal_possible_stored_value(&self) -> BigUint {
        if self.is_constant() {
            self.get_raw_value().unwrap()
        } else {
            let shift = self.representation_params.binary_limb_width;
            let mut result = BigUint::from(0u64);

            for l in self.binary_limbs.iter().rev() {
                result <<= shift;
                result += l.max_value();
            }

            result
        }
    }

    fn check_params_equivalence(a: &Self, b: &Self) -> bool {
        std::ptr::eq(a.representation_params, b.representation_params)
    }

    fn debug_check_value_coherency(&self) -> () {
        let lhs = self.get_field_value().unwrap_or(F::zero());
        let rhs = self.get_raw_value().map(|x| biguint_to_fe::<F>(x)).unwrap_or(F::zero());
        assert_eq!(lhs, rhs);
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        let use_opt_version = unsafe {
            INIT_IS_ZERO_CHECK.call_once(|| {
                // (verifying that k * Fr::modulus != 0 (mod 2^{limb_width}) for all positive values of k, 
                // such that: bitlength(k * Fr::modulus) <= represented_field_modulus_bitlength bits
                let params = self.representation_params;
                let shift = BigUint::one() << params.binary_limb_width;
                if params.native_field_modulus_bitlength == params.represented_field_modulus_bitlength {
                    let mut multiple_of_fr_char = params.native_field_modulus.clone();
                    while multiple_of_fr_char.bits() as usize <= params.represented_field_modulus_bitlength {
                        if (multiple_of_fr_char.clone() % shift.clone()).is_zero() {
                            return;
                        }
                        multiple_of_fr_char += params.native_field_modulus.clone(); 
                    }
                    USE_OPT_IS_ZERO_CHECK = true;
                }
            });
            USE_OPT_IS_ZERO_CHECK
        };

        if use_opt_version {
            self.is_zero_optimized(cs)
        } else {
            self.is_zero_unopt(cs)
        }
    }

    fn is_zero_unopt<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> 
    {
        self.normalize(cs)?;
        let least_significant_binary_limb = self.binary_limbs[0].term.collapse_into_num(cs)?;
        let base_field_limb = self.base_field_limb.collapse_into_num(cs)?;
        self.binary_limbs[0].term = Term::from_num(least_significant_binary_limb.clone());
        self.base_field_limb = Term::from_num(base_field_limb.clone());

        // check if x == 0
        let binary_limb_check = least_significant_binary_limb.is_zero(cs)?;
        let base_field_limb_check = base_field_limb.is_zero(cs)?;
        let is_zero = Boolean::and(cs, &binary_limb_check, &base_field_limb_check)?;
        Ok(is_zero)
    }

    // this method requires x to be either loosely refuced or normalized, if it is in fact not - we do
    // normalization ourselves, and that's why referece is mutable
    fn is_zero_optimized<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Boolean, SynthesisError> 
    {
        let params = self.representation_params;
        let is_normalized = self.reduction_status == ReductionStatus::Normalized;
        self.reduce(cs)?;

        // after reduction the value of x is in interval [0; 2*F) and all limbs occupy exactly limb_width bits
        // (i.e. capacity bits are not involved)
        // so, to test if x is zero we need to consider two cases: x == 0 and x == F
        // x == 0 <=> field_limb == 0 and least_significant_binary_limb == 0 
        // (but we should additionaly check that k * Fr::modulus % 2^{limb_width} != 0 for small positive k)
        // x == F <=> field_limb == F (mod Fr) and least_significal_binary_llimb == F (mod 2^{limb_width})
        // (again, as long as k * Fr::modulus != 0 (mod 2^{limb_width}) for small positive k)
        // the exact range of k to test is determined by the maximal multiple of Fr::modulus which fits into
        // params.represented_field_modulus_bitlength bits
        // if the value was in normalized form from the beginning than checking that
        // field_limb == 0 and least_significant_binary_limb == 0 is enough 
        let least_significant_binary_limb = self.binary_limbs[0].term.collapse_into_num(cs)?;
        let base_field_limb = self.base_field_limb.collapse_into_num(cs)?;
        self.binary_limbs[0].term = Term::from_num(least_significant_binary_limb.clone());
        self.base_field_limb = Term::from_num(base_field_limb.clone());

        // check if x == 0
        let binary_limb_check = least_significant_binary_limb.is_zero(cs)?;
        let base_field_limb_check = base_field_limb.is_zero(cs)?;
        let x_is_raw_zero = Boolean::and(cs, &binary_limb_check, &base_field_limb_check)?;

        //check if x == F::char
        let x_is_raw_modulus = if !is_normalized {
            let f_char_mod_fr_char = Num::Constant(params.f_char_mod_fr_char.clone());
            let f_char_mod_binary_shift = Num::Constant(params.f_char_mod_binary_shift.clone());
            let binary_limb_check = Num::equals(cs, &least_significant_binary_limb, &f_char_mod_binary_shift)?;
            let base_field_limb_check = Num::equals(cs, &base_field_limb, &f_char_mod_fr_char)?;
            let x_is_raw_modulus = Boolean::and(cs, &binary_limb_check, &base_field_limb_check)?;
            x_is_raw_modulus
        } else {
            Boolean::constant(false)
        };

        let is_zero = Boolean::or(cs, &x_is_raw_zero, &x_is_raw_modulus)?;  
        Ok(is_zero)
    }

    #[track_caller]
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError>  
    {
        assert!(Self::check_params_equivalence(first, second));
        match flag {
            Boolean::Constant(c) => {
                if *c { return Ok(first.clone()) } else { return Ok(second.clone()) };
            },
            _ => {},
        };
        if first == second {
            return Ok(first.clone());
        }

        // flag * a + (1-flag) * b = flag * (a-b) + b
        let mut new_binary_limbs = vec![];
        for (l, r) in first.binary_limbs.iter().zip(second.binary_limbs.iter()) 
        {
            // let mut minus_b = r.term.clone();
            // minus_b.negate();
            // let a_minus_b = l.term.add(cs, &minus_b)?;
            // let n = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &r.term)?;
            let n = Term::<E>::conditionally_select(cs, &flag, &l.term, &r.term)?;
            
            let new_max = std::cmp::max(l.max_value(), r.max_value());
            let new_limb = Limb::new(n, new_max);
            new_binary_limbs.push(new_limb);
        }

        // let mut minus_b = second.base_field_limb.clone();
        // minus_b.negate();
        // let a_minus_b = first.base_field_limb.add(cs, &minus_b)?;
        let new_base_limb = Term::<E>::conditionally_select(
            cs, &flag, &first.base_field_limb, &second.base_field_limb
        )?;

        let new_value = if let Some(f) = flag.get_value() {
            if f { first.get_field_value() } else { second.get_field_value() }
        } else {
            None
        };

        let final_reduction_status = match (first.reduction_status, second.reduction_status) {
            (ReductionStatus::Unreduced, _) | (_, ReductionStatus::Unreduced) => ReductionStatus::Unreduced,
            (ReductionStatus::Loose, _) | (_, ReductionStatus::Loose) => ReductionStatus::Loose,
            (ReductionStatus::Normalized, ReductionStatus::Normalized) => ReductionStatus::Normalized
        };

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: first.representation_params,
            reduction_status: final_reduction_status
        };
        Ok(new)
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::zero(&self.representation_params).sub(cs, self)
    }

    // negates if true
    #[deprecated]
    #[track_caller]
    pub fn conditionally_negate_unoptimized<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, flag: &Boolean
    ) -> Result<Self, SynthesisError>  
    {
        if flag.is_constant() {
            if flag.get_value().unwrap() { return self.negate(cs) } else { return Ok(self.clone()) }
        };
        let negated = self.negate(cs)?;
        Self::conditionally_select(cs, flag, &negated, self)
    }

    #[track_caller]
    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        if flag.is_constant() {
            if flag.get_value().unwrap() { return self.negate(cs) } else { return Ok(self.clone()) }
        };
        if self.is_constant() && self.get_field_value().unwrap().is_zero() {
            return Ok(self.clone())
        }
        
        let max_val = self.get_maximal_possible_stored_value();
        let params = self.representation_params;
        let limbs_max_vals = self.binary_limbs.iter().map(|x| x.max_value()).collect::<Vec<BigUint>>();
        let (multiples_to_add, const_chunks) = Self::subtraction_helper(max_val, limbs_max_vals, params);
        
        // create new limbs
        let mut new_binary_limbs = vec![];
        let flag_term = Term::from_boolean(flag);
        let mut minus_two = E::Fr::one();
        minus_two.double();
        minus_two.negate();
        let iter = itertools::multizip((&self.binary_limbs, const_chunks));

        for (limb, cnst) in iter 
        {
            // new_limb = flag * cnst + (1 - 2*flag) * limb = flag * cnst - 2 * flag * limb + limb
            let constant_as_fe = biguint_to_fe::<E::Fr>(cnst.clone());
            let mut alc = AmplifiedLinearCombination::zero();
            alc.add_assign_term_with_coeff(&flag_term, constant_as_fe.clone());
            alc.add_assign_product_of_terms_with_coeff(&flag_term, &limb.term, minus_two.clone());
            alc.add_assign_term(&limb.term);
            let (res, num_of_gates) = alc.into_num_ext(cs)?;
            assert!(num_of_gates <= 1);

            let new_max_value = cnst;
            let limb = Limb::<E>::new(Term::from_num(res), new_max_value);
            new_binary_limbs.push(limb);
        }

        let residue_to_add = multiples_to_add % &params.native_field_modulus;
        let constant_as_fe = biguint_to_fe::<E::Fr>(residue_to_add.clone());

        let mut alc = AmplifiedLinearCombination::zero();
        alc.add_assign_term_with_coeff(&flag_term, constant_as_fe.clone());
        alc.add_assign_product_of_terms_with_coeff(&flag_term, &self.base_field_limb, minus_two.clone());
        alc.add_assign_term(&self.base_field_limb);
        let (res, num_of_gates) = alc.into_num_ext(cs)?;
        assert!(num_of_gates <= 1);
        let new_field_limb = Term::from_num(res);

        let new_value = match (self.get_field_value(), flag.get_value()) {
            (Some(fr), Some(bit)) => {
                let mut res = fr;
                if bit { res.negate() };
                Some(res)
            },
            _ => None,
        };

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_field_limb,
            value: new_value,
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };
        
        if cfg!(debug_assertions) {
            new.debug_check_value_coherency();
        }
        Ok(new)
    }

    pub fn normalize<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        // if already normalized no nothing - we do not want to normalize twice in a row
        if self.reduction_status == ReductionStatus::Normalized {
            return Ok(());
        }    
        self.reduce(cs)?; 
        self.enforce_if_normalized(cs)
    }

    #[track_caller]
    pub fn reduce<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        if self.reduction_status == ReductionStatus::Unreduced && !self.is_constant() {
            let one = Self::one(self.representation_params);
            let reduced = self.mul(cs, &one)?;
            *self = reduced;
            self.reduction_status = ReductionStatus::Loose;
        }
        Ok(())
    }

    #[track_caller]
    pub fn enforce_if_normalized<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert_ne!(self.reduction_status, ReductionStatus::Unreduced);
        self.reduction_status = ReductionStatus::Normalized;
        if self.is_constant() { return Ok(()) }
        let params = self.representation_params;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        // msl here stands for Most Significant Limb
        let (modulus_limbs, msl_width) = slice_into_limbs_non_exact(
            params.represented_field_modulus.clone(), 
            params.represented_field_modulus_bitlength, params.binary_limb_width
        ); 

        let ordinary_shift = params.shift_left_by_limb_constant;
        let msl_shift = biguint_to_fe::<E::Fr>(BigUint::one() << msl_width);

        let mut borrow = Limb::zero();
        let mut is_const_term = true;
        let iter = self.binary_limbs.iter().zip(modulus_limbs.iter()).identify_first_last();
        for (_is_first, is_last, (l, m)) in  iter {
            // l - borrow - m + new_borrow * shift = r
            // check if l >= borrow + m to fing the value of new_borrow
            let width = if is_last { msl_width } else { params.binary_limb_width };
            let (new_borrow_wit, r_wit) = match (l.get_value_as_biguint(), borrow.get_value_as_biguint()) {
                (Some(l), Some(borrow)) => {
                    if l >= borrow.clone() + m {
                        (Some(false), Some(l - borrow - m))
                    } else {
                        (Some(true), Some((BigUint::one() << width) + l - borrow - m))
                    }
                }
                (_, _) => (None, None)
            }; 
            is_const_term &= l.is_constant(); 
            
            let b = if is_last {
                Boolean::constant(true)
            } else if is_const_term {
                Boolean::constant(new_borrow_wit.unwrap() as bool)
            } else {
                Boolean::Is(AllocatedBit::alloc(cs, new_borrow_wit.map(|x| x as bool))?)
            };
            let new_borrow = Term::<E>::from_boolean(&b);

            let r = if is_const_term {
                Num::Constant(biguint_to_fe::<E::Fr>(r_wit.unwrap()))
            } else {
                let var = AllocatedNum::alloc(cs, || r_wit.map(|x| biguint_to_fe::<E::Fr>(x)).grab())?;
                constraint_bit_length_with_strategy(cs, &var, width, params.range_check_strategy)?;
                Num::Variable(var) 
            };
            let r_term = Term::<E>::from_num(r);

            // enforce constraint: l - borrow - m + new_borrow * shift - r = 0
            let shift = if is_last { msl_shift } else { ordinary_shift };
            let mut lc = LinearCombination::zero();
            lc.add_assign_term(&l.term);
            lc.add_assign_term_with_coeff(&borrow.term, minus_one.clone());
            lc.sub_assign_constant(biguint_to_fe::<E::Fr>(m.clone()));
            lc.add_assign_term_with_coeff(&new_borrow, shift);
            lc.add_assign_term_with_coeff(&r_term, minus_one.clone());
            lc.enforce_zero(cs)?;
            
            borrow = Limb::new(new_borrow, BigUint::one());
        }

        Ok(())
    }

    // helper function used in sub, mul_with_chain and div_with_chain functions:
    // instead of substracting x we compute the least possible multiple of represented_field_modulus = k,
    // such that k - x is nonnegative
    // the function returns k and chunk division of k
    #[track_caller]
    fn subtraction_helper(
        max_val: BigUint, limbs_max_vals: Vec<BigUint>, params: &RnsParameters<E, F>
    ) -> (BigUint, Vec<BigUint>) {
        let modulus = params.represented_field_modulus.clone();
        let rem = max_val.clone() % modulus.clone();
        let to_add = if rem.is_zero() { BigUint::zero() } else { modulus - rem };
        let multiples_to_add_at_least = max_val + to_add.clone();

        let bits_per_limb = params.binary_limb_width;
        let num_limbs = params.num_binary_limbs;
        let chunks_to_add = split_into_fixed_number_of_limbs(to_add, bits_per_limb, num_limbs);
        let mut const_constituent_chunks = Vec::<BigUint>::with_capacity(num_limbs);

        for (left, right) in limbs_max_vals.into_iter().zip(chunks_to_add.into_iter()) {
            const_constituent_chunks.push(left + right);
        }

        if cfg!(debug_assertions) {
            let mut total = BigUint::zero();
            for chunk in const_constituent_chunks.iter().rev() {
                total <<= bits_per_limb;
                total += chunk
            }
            assert_eq!(total, multiples_to_add_at_least)
        }

        (multiples_to_add_at_least, const_constituent_chunks)
    }

    #[track_caller]
    pub fn add_with_reduction<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self, needs_reduction: bool
    ) -> Result<Self, SynthesisError> {
        let params = self.representation_params;
        assert!(Self::check_params_equivalence(self, other));

        if self.is_constant() && other.is_constant() {
            let tmp = self.get_field_value().add(&other.get_field_value());
            let new = Self::constant(tmp.unwrap(), params);
            return Ok(new);
        }
        
        // perform addition without reduction, so it will eventually be reduced later on
        let mut new_binary_limbs = vec![];
        for (l, r) in self.binary_limbs.iter().zip(other.binary_limbs.iter()) 
        {
            let new_term = l.term.add(cs, &r.term)?;
            let new_max_value = l.max_value.clone() + &r.max_value;
            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs.push(limb);
        }
        let new_base_limb = self.base_field_limb.add(cs, &other.base_field_limb)?;
        let new_value = self.get_field_value().add(&other.get_field_value());

        let mut new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };

        if cfg!(debug_assertions) {
            new.debug_check_value_coherency();
        }
        if needs_reduction {
            new.reduce(cs)?;
        }

        Ok(new)
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        self.add_with_reduction(cs, other, !self.representation_params.allow_individual_limb_overflow)
    }

    pub fn conditionally_increment<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError>
    where CS: ConstraintSystem<E> {
        let params = self.representation_params;
        let new_value = self.get_field_value().add(&flag.get_value().map(|x| if x {F::one()} else {F::zero()}));
        
        if self.is_constant() && flag.is_constant() {
            let new = Self::constant(new_value.unwrap(), params);
            return Ok(new);
        }
        
        let mut new_binary_limbs = self.binary_limbs.clone();
        {
            let x = new_binary_limbs[0].clone();
            let new_term = x.term.conditionally_increment(cs, flag)?;
            let new_max_value = x.max_value.clone() + BigUint::one();
            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs[0] = limb;
        };
        let new_base_limb = self.base_field_limb.conditionally_increment(cs, flag)?;
        
        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };

        if cfg!(debug_assertions) {
            new.debug_check_value_coherency();
        }
        
        Ok(new)
    }

    pub fn scale_with_reduction<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, factor: u64, needs_reduction: bool
    ) -> Result<Self, SynthesisError>  
    {
        let params = self.representation_params;
        let factor_as_native_field_elem = u64_to_fe::<E::Fr>(factor);
        let factor_as_represented_field_elem = u64_to_fe::<F>(factor);

        if self.is_constant() {
            let mut tmp = self.get_field_value().unwrap();
            tmp.mul_assign(&factor_as_represented_field_elem);
            let new = Self::constant(tmp, params);
            return Ok(new);
        }

        let mut new_binary_limbs = vec![];
        for l in self.binary_limbs.iter()
        {
            let mut new_term = l.term.clone();
            new_term.scale(&factor_as_native_field_elem);
            let new_max_value = l.max_value.clone() * fe_to_biguint(&factor_as_native_field_elem);

            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs.push(limb);
        }
        let mut new_base_limb = self.base_field_limb.clone();
        new_base_limb.scale(&factor_as_native_field_elem);
        let new_value = self.get_field_value().map(|x| {
            let mut tmp = x;
            tmp.mul_assign(&factor_as_represented_field_elem);
            tmp
        });

        let mut new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };
        
        if needs_reduction {
            new.reduce(cs)?;
        }
        Ok(new)
    }

    pub fn scale<CS: ConstraintSystem<E>>(&self, cs: &mut CS, factor: u64) -> Result<Self, SynthesisError> {
        self.scale_with_reduction(cs, factor, !self.representation_params.allow_individual_limb_overflow)       
    }

    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        self.scale(cs, 2u64)
    }

    pub fn sub_with_reduction<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self, needs_reduction: bool
    ) -> Result<Self, SynthesisError> 
    {
        let params = self.representation_params;
        assert!(Self::check_params_equivalence(self, other));

        if self.is_constant() && other.is_constant() {
            let tmp = self.get_field_value().sub(&other.get_field_value());
            let new = Self::constant(tmp.unwrap(), params);
            return Ok(new);
        }

        if other.is_constant() {
            let tmp = other.get_field_value().negate();
            let other_negated = Self::constant(tmp.unwrap(), params);
            let result = self.add_with_reduction(cs, &other_negated, needs_reduction)?;
            return Ok(result);
        }

        // now we can determine how many moduluses of the represented field we have to add to never underflow
        let max_val = other.get_maximal_possible_stored_value();
        let limbs_max_vals = other.binary_limbs.iter().map(|x| x.max_value()).collect::<Vec<BigUint>>();
        let (multiples_to_add_at_least, const_constituent_chunks) = Self::subtraction_helper(max_val, limbs_max_vals, params);
        
        // create new limbs
        let mut new_binary_limbs = vec![];
        let iter = itertools::multizip((&self.binary_limbs, &other.binary_limbs, const_constituent_chunks));
        for (left, right, cnst) in iter 
        {
            let constant_as_fe = biguint_to_fe::<E::Fr>(cnst.clone());
            
            let mut tmp = left.term.clone();
            tmp.add_constant(&constant_as_fe);
            let res = tmp.sub(cs, &right.term)?;

            let new_max_value = left.max_value() + cnst;
            let limb = Limb::<E>::new(res, new_max_value);
            new_binary_limbs.push(limb);
        }

        let residue_to_add = multiples_to_add_at_least % &params.native_field_modulus;
        let constant_as_fe = biguint_to_fe::<E::Fr>(residue_to_add.clone());

        let mut tmp = self.base_field_limb.clone();
        tmp.add_constant(&constant_as_fe);
        let new_field_limb = tmp.sub(cs, &other.base_field_limb)?;
        let new_value = self.get_field_value().sub(&other.get_field_value());

        let mut new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_field_limb,
            value: new_value,
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };

        if cfg!(debug_assertions) {
            new.debug_check_value_coherency();
        }
        if needs_reduction {
            new.reduce(cs)?;
        }

        Ok(new)
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        self.sub_with_reduction(cs, other, !self.representation_params.allow_individual_limb_overflow)
    }

    pub fn mul<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        Self::mul_with_chain(cs, &self, &other, FieldElementsChain::new())
    }

    pub fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::mul_with_chain(cs, &self, &self, FieldElementsChain::new())
    }

    pub fn square_with_chain<CS>(&self, cs: &mut CS, chain: FieldElementsChain<'a, E, F>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        Self::mul_with_chain(cs, &self, &self, chain)
    }

    pub fn div<CS: ConstraintSystem<E>>(&self, cs: &mut CS, den: &Self) -> Result<Self, SynthesisError> {
        let mut num_chain = FieldElementsChain::new();
        num_chain.add_pos_term(self);
        Self::div_with_chain(cs, num_chain, den)
    }

    pub fn inverse<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut num_chain = FieldElementsChain::new();
        num_chain.add_pos_term(&Self::one(&self.representation_params));
        Self::div_with_chain(cs, num_chain, self)
    }

    #[track_caller]
    pub fn div_with_chain<CS>(cs: &mut CS, chain: FieldElementsChain<'a, E, F>, den: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let params = &den.representation_params;
        // we do chain/den = result mod p, where we assume that den != 0
        assert!(!den.get_field_value().unwrap_or(F::one()).is_zero());

        let numerator_value = chain.get_field_value();
        let den_inverse_value = den.get_field_value().map(|x| x.inverse().expect("denominator is zero"));
        let final_value = numerator_value.mul(&den_inverse_value);
        let all_constants = den.is_constant() && chain.is_constant();
        
        if all_constants {
            let res = Self::constant(final_value.unwrap(), params);
            Ok(res)
        }
        else {
            let res = Self::alloc(cs, final_value, params)?;
            let chain = chain.negate();
            Self::constraint_fma(cs, &res, &den, chain)?;
            Ok(res)
        }
    }

    #[track_caller]
    pub fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self, mut chain: FieldElementsChain<'a, E, F>,
    ) -> Result<Self, SynthesisError> {
        let params = &a.representation_params;
        let mut final_value = a.get_field_value();
        final_value = final_value.mul(&b.get_field_value());
        final_value = final_value.add(&chain.get_field_value());
        let all_constants = a.is_constant() && b.is_constant() && chain.is_constant();
        
        if all_constants {
            let r = Self::constant(final_value.unwrap(), params);
            Ok(r)
        }
        else {
            let r = Self::alloc(cs, final_value, params)?;
            chain.add_neg_term(&r);
            Self::constraint_fma(cs, &a, &b, chain)?;
            Ok(r)
        }
    }

    #[track_caller]
    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        assert!(Self::check_params_equivalence(&this, &other));
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            assert!(a == b);
            return Ok(())
        }
        
        this.reduce(cs)?;
        other.reduce(cs)?;

        // at this point both values a and b are reduced and hence both are in the range [0, 2 * repr_field_modulus)
        // the easiest way to attest equality is to compare corresponding binary limbs, but we can go with less:
        // assume that a == b (mod Fr) and a == b (mod 2^{N * limb_width}) => w.l.o.g. a >= b:
        // a - b == 0 (mod Fr * 2^{N * limb_width})  and 0 <= a - b < 2 * repr_field_modulus
        // and if we enforce that 2 * repr_field_modulus <= Fr * 2^{N * limb_width} than from a == b
        // N here is the number of binary limbs to compare (usually N == 1 for BN and N == 2 for BLS)
        let num_binary_limbs_to_compare = {
            unsafe {
                INIT_ENFORCE_EQUAL_CHECK.call_once(|| {
                    let params = this.representation_params;
                    let mut n = 1;
                    let lhs = params.represented_field_modulus.clone() * 2u64;
                    let mut rhs = params.native_field_modulus.clone() << params.binary_limb_width;
                    while lhs > rhs {
                        n += 1;
                        rhs <<= params.binary_limb_width;
                    }
                    NUM_BINARY_LIMBS_FOR_ENFORCE_EQUAL_CHECK = n;
                });
                NUM_BINARY_LIMBS_FOR_ENFORCE_EQUAL_CHECK
            }
        };
        
        for i in 0..num_binary_limbs_to_compare {
            this.binary_limbs[i].term.enforce_equal(cs, &other.binary_limbs[i].term)?;
        }
        this.base_field_limb.enforce_equal(cs, &other.base_field_limb)?;

        // if field_elements are equal than they are normalized or not simultaneously!
        // hence if we somehow know that one of values is normalized than we may lay the other to be normalized
        let any_is_normalized = {
            this.reduction_status == ReductionStatus::Normalized || 
            other.reduction_status == ReductionStatus::Normalized
        };
        if any_is_normalized {
            this.reduction_status = ReductionStatus::Normalized;
            other.reduction_status = ReductionStatus::Normalized;
        };

        Ok(())
    }

    #[track_caller]
    pub fn enforce_not_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        assert!(Self::check_params_equivalence(&this, &other));   
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            assert!(a != b);
            return Ok(())
        }

        this.normalize(cs)?;
        other.normalize(cs)?;

        // here we know that both variables are reduced, hence there exists a, b such that:
        // a * (this.field_modulus - other.field_modulus) + b * (this.limb_modulus - other.limb_modulus) == 1
        // we can allocate the constraint system for this check on two gates:
        // 1) [a. this.field_modulus, other.field_modulus, tmp]:
        //    a * this.field_modulus - a * other.field_modulus - 1 = tmp
        // 2) [b, this.limb_modulus, other.limb_modulus, tmp]:
        //    b * this.limb_modulus - b * other.limb_modulus + tmp = 0
        let a = construct_equality_certificate(
            cs, &this.binary_limbs[0].term, &other.binary_limbs[0].term, false
        )?;
        let flag = !a.get_value().unwrap_or(E::Fr::zero()).is_zero();
        let b = construct_equality_certificate(cs, &this.base_field_limb, &other.base_field_limb, flag)?;
        
        // construct first_gate:
        let mut lc = AmplifiedLinearCombination::zero();
        lc.add_assign_product_of_terms(&a, &this.binary_limbs[0].term);
        lc.sub_assign_product_of_terms(&a, &other.binary_limbs[0].term);
        lc.sub_assign_constant(E::Fr::one());
        let (tmp, num_gates) = lc.into_num_ext(cs)?;
        assert_eq!(num_gates, 1);

        let mut lc = AmplifiedLinearCombination::zero();
        lc.add_assign_product_of_terms(&b, &this.base_field_limb);
        lc.add_assign_product_of_terms(&b, &other.base_field_limb);
        lc.add_assign_number_with_coeff(&tmp, E::Fr::one());
        let num_gates = lc.enforce_zero(cs)?;
        assert_eq!(num_gates, 1);
            
        return Ok(())
    }

    // TODO: usage by reference here is much more better
    #[track_caller]
    pub fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError> {
        assert!(Self::check_params_equivalence(&this, &other));
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            return Ok(Boolean::constant(a == b));
        }

        this.normalize(cs)?;
        other.normalize(cs)?;

        let mut out_0 = Boolean::zero();
        let mut out_1 = Boolean::zero();
       
        let arr = vec![
            (&this.binary_limbs[0].term, &other.binary_limbs[0].term, &mut out_0), 
            (&this.base_field_limb, &other.base_field_limb, &mut out_1)
        ];
        for (a, b, out) in arr.into_iter() {
            let a = a.collapse_into_num(cs)?;
            let b = b.collapse_into_num(cs)?;
            let equals = Num::equals(cs, &a, &b)?;
            *out = equals;
        }

        let equals = Boolean::and(cs, &out_0, &out_1)?;
        Ok(equals)
    }

    #[track_caller]
    pub fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self, chain: FieldElementsChain<'a, E, F>
    ) -> Result<(), SynthesisError> {  
        assert!(Self::check_params_equivalence(a, b));
        assert!(chain.elems_to_add.iter().all(|x| Self::check_params_equivalence(a, x)));
        assert!(chain.elems_to_sub.iter().all(|x| Self::check_params_equivalence(a, x)));
        let params = &a.representation_params;

        // we are goint to enforce the following relation:
        // a * b + /sum positive_chain_elements - /sum negative_chain_elements = q * p (*)
        // however, there may be situations when the lhs term is negative: take a = 0, and chain with only negative
        // and no positive elements
        // one of possible solutions would be to transform (*) into equaivalent representation:
        // a * b + /sum positive_chain_elements = /sum negative_chain_elements = sign_bit * q * p
        // but this approach is expensive in terms of constrains as there will be additional multiplications 
        // of q by the sign (which would be an allocated bit) and we would pay additional multiplication gate for 
        // EVERY limb of q
        // we take another way, borrowing the approach taken in sub function: instead of simply subtracting 
        // /sum negative_chain_elements = x we instead add (k * p - x) (**), where k - is constant, taken in such a way
        // that the difference (**) is positive is for every value of x (that's one of the reasons, 
        // we are tracking the maximal possible of FieldElement)
        // this apporach reduces the problem of handling negative chain elements to ONE constant addition 
        // in constaint system. Nobody could deny that this price is neglectable!

        let mut raw_value = a.get_raw_value().zip(b.get_raw_value()).map(|(x, y)| x * y);
        // deal with negative elements and use the trick we have explained at the start of this fucntion
        let (const_delta_value, const_delta_chunks) = {
            let mut limbs_max_vals = vec![BigUint::zero(); params.num_binary_limbs];
            let mut max_val = BigUint::zero();
            for r in chain.elems_to_sub.iter() {
                max_val += r.get_maximal_possible_stored_value();
                for (r_limb, out_limb) in r.binary_limbs.iter().zip(limbs_max_vals.iter_mut()) {
                    *out_limb += r_limb.max_value();
                }
            }
            Self::subtraction_helper(max_val, limbs_max_vals, params)
        };
        let const_limbs : Vec<_> = const_delta_chunks.into_iter().map(|x| {
            Limb::<E>::constant_from_biguint(x)
        }).collect();
        raw_value.as_mut().map(|x| *x += const_delta_value.clone());
        raw_value = chain.add_raw_value_to_accumulator(raw_value);
        let q = raw_value.map(|x| {
            let (q, r) = x.div_rem(&params.represented_field_modulus);
            assert!(r.is_zero());
            q
        });
       
        // so we constraint a * b + [chain_elems_to_add] = q * p + [chain_elems_to_sub] 
        // we start ny estimating q width
        let mut lhs_max_value = a.get_maximal_possible_stored_value() * b.get_maximal_possible_stored_value();
        lhs_max_value += chain.get_maximal_positive_stored_value(); 
        lhs_max_value += const_delta_value.clone();
        let q_max_value = lhs_max_value.clone() / &params.represented_field_modulus;
        let q_max_bits = q_max_value.bits();
        let coarsely = params.allow_coarse_allocation_for_temp_values;
        let quotient = Self::alloc_for_known_bitwidth(cs, q, q_max_bits as usize, params, coarsely)?;

        // next with finding the RNS binary modulus - we perform an exhaustive check here: 
        // a * b + [chain_elems_to_add] < RNS composite_modulus = RNS_binary_modulus * RNS_native_modulus
        // q * p + [chain_elems_to_sub] < RNS composite_modulus
        let rhs_max_value = quotient.get_maximal_possible_stored_value() * &params.represented_field_modulus;
        // rhs_max_value += chain.get_maximal_negative_stored_value(); 
        let max_value = BigUint::max(lhs_max_value, rhs_max_value);

        // now we need to select t - multiple of range check granularity to be large enough, so that:
        // max_value < 2^t * native_field_modulus
        let granularity = params.range_check_granularity;
        let mut rns_binary_modulus_width = round_up(params.represented_field_modulus_bitlength, granularity);
        let mut dynamic_binary_modulus = BigUint::one() << rns_binary_modulus_width; 
        while max_value >= dynamic_binary_modulus.clone() * params.native_field_modulus.clone() {
            rns_binary_modulus_width += granularity;
            dynamic_binary_modulus <<= granularity; 
        }
        let rns_binary_modulus_width_in_limbs = {
            (rns_binary_modulus_width + params.binary_limb_width - 1) / params.binary_limb_width
        };      
        // find how many limbs we could process during single lc processing
        let limbs_per_cycle = {
            let max_btilen = params.native_field_modulus_bitlength;
            (max_btilen - MAX_INTERMIDIATE_OVERFLOW_WIDTH - 1) / params.binary_limb_width - 1
        };
        assert_eq!(limbs_per_cycle, EXPECTED_NUM_LIMBS_PER_FMA_CYCLE);

        // construct shifts:
        let mut shifts = Vec::with_capacity(limbs_per_cycle as usize);
        let shift = params.shift_left_by_limb_constant.clone();
        let mut el = E::Fr::one();
        for _ in 0..limbs_per_cycle {
            shifts.push(el);
            el.mul_assign(&shift);
        }
        shifts.push(el);
        let carry_shift_inverse = shifts[limbs_per_cycle].inverse().unwrap();
        let mut two = E::Fr::one();
        two.double();

        // final goal is to prove that a*b + \sum addition_elements = q * p + r
        // we transform it into the following form for each limb : 
        // new_of * shift + /sum_{i+j = k} a[i] * b[j] + \sum addition_elements[k] - q[k] * p[k] - r[k] + old_shift
        // NB that all p[i] are constants, so in principle we have less multiplications
        let mut left_border : usize = 0;
        let mut input_carry = Term::<E>::zero();
        let p_limbs = Self::split_const_into_limbs(params.represented_field_modulus.clone(), params);
        let max_carry_width = params.binary_limb_width + MAX_INTERMIDIATE_OVERFLOW_WIDTH;
        let mut carry_width = 0;
       
        while left_border < rns_binary_modulus_width_in_limbs {
            let mut lc = AmplifiedLinearCombination::zero();
            lc.add_assign_term(&input_carry);
            let right_border = std::cmp::min(left_border + limbs_per_cycle, rns_binary_modulus_width_in_limbs);

            // if current carry width is zero then we should have carry to be constant zero:
            // a -> b is equal to !a || b
            assert!(
                !(carry_width == 0) || (input_carry.is_constant() && input_carry.get_value().unwrap().is_zero())
            );

            carry_width = {
                // we optimistically assume that all intermidiate overflows do not exceed special
                // apriori chosen constant - MAX_INTERMIDIATE_OVERFLOW_WIDTH
                // however, we are a "validium" solution, so we are going to check that 
                // all overflows are indeed small enough
                let mut dbg_lhs_max_value = BigUint::zero();
                let mut dbg_rhs_max_value = BigUint::zero();
                let carry_max_value = if input_carry.is_constant() {
                    fe_to_biguint(&input_carry.get_constant_value())
                } else {
                    (BigUint::one() << carry_width) - 1u32
                };
                dbg_lhs_max_value += carry_max_value.clone();
                dbg_rhs_max_value += carry_max_value.clone();

                // add terms like a[i] * b[j], where i+j /in [left_border, right_border)
                let iter = get_limbs_product_in_diapason(&a.binary_limbs, &b.binary_limbs, left_border, right_border);
                for (idx, a_limb, b_limb) in iter {
                    let shift = shifts[idx - left_border];
                    dbg_lhs_max_value += a_limb.max_value() * b_limb.max_value() * fe_to_biguint(&shift);
                }

                // add const limbs
                for (i, limb) in get_limbs_in_diapason(&const_limbs, left_border, right_border) {
                    dbg_lhs_max_value += limb.max_value() * fe_to_biguint(&shifts[i - left_border]);
                }
            
                // add limbs of elements that are added:
                for elem in chain.elems_to_add.iter() {
                    for (i, limb) in get_limbs_in_diapason(&elem.binary_limbs, left_border, right_border) {
                        dbg_lhs_max_value += limb.max_value() * fe_to_biguint(&shifts[i - left_border]);
                    }
                }

                // add limbs of elements that are subtracted:
                for elem in chain.elems_to_sub.iter() {
                    for (i, limb) in get_limbs_in_diapason(&elem.binary_limbs, left_border, right_border) {
                        dbg_rhs_max_value += limb.max_value() * fe_to_biguint(&shifts[i - left_border]);
                    }
                }

                // sub limbs for q * p
                let iter = get_limbs_product_in_diapason(&quotient.binary_limbs, &p_limbs, left_border, right_border);
                for (idx, q_limb, p_limb) in iter {
                    let shift = shifts[idx - left_border];
                    dbg_rhs_max_value += q_limb.max_value() * p_limb.max_value() * fe_to_biguint(&shift);
                }

                let dbg_max_value = BigUint::max(dbg_lhs_max_value, dbg_rhs_max_value);
                let dbg_max_bitlen = dbg_max_value.bits() as usize;
                let num_limbs = right_border - left_border;
                let allowed_bitlen = num_limbs * params.binary_limb_width + max_carry_width;
                assert!(dbg_max_bitlen <= allowed_bitlen);

                let mut carry_width = if dbg_max_bitlen <= num_limbs * params.binary_limb_width {
                    0
                } else {
                    dbg_max_bitlen - num_limbs * params.binary_limb_width
                };
                let rem = carry_width % granularity;
                carry_width = if rem > 0 { carry_width + granularity - 8 } else { carry_width };
                assert!(carry_width <= max_carry_width); 
                carry_width
            };
            
            // add terms like a[i] * b[j], where i+j /in [left_border, right_border)
            let iter = get_limbs_product_in_diapason(&a.binary_limbs, &b.binary_limbs, left_border, right_border);
            for (idx, a_limb, b_limb) in iter {
                let shift = shifts[idx - left_border];
                lc.add_assign_product_of_terms_with_coeff(&a_limb.term, &b_limb.term, shift);
            }

            // add const limbs
            for (i, limb) in get_limbs_in_diapason(&const_limbs, left_border, right_border) {
                let shift = shifts[i - left_border];
                lc.add_assign_term_with_coeff(&limb.term, shift);
            }
            
            // add limbs of elements that are added:
            for elem in chain.elems_to_add.iter() {
                for (i, limb) in get_limbs_in_diapason(&elem.binary_limbs, left_border, right_border) {
                    lc.add_assign_term_with_coeff(&limb.term, shifts[i - left_border]);
                }
            }

            // add limbs of elements that are subtracted:
            for elem in chain.elems_to_sub.iter() {
                for (i, limb) in get_limbs_in_diapason(&elem.binary_limbs, left_border, right_border) {
                    lc.sub_assign_term_with_coeff(&limb.term, shifts[i - left_border]);
                }
            }

            // sub limbs for q * p
            let iter = get_limbs_product_in_diapason(&quotient.binary_limbs, &p_limbs, left_border, right_border);
            for (idx, q_limb, p_limb) in iter {
                let mut shift = shifts[idx - left_border];
                shift.negate();
                lc.add_assign_product_of_terms_with_coeff(&q_limb.term, &p_limb.term, shift);
            }

            let limb_range = right_border - left_border;
            let scale_coef = if limb_range == limbs_per_cycle {
                carry_shift_inverse
            } else {
                shifts[limb_range].inverse().unwrap()
            };
            lc.scale(&scale_coef);

            input_carry = if carry_width == 0 {
                lc.enforce_zero(cs)?;
                Term::zero()
            } else {
                input_carry = Term::from_num(lc.into_num(cs)?);
                // carry could be both positive and negative but in any case the bitwidth of it absolute value is 
                // [0, chunk_bitlen + MAX_INTERMIDIATE_OVERFLOW_WIDTH]
                // input_carry = +/- abs_carry * shift;
                let (abs_flag_wit, abs_wit) = match input_carry.get_value() {
                    Some(x) => {
                        let x_as_biguint = fe_to_biguint(&x);
                        if x_as_biguint < BigUint::one() << carry_width {
                            (Some(true), Some(x.clone()))
                        } else {
                            let mut tmp = x.clone();
                            tmp.negate();
                            (Some(false), Some(tmp))
                        }
                    },
                    None => (None, None)
                };
            
                let abs_flag = Term::from_boolean(&Boolean::Is(AllocatedBit::alloc(cs, abs_flag_wit)?)); 
                let abs_carry = AllocatedNum::alloc(cs, || abs_wit.grab())?;
                constraint_bit_length_ext_with_strategy(
                    cs, &abs_carry, carry_width, params.range_check_strategy, true, None
                )?;
                let abs_carry = Term::from_num(Num::Variable(abs_carry)); 
           
                // we need to constraint: carry == (2 * abs_flag - 1) * abs_carry
                // 2 * abs_flag * abs_carry - carry - abs_carry == 0
                let mut lc = AmplifiedLinearCombination::zero();
                lc.add_assign_product_of_terms_with_coeff(&abs_flag, &abs_carry, two);
                lc.sub_assign_term(&input_carry);
                lc.sub_assign_term(&abs_carry);
                lc.enforce_zero(cs)?;
                input_carry
            };

            left_border = right_border;
        }
        
        // now much more trivial part - multiply elements modulo base field
        // a * b + \sum positive_chain_terms - /sum negative_chain_terms - q * p == 0 (mod base_field)
        let residue_to_add = const_delta_value % &params.native_field_modulus;
        let constant_as_fe = biguint_to_fe::<E::Fr>(residue_to_add.clone());

        let mut lc = AmplifiedLinearCombination::zero();
        lc.add_assign_constant(constant_as_fe);
        lc.add_assign_product_of_terms(&a.base_field_limb, &b.base_field_limb);
        for elem in chain.elems_to_add.iter() {
            lc.add_assign_term(&elem.base_field_limb)
        }
        for elem in chain.elems_to_sub.iter() {
            lc.sub_assign_term(&elem.base_field_limb)
        }
        lc.sub_assign_term_with_coeff(&quotient.base_field_limb, params.f_char_mod_fr_char);
        lc.enforce_zero(cs)?;
        
        Ok(())
    } 

    pub fn get_raw_limbs_representation<CS>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError> 
    where CS: ConstraintSystem<E> {
        self.binary_limbs.iter().map(|x| x.term.collapse_into_num(cs)).collect::<Result<Vec<_>, SynthesisError>>()
    }

    #[track_caller]
    pub fn decompose_into_binary_representation<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, limit: Option<usize>
    )-> Result<Vec<Boolean>, SynthesisError> {
        let params = self.representation_params;
        let limit = limit.unwrap_or(params.represented_field_modulus_bitlength);
        self.reduce(cs)?;

        let mut binary_decomposition = Vec::<Boolean>::with_capacity(limit);
        let mut num_bits_accumulated = 0;
        let mut exceeds_limit = false;
        for (_is_first, is_last, limb) in self.binary_limbs.iter().identify_first_last() {
            let max_chunk_bitlen = if is_last { params.msl_width } else { params.binary_limb_width };
            let chunk_bitlen = std::cmp::min(max_chunk_bitlen, limit - num_bits_accumulated);

            if !exceeds_limit {
                let limb_as_num = limb.term.collapse_into_num(cs)?;
                let limb_decomposition = limb_as_num.into_bits_le(cs, Some(chunk_bitlen))?;
                binary_decomposition.extend(limb_decomposition.into_iter());
                num_bits_accumulated += chunk_bitlen;
                exceeds_limit = num_bits_accumulated >= limit;
            } else {
                limb.term.enforce_equal(cs, &Term::zero())?;
            }
        }

        Ok(binary_decomposition)
    }  

    #[track_caller]
    pub fn collapse_chain_with_reduction<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<'a, E, F>, needs_reduction: bool
    ) -> Result<Self, SynthesisError> {
        assert!(chain.len() > 0);
        let params = chain.elems_to_add.get(0).unwrap_or_else(|| &chain.elems_to_sub[0]).representation_params;
        if chain.is_constant() {
            let val = chain.get_field_value().unwrap();
            return Ok(Self::constant(val, params))
        }

        let (const_delta_value, const_delta_chunks) = {
            let mut limbs_max_vals = vec![BigUint::zero(); params.num_binary_limbs];
            let mut max_val = BigUint::zero();
            for r in chain.elems_to_sub.iter() {
                max_val += r.get_maximal_possible_stored_value();
                for (r_limb, out_limb) in r.binary_limbs.iter().zip(limbs_max_vals.iter_mut()) {
                    *out_limb += r_limb.max_value();
                }
            }
            Self::subtraction_helper(max_val, limbs_max_vals, params)
        };
        let const_limbs : Vec<_> = const_delta_chunks.into_iter().map(|x| {
            Limb::<E>::constant_from_biguint(x)
        }).collect();
        
        let mut new_binary_limbs = vec![];
        for idx in 0..params.num_binary_limbs {
            let mut lc = LinearCombination::zero();
            let mut max_val = BigUint::zero();
            for elem in chain.elems_to_add.iter() {
                lc.add_assign_term(&elem.binary_limbs[idx].term);   
                max_val += elem.binary_limbs[idx].max_value();
            }
            for elem in chain.elems_to_sub.iter() {
                lc.sub_assign_term(&elem.binary_limbs[idx].term);   
            }
            lc.add_assign_term(&const_limbs[idx].term);
            max_val += const_limbs[idx].get_value_as_biguint().unwrap();

            let num = lc.into_num(cs)?;
            let limb = Limb::<E>::new(Term::from_num(num), max_val);
            new_binary_limbs.push(limb);
        }

        let mut lc = AmplifiedLinearCombination::zero();
        lc.add_assign_constant(biguint_to_fe(const_delta_value));
        for elem in chain.elems_to_add.iter() {
            lc.add_assign_term(&elem.base_field_limb)
        }
        for elem in chain.elems_to_sub.iter() {
            lc.sub_assign_term(&elem.base_field_limb)
        }
        let base_field_term = Term::from_num(lc.into_num(cs)?);

        let mut new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: base_field_term,
            value: chain.get_field_value(),
            representation_params: params,
            reduction_status: ReductionStatus::Unreduced
        };

        if needs_reduction {
            new.reduce(cs)?;
        }

        Ok(new)
    }

    pub fn collapse_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<'a, E, F>
    ) -> Result<Self, SynthesisError> {
        assert!(chain.len() > 0);
        let params = chain.elems_to_add.get(0).unwrap_or_else(|| &chain.elems_to_sub[0]).representation_params;
        Self::collapse_chain_with_reduction(cs, chain, !params.allow_individual_limb_overflow)
    }

    pub fn from_boolean(flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
        let mut binary_limbs = vec![Limb::zero(); params.num_binary_limbs];
        binary_limbs[0] = Limb::new(Term::from_boolean(flag), BigUint::one());
        Self {
            binary_limbs,
            base_field_limb: Term::from_boolean(flag),
            representation_params: params,
            value: flag.get_value().map(|x| if x { F::one()} else { F::zero()}),
            reduction_status: ReductionStatus::Normalized
        }
    }

    pub fn conditional_constant(value: F, flag: &Boolean, params: &'a RnsParameters<E, F>) -> Self {
        let unconditional_constant = Self::constant(value, params);
        let binary_limbs = unconditional_constant.binary_limbs.iter().map(|cnst_limb| {
            let val = cnst_limb.get_value().unwrap();
            let max_value = cnst_limb.max_value();
            let mut term = Term::from_boolean(flag);
            term.scale(&val);
            Limb { term, max_value }
        }).collect();
        let base_field_value = unconditional_constant.base_field_limb.get_constant_value();
        let mut base_field_term = Term::from_boolean(flag);
        base_field_term.scale(&base_field_value);

        Self {
            binary_limbs,
            base_field_limb: base_field_term,
            representation_params: params,
            value: flag.get_value().map(|x| if x { value } else { F::zero()}),
            reduction_status: ReductionStatus::Normalized
        }
    }

    pub fn enforce_chain_is_zero<CS: ConstraintSystem<E>>(
        cs: &mut CS, chain: FieldElementsChain<'a, E, F>, 
    ) -> Result<(), SynthesisError> {
        let params = chain.elems_to_add.get(0).unwrap_or_else(|| &chain.elems_to_sub[0]).representation_params;
        Self::constraint_fma(cs, &Self::zero(params), &Self::zero(params), chain)
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};
    use plonk::circuit::Width4WithCustomGates;
    use bellman::{plonk::better_better_cs::gates::{selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self}, bls12_381::Bls12};
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;

    // the reason for this test is twofold:
    // first we would like to measure the efficiency of RNS-approach (in terms of number of resulting constraints),
    // and to do this we would compare the number of gates in RNS-mul against number of gates in naive approach
    // second - implemeting modulus multiplication and reduction via schoolbook limbwise approach is a cool and 
    // simple way to test our AmplifiedLinearCombination on a rather maningful example
    #[test]
    fn test_naive_modulus_multiplication() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, Fq>::new_optimal(&mut cs, 80usize);
        let mut rng = rand::thread_rng();

        let a_f: Fq = rng.gen();
        let b_f: Fq = rng.gen();
        let mut result_f = a_f;
        result_f.mul_assign(&b_f);
        
        let a = FieldElement::alloc(&mut cs, Some(a_f), &params).unwrap();
        let b = FieldElement::alloc(&mut cs, Some(b_f), &params).unwrap();
        let mut actual_result = FieldElement::alloc(&mut cs, Some(result_f), &params).unwrap();
    
        let naive_mul_start = cs.get_current_step_number();
        let total_bitlen = params.binary_limb_width * params.num_binary_limbs * 2;
        let carry_bitlen = params.binary_limb_width + params.range_check_granularity;
        let limbs_per_window = (params.native_field_modulus_bitlength - carry_bitlen) / params.binary_limb_width;

        let a_raw = &a.binary_limbs;
        let b_raw = &b.binary_limbs;

        let raw_value = a.get_raw_value().unwrap() * b.get_raw_value().unwrap();
        let (q, r) = raw_value.div_rem(&params.represented_field_modulus);

        let max_value = a.get_maximal_possible_stored_value() * b.get_maximal_possible_stored_value();
        let q_max_value = max_value / &params.represented_field_modulus;
        let q_max_bits = q_max_value.bits();

        let q = FieldElement::alloc_for_known_bitwidth(&mut cs, Some(q), q_max_bits as usize, &params, false).unwrap();
        let mut r = FieldElement::alloc(&mut cs, Some(biguint_to_fe::<Fq>(r)), &params).unwrap();

        // overflow check for q * p + r:
        let mut max_value = q.get_maximal_possible_stored_value() * params.represented_field_modulus.clone();
        max_value += r.get_maximal_possible_stored_value();
        assert!(max_value.bits() as usize <= total_bitlen);

        let q_raw = &q.binary_limbs;
        let r_raw = &r.binary_limbs;
        let p_raw = FieldElement::split_const_into_limbs(params.represented_field_modulus.clone(), &params);

        // construct shifts:
        let mut shifts = Vec::with_capacity(limbs_per_window as usize);
        let shift = params.shift_left_by_limb_constant.clone();
        let mut el = Fr::one();
        for _ in 0..limbs_per_window {
            shifts.push(el);
            el.mul_assign(&shift);
        }
        shifts.push(el);
        let carry_shift_inverse = shifts[limbs_per_window].inverse().unwrap();

        let mut input_carry = Term::zero();
        let mut left_border : usize = 0;
        let total_num_of_limbs = params.num_binary_limbs * 2;
        let mut two = Fr::one();
        two.double();
        
        while left_border < total_num_of_limbs {
            let mut lc = AmplifiedLinearCombination::zero();
            lc.add_assign_term(&input_carry);
            let right_border = std::cmp::min(left_border + limbs_per_window, total_num_of_limbs);

            // add terms like a[i] * b[j], where i+j /in [left_border, right_border)
            let iter = get_limbs_product_in_diapason(a_raw, b_raw, left_border, right_border);
            for (idx, a_limb, b_limb) in iter {
                let shift = shifts[idx - left_border];
                lc.add_assign_product_of_terms_with_coeff(&a_limb.term, &b_limb.term, shift);
            }
            
            // sub limbs for q * p
            let iter = get_limbs_product_in_diapason(q_raw, &p_raw, left_border, right_border);
            for (idx, q_limb, p_limb) in iter {
                let mut shift = shifts[idx - left_border];
                shift.negate();
                lc.add_assign_product_of_terms_with_coeff(&q_limb.term, &p_limb.term, shift);
            }

            // sub remainder
            for (i, limb) in get_limbs_in_diapason(r_raw, left_border, right_border) {
                lc.sub_assign_term_with_coeff(&limb.term, shifts[i - left_border]);
            }

            left_border = right_border;
            let is_last = left_border == total_num_of_limbs;
            if is_last {
                lc.enforce_zero(&mut cs).unwrap();
                break;
            }

            lc.scale(&carry_shift_inverse);
            input_carry = Term::from_num(lc.into_num(&mut cs).unwrap());
            // carry could be both positive and negative but in any case the bitwidth of it absolute value is 
            // [0, chunk_bitlen + MAX_INTERMIDIATE_OVERFLOW_WIDTH]
            // input_carry = +/- abs_carry * shift;
            let mut x = input_carry.get_value().unwrap();
            let (abs_flag_wit, abs_wit) = {
                let x_as_biguint = fe_to_biguint(&x);
                if x_as_biguint < BigUint::one() << carry_bitlen {
                    (Some(true), Some(x))
                } else {
                    x.negate();
                    (Some(false), Some(x))
                }
            };
            
            let abs_flag = Term::from_boolean(&Boolean::Is(AllocatedBit::alloc(&mut cs, abs_flag_wit).unwrap())); 
            let abs_carry = AllocatedNum::alloc(&mut cs, || abs_wit.grab()).unwrap();
            constraint_bit_length_ext_with_strategy(
                &mut cs, &abs_carry, carry_bitlen, params.range_check_strategy, true, None
            ).unwrap();
            let abs_carry = Term::from_num(Num::Variable(abs_carry)); 
           
            // we need to constraint: carry == (2 * abs_flag - 1) * abs_carry
            // 2 * abs_flag * abs_carry - carry - abs_carry == 0
            let mut lc = AmplifiedLinearCombination::zero();
            lc.add_assign_product_of_terms_with_coeff(&abs_flag, &abs_carry, two);
            lc.sub_assign_term(&input_carry);
            lc.sub_assign_term(&abs_carry);
            lc.enforce_zero(&mut cs).unwrap();
        }
        let naive_mul_end = cs.get_current_step_number();

        // check the correctness of native multiplication
        FieldElement::enforce_equal(&mut cs, &mut actual_result, &mut r).unwrap();

        let rns_mul_start = cs.get_current_step_number();
        let mut result = a.mul(&mut cs, &b).unwrap();
        let rns_mul_end = cs.get_current_step_number();
        
        // check the correctness of rns multiplication
        FieldElement::enforce_equal(&mut cs, &mut actual_result, &mut result).unwrap();
       
        assert!(cs.is_satisfied());
        println!("number of constraints for naive approach: {}", naive_mul_end - naive_mul_start);
        println!("number of constraints for rns approach: {}", rns_mul_end - rns_mul_start);
    } 

    struct TestCircuit<E:Engine>{
        _marker: std::marker::PhantomData<E>
    }
    
    impl<E: Engine> Circuit<E> for TestCircuit<E> {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let params = RnsParameters::<E, E::Fq>::new_optimal(cs, 64usize);
            let mut rng = rand::thread_rng();

            let a: E::Fq = rng.gen();
            let b: E::Fq = rng.gen();
            let elem_to_add_0 = rng.gen();
            let elem_to_add_1 = rng.gen();
            let elem_to_sub_0 = rng.gen();
            let elem_to_sub_1 = rng.gen();
            let mut actual_res = a;
            actual_res.add_assign(&elem_to_add_0); 
            actual_res.add_assign(&elem_to_add_1); 
            actual_res.sub_assign(&elem_to_sub_0);
            actual_res.sub_assign(&elem_to_sub_1);
            let b_inv = b.inverse().unwrap();
            actual_res.mul_assign(&b_inv);

            let a = FieldElement::alloc(cs, Some(a), &params)?;
            println!("HERE");
            let b = FieldElement::alloc(cs, Some(b), &params)?;
            let elem_to_add_0 = FieldElement::alloc(cs, Some(elem_to_add_0), &params)?;
            let elem_to_add_1 = FieldElement::alloc(cs, Some(elem_to_add_1), &params)?;
            let elem_to_sub_0 = FieldElement::alloc(cs, Some(elem_to_sub_0), &params)?;
            let elem_to_sub_1 = FieldElement::alloc(cs, Some(elem_to_sub_1), &params)?;
            let mut actual_res = FieldElement::alloc(cs, Some(actual_res), &params)?;

            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&a).add_pos_term(&elem_to_add_0).add_pos_term(&elem_to_add_1);
            chain.add_neg_term(&elem_to_sub_0).add_neg_term(&elem_to_sub_1);
            let mut result = FieldElement::div_with_chain(cs, chain, &b)?;

            FieldElement::enforce_equal(cs, &mut result, &mut actual_res)
        }
    }

    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
    use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
    use crate::bellman::plonk::better_better_cs::verifier::verify;
      
    #[test]
    fn test_stuff_for_bn256() {  
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit = TestCircuit::<Bn256> {_marker: std::marker::PhantomData};
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
        let worker = Worker::new();
        let setup_size = cs.n().next_power_of_two();
        let crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(setup_size, &worker);
        let setup = cs.create_setup::<TestCircuit::<Bn256>>(&worker).unwrap();
        let vk = VerificationKey::from_setup(&setup, &worker, &crs).unwrap();
        
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit = TestCircuit::<Bn256> {_marker: std::marker::PhantomData};
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
        let proof = cs.create_proof::<_, RollingKeccakTranscript<Fr>>(&worker, &setup, &crs, None).unwrap();
        let valid = verify::<_, _, RollingKeccakTranscript<Fr>>(&vk, &proof, None).unwrap();
        assert!(valid);
    }

    #[test]
    fn test_bugfix() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, Fq>::new_optimal(&mut cs, 80usize);
        let mut rng = rand::thread_rng();

        let a: Fq = rng.gen();
        let mut a = FieldElement::alloc(&mut cs, Some(a), &params).unwrap();
        a.normalize(&mut cs).unwrap();
        assert!(cs.is_satisfied());
    }   

    #[test]
    fn test_inversion() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, Fq>::new_optimal(&mut cs, 80usize);
        let mut rng = rand::thread_rng();
        let a: Fq = rng.gen();

        let a_fq = FieldElement::alloc_ext(&mut cs, Some(a), &params).unwrap().0;
        let a_inv = a.inverse();
        let  mut a_res = FieldElement::alloc_ext(&mut cs, a_inv, &params).unwrap().0;
        let a_fq_inverse = a_fq.inverse(&mut cs).unwrap();
        let g = FieldElement::equals(&mut cs, &mut a_fq_inverse.clone(), &mut a_res).unwrap();
        println!("inverses over Fq is {} ", Boolean::get_value(&g).unwrap());
    }

    #[test]
    fn test_bls12_381() {
        use crate::bellman::pairing::bls12_381::{Fq, Bls12, Fr};
        let mut cs = TrivialAssembly::<Bls12, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bls12, Fq>::new_optimal(&mut cs, 72usize);
        let mut rng = rand::thread_rng();

        let a: Fq = rng.gen();
        let b: Fq = rng.gen();
        let mut actual_result = a;
        actual_result.mul_assign(&b);
        let a = FieldElement::alloc(&mut cs, Some(a), &params).unwrap();
        let b = FieldElement::alloc(&mut cs, Some(b), &params).unwrap();
        let mut actual_result = FieldElement::alloc(&mut cs, Some(actual_result), &params).unwrap();
        let mut res = FieldElement::mul(&a, &mut cs, &b).unwrap();
        FieldElement::enforce_equal(&mut cs, &mut res, &mut actual_result).unwrap();
       
        assert!(cs.is_satisfied());
    }   

    #[test]
    fn test_stuff_for_bls12() {  
        use crate::bellman::pairing::bls12_381::{Fq, Bls12, Fr};
        let mut cs = TrivialAssembly::<Bls12, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit = TestCircuit::<Bls12> {_marker: std::marker::PhantomData};
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }
}




    

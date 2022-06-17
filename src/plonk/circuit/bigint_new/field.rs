use super::*;
use super::bigint::*;
use num_traits::{Zero, One};
use num_integer::Integer;

use num_bigint::BigUint;
use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use crate::plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;
use crate::plonk::circuit::SomeField;


// this variable is used in fma implementation: it is set to the maximal numver of bits on which 
// new_of * shift + /sum_{i+j = k} a[i] * b[j] + \sum addition_elements[k] may overflow the limb width border
// NB: this value is chosen more or less randomly - may be it is better to add some heuristics here
const MAX_INTERMIDIATE_OVERFLOW_WIDTH : usize = 16;

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
    allow_coarse_allocation: bool,

    range_check_strategy: RangeConstraintStrategy,
    range_check_granularity: usize,

    num_binary_limbs: usize,
    binary_limb_width: usize,
    msl_width: usize, // hereinafter msl stands for Most Significant Limb

    native_field_modulus: BigUint,
    represented_field_modulus: BigUint,
    represented_field_modulus_bitlength: usize,
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
        let allow_coarse_allocation = true;
        
        let strategy = get_optimal_strategy(cs);
        let range_check_granularity = strategy.get_range_check_granularity();
        assert!(limb_size % range_check_granularity == 0, "limb size is not a multiple of range check quant");

        let native_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let represented_field_modulus = repr_to_biguint::<F>(&F::char());
        let represented_field_modulus_bitlength = represented_field_modulus.bits() as usize;
        let num_binary_limbs = represented_field_modulus_bitlength + limb_size - 1 / limb_size;     
        
        let rem = represented_field_modulus_bitlength % limb_size;
        let msl_width = if rem == 0 { limb_size } else { rem };

        let shift = BigUint::one() << limb_size;
        let shift_left_by_limb_constant = biguint_to_fe::<E::Fr>(shift.clone());
        
        // (verifying that k * Fr::modulus != 0 (mod 2^{limb_width}) for all positive values of k, such that:
        // bitlength(k * Fr::modulus) <= represented_field_modulus_bitlength bits
        // for the testimony of the necessity of this check look the comments in "iz_zero" function
        let mut multiple_of_fr_char = native_field_modulus.clone();
        while multiple_of_fr_char.bits() as usize <= represented_field_modulus_bitlength {
            if (multiple_of_fr_char.clone() % shift.clone()).is_zero() {
                panic!("k * Fr::modulus == 0 (mod 2^limb_width)");
            }
            multiple_of_fr_char += native_field_modulus.clone(); 
        }
        let f_char_mod_fr_char = biguint_to_fe::<E::Fr>(represented_field_modulus.clone());
        let f_char_mod_binary_shift = biguint_to_fe::<E::Fr>(represented_field_modulus.clone() % shift);
       
        // we chose t to be large enough, so that: 2^(2 * max_binary_bitlen) < native_field_modulus * 2^t
        let t = represented_field_modulus_bitlength * 2usize;
        let infty = BigUint::one() << t;

        let max_ordinary_limb_val_on_alloc = get_max_possible_value_for_bit_width(limb_size);
        let max_msl_val_on_alloc_coarsely = get_max_possible_value_for_bit_width(msl_width);
        let max_msl_val_on_alloc_strict = represented_field_modulus.clone() >> ((num_binary_limbs - 1) * limb_size);
        
        // check by 4 * p < native_field_modulus * 2^{limb_width} :
        // this is required by enforce_zero family of functions
        let lhs = represented_field_modulus.clone() * 4u64;
        let rhs = native_field_modulus.clone() << limb_size;
        assert!(lhs < rhs, "4 * p >= native_field_modulus * 2^limb_width");

        RnsParameters::<E, F> {
            allow_individual_limb_overflow,
            allow_coarse_allocation,
            num_binary_limbs,
            range_check_strategy: strategy,
            range_check_granularity,
            binary_limb_width: limb_size,
            msl_width,
            native_field_modulus,
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
        self.max_value.clone()
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
) -> Box<dyn Iterator<Item = (usize, &'a Limb<E>)> + 'a> {
    let iter = x.iter().enumerate().filter(move |(i, _x)| { *i >= start && *i < end});
    Box::new(iter)
}

fn get_limbs_product_in_diapason<'a, E: Engine>(
    x: &'a Vec<Limb<E>>, y: &'a Vec<Limb<E>>, start: usize, end: usize
) -> Box<dyn Iterator<Item = (usize, &'a Limb<E>, &'a Limb<E>)> + 'a> {
    let iter = x.iter().enumerate().zip(y.iter().enumerate()).filter_map(move |x| {
        let ((i, x_limb), (j, y_limb)) = x;
        if i + j >= start && i + j < end {
            Some((i + j, x_limb, y_limb))
        }
        else {
            None
        }
    });
    Box::new(iter)
}


#[derive(Clone, Debug, PartialEq)]
pub enum ReductionMode {
    Strict,
    Loose,
    NoReduction
}


#[derive(Clone, Debug)]
pub struct FieldElement<'a, E: Engine, F: PrimeField>{
    pub binary_limbs: Vec<Limb<E>>,
    pub base_field_limb: Term<E>,
    pub representation_params: &'a RnsParameters<E, F>,
    pub value: Option<F>,
}

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
pub fn slice_into_limbs_non_exact(
    value: BigUint, max_width: usize, limb_width: usize
) -> (Vec<BigUint>, usize) {
    // here msl stands for Most Significant Limb
    let (chunks, msl_width) = slice_some_into_limbs_non_exact(Some(value), max_width, limb_width);
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

    // we do not do the range check of the limbs: 
    // this function assumes that every limb is at most params.binary_limb_bitwidth bits long
    // and the maximal_stored_value < F::char
    #[track_caller]
    pub fn alloc_from_limbs_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS, raw_limbs: &[Num<E>], params: &'a RnsParameters<E, F>
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
        
        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: total_value,
        };
        
        Ok(new)
    }

    #[track_caller]
    fn alloc_impl<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, params: &'a RnsParameters<E, F>, coarsely: bool
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
            value.clone(), params.represented_field_modulus_bitlength, params.binary_limb_width
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
                cs, &a, bitlength, params.range_check_strategy, coarsely
            )?; 
            decompositions.push(decomposition);

            let term = Term::<E>::from_allocated_num(a.clone());
            let limb = Limb::<E>::new(term, max_value);

            binary_limbs_allocated.push(limb);

            base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
            current_constant.mul_assign(&shift_constant);
        }
        assert!(binary_limbs_allocated.len() <= params.num_binary_limbs);
        binary_limbs_allocated.resize(params.num_binary_limbs, Limb::zero());
        
        let base_field_limb_num = base_field_lc.into_num(cs)?;
        let base_field_term = Term::<E>::from_num(base_field_limb_num);
        let field_value = value.map(|x| biguint_to_fe::<F>(x));
        
        let new = Self {
            binary_limbs: binary_limbs_allocated,
            base_field_limb: base_field_term,
            representation_params: params,
            value: field_value,
        };
        let total_decomposition = RangeCheckDecomposition::combine(&decompositions);
        
        Ok((new, total_decomposition))
    }

    // coarsely means that most significant limb may overflow a little (up to range constraint granularity)
    #[track_caller]
    pub fn alloc_coarsely<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (new, _decomposition) = Self::alloc_ext(cs, value, params, true)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_exactly<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let (new, _decomposition) = Self::alloc_ext(cs, value, params, false)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>, coarsely: bool
    ) -> Result<(Self, RangeCheckDecomposition<E>), SynthesisError>  
    {
        let bit_width = params.represented_field_modulus_bitlength;
        let value_as_biguint = value.map(|x| fe_to_biguint(&x));
        Self::alloc_impl(cs, value_as_biguint, bit_width, params, coarsely)
    }

    #[track_caller]
    fn alloc_for_known_bitwidth<CS: ConstraintSystem<E>>(
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, params: &'a RnsParameters<E, F>, coarsely: bool
    ) -> Result<Self, SynthesisError> {
        let (val, _decomposition) = Self::alloc_impl(cs, value, bit_width, params, coarsely)?;
        Ok(val)
    }

    fn split_const_into_limbs(value: BigUint, params: &'a RnsParameters<E, F>) -> Vec<Limb<E>> {
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
    fn get_maximal_possible_stored_value(&self) -> BigUint {
        let shift = self.representation_params.binary_limb_width;
        let mut result = BigUint::from(0u64);

        for l in self.binary_limbs.iter().rev() {
            result <<= shift;
            result += l.max_value();
        }

        result
    }

    fn check_params_equivalence(a: &Self, b: &Self) -> bool {
        std::ptr::eq(a.representation_params, b.representation_params)
    }

    pub fn is_zero<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(Boolean, Self), SynthesisError> 
    {
        let params = self.representation_params;
        let mut x = self.reduce_strict(cs)?;
       
        // after reduction the value of x is in interval [0; 2*F) and all limbs occupy exactly limb_width bits
        // (i.e. capacity bits are not involved)
        // so, to test if x is zero we need to consider two cases: x == 0 and x == F
        // x == 0 <=> field_limb == 0 and least_significant_binary_limb == 0 
        // (but we should additionaly check that k * Fr::modulus % 2^{limb_width} != 0 for small positive k)
        // x == F <=> field_limb == F (mod Fr) and least_significal_binary_llimb == F (mod 2^{limb_width})
        // (again, as long as k * Fr::modulus != 0 (mod 2^{limb_width}) for small positive k)
        // the exact range of k to test is determined by the maximal multiple of Fr::modulus which fits into
        // params.represented_field_modulus_bitlength bits
        
        let least_significant_binary_limb = x.binary_limbs[0].term.collapse_into_num(cs)?;
        let base_field_limb = x.base_field_limb.collapse_into_num(cs)?;

        // check if x == 0
        let binary_limb_check = least_significant_binary_limb.is_zero(cs)?;
        let base_field_limb_check = base_field_limb.is_zero(cs)?;
        let x_is_raw_zero = Boolean::and(cs, &binary_limb_check, &base_field_limb_check)?;

        // check if x == F::char
        let f_char_mod_fr_char = Num::Constant(params.f_char_mod_fr_char.clone());
        let f_char_mod_binary_shift = Num::Constant(params.f_char_mod_binary_shift.clone());
        let binary_limb_check = Num::equals(cs, &least_significant_binary_limb, &f_char_mod_binary_shift)?;
        let base_field_limb_check = Num::equals(cs, &base_field_limb, &f_char_mod_fr_char)?;
        let x_is_raw_modulus = Boolean::and(cs, &binary_limb_check, &base_field_limb_check)?;
        
        let is_zero = Boolean::or(cs, &x_is_raw_zero, &x_is_raw_modulus)?;
        x.binary_limbs[0].term = Term::from_num(least_significant_binary_limb);
        x.base_field_limb = Term::from_num(base_field_limb);
        
        Ok((is_zero, x))
    }

    #[track_caller]
    pub fn select<CS>(cs: &mut CS, flag: &Boolean, first: &Self, second: &Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        assert!(Self::check_params_equivalence(first, second));
        match flag {
            Boolean::Constant(c) => {
                if *c { return Ok(first.clone()) } else { return Ok(second.clone()) };
            },
            _ => {},
        };

        // flag * a + (1-flag) * b = flag * (a-b) + b
        let flag_as_term = Term::<E>::from_boolean(flag);
        let mut new_binary_limbs = vec![];

        for (l, r) in first.binary_limbs.iter().zip(second.binary_limbs.iter()) 
        {
            let mut minus_b = r.term.clone();
            minus_b.negate();
            let a_minus_b = l.term.add(cs, &minus_b)?;
            let n = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &r.term)?;
            let new_max = std::cmp::max(l.max_value(), r.max_value());
            let new_limb = Limb::new(n, new_max);

            new_binary_limbs.push(new_limb);
        }

        let mut minus_b = second.base_field_limb.clone();
        minus_b.negate();
        let a_minus_b = first.base_field_limb.add(cs, &minus_b)?;
        let new_base_limb = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &second.base_field_limb)?;

        let new_value = if let Some(f) = flag.get_value() {
            if f { first.get_field_value() } else { second.get_field_value() }
        } else {
            None
        };

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: first.representation_params
        };
        Ok(new)
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::zero(&self.representation_params).sub(cs, self)
    }

    #[track_caller]
    // negates if true
    pub fn conditional_negation<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        if let Some(f) = flag.get_value() {
            if f { return self.negate(cs) } else { return Ok(self.clone()) }
        };
        let negated = self.negate(cs)?;
        Self::select(cs, flag, &negated, self)
    }

    // we call value to be reduced if all binary limbs do not overflow: i.e there are no capacity bits occupied, 
    // additionally we require for Loose normalization for value to fit [0, 2 * F::char) range
    // and for Strict reduction value should be completely normalized i.e. to be in [0, F::char) range
    fn needs_reduction(&self, mode: ReductionMode) -> bool {
        if self.is_constant() {
            return false;
        }

        let params = &self.representation_params;
        let upper_bound = match mode {
            ReductionMode::Loose => params.represented_field_modulus.clone() * 2u64,
            ReductionMode::Strict => params.represented_field_modulus.clone(),
            ReductionMode::NoReduction => params.infty.clone(),
        };
        let mut needs_reduction = self.get_maximal_possible_stored_value() >= upper_bound;

        if mode == ReductionMode::NoReduction {
            return false;
        }
        
        for (_is_first, is_last, binary_limb) in self.binary_limbs.iter().identify_first_last() {
            let max_width = if is_last { params.msl_width } else { params.binary_limb_width };
            needs_reduction = needs_reduction || (binary_limb.max_value().bits() as usize > max_width);
        }

        needs_reduction
    }

    #[track_caller]
    pub fn reduce_if_necessary<CS>(self, cs: &mut CS, mode: ReductionMode) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        if self.needs_reduction(mode) {
            return self.reduction_impl(cs);
        }
        Ok(self)
    }

    pub fn reduce_strict<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let x = self.reduce_if_necessary(cs, ReductionMode::Strict)?; 
        x.enforce_if_normalized(cs)?;
        Ok(x)        
    }

    pub fn reduce_loose<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self, SynthesisError> {
        self.reduce_if_necessary(cs, ReductionMode::Loose) 
    }

    #[track_caller]
    fn reduction_impl<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let params = self.representation_params;

        // in order to reduce the value x, we calculate y = x (mod F::char) and k, such that y = x - k * F::char
        // which is equaivalent to x = y + k * F::char, and k is small enough
        // first perform actual reduction in the field that we try to represent
        let (q, rem) = if let Some(v) = self.get_raw_value() {
            let (q, rem) = v.div_rem(&params.represented_field_modulus);
            debug_assert_eq!(fe_to_biguint(&self.get_field_value().unwrap()), rem);
            (Some(q), Some(rem))
        } else {
            (None, None)
        };
        let max_val = self.get_maximal_possible_stored_value();
        let max_q_bits = (max_val / &params.represented_field_modulus).bits() as usize;
        assert!(max_q_bits <= E::Fr::CAPACITY as usize, "for no quotient size can overflow capacity");

        let q_as_field_repr = if max_q_bits == 0 { 
            Self::zero(&params)
        } else { 
            Self::alloc_for_known_bitwidth(cs, q, max_q_bits, &params, params.allow_coarse_allocation)?
        };

        let r_fe = some_biguint_to_fe::<F>(&rem);
        let r_elem = Self::alloc_exactly(cs, r_fe, params)?;
        assert!(r_elem.needs_reduction(ReductionMode::Strict) == false);

        // perform constraining by implementing multiplication: x = q*p + r
        let one = Self::one(self.representation_params);
        Self::constraint_fma(cs, &self, &one, &[], &q_as_field_repr, &r_elem.clone())?;

        Ok(r_elem)
    }

    #[track_caller]
    fn enforce_if_normalized<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        if self.is_constant() { return Ok(()) }
        let params = self.representation_params;
        let shift = params.shift_left_by_limb_constant;
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        // msl here stands for Most Significant Limb
        let (modulus_limbs, msl_width) = slice_into_limbs_non_exact(
            params.represented_field_modulus.clone(), params.binary_limb_width, params.num_binary_limbs
        ); 

        let mut borrow = Limb::zero();
        let mut is_const_term = true;
        let iter = self.binary_limbs.iter().zip(modulus_limbs.iter()).identify_first_last();
        for (_is_first, is_last, (l, m)) in  iter {
            // l - borrow - m + new_borrow * shift = r
            // check if l >= borrow + m to fing the value of new_borrow
            let (new_borrow_wit, r_wit) = match (l.get_value_as_biguint(), borrow.get_value_as_biguint()) {
                (Some(l), Some(borrow)) => {
                    if l >= borrow.clone() + m {
                        (Some(false), Some(l - borrow - m))
                    } else {
                        (Some(true), Some((BigUint::one() << params.binary_limb_width) + l - borrow - m))
                    }
                }
                (_, _) => (None, None)
            }; 
            is_const_term &= l.is_constant(); 
            
            let b = if is_const_term || is_last {
                Boolean::constant(if is_last { true } else { new_borrow_wit.unwrap() as bool })
            } else {
                Boolean::Is(AllocatedBit::alloc(cs, new_borrow_wit.map(|x| x as bool))?)
            };
            let new_borrow = Term::<E>::from_boolean(&b);

            let r = if is_const_term {
                Num::Constant(biguint_to_fe::<E::Fr>(r_wit.unwrap()))
            } else {
                let var = AllocatedNum::alloc(cs, || r_wit.map(|x| biguint_to_fe::<E::Fr>(x)).grab())?;
                let width = if is_last { msl_width } else { params.binary_limb_width };
                constraint_bit_length_with_strategy(cs, &var, width, params.range_check_strategy)?;
                Num::Variable(var) 
            };
            let r_term = Term::<E>::from_num(r);

            // enforce constraint: l - borrow - m + new_borrow * shift - r = 0
            let mut lc = LinearCombination::zero();
            lc.add_assign_term(&l.term);
            lc.add_assign_term_with_coeff(&borrow.term, minus_one.clone());
            lc.add_assign_term_with_coeff(&new_borrow, shift.clone());
            lc.add_assign_term_with_coeff(&r_term, minus_one.clone());
            lc.enforce_zero(cs)?;
            
            borrow = Limb::new(new_borrow, BigUint::one());
        }

        Ok(())
    }

    #[track_caller]
    pub fn add_with_reduction<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self, mode: ReductionMode
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

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };
        new.reduce_if_necessary(cs, mode)
    }

    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let mode = if self.representation_params.allow_individual_limb_overflow {
            ReductionMode::NoReduction
        } else {
            ReductionMode::Loose
        };
        self.add_with_reduction(cs, other, mode)
    }

    pub fn double_with_reduction<CS>(&self, cs: &mut CS, mode: ReductionMode) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        let params = self.representation_params;
        let mut two = E::Fr::one();
        two.double();

        if self.is_constant() {
            let tmp = self.get_field_value().add(&self.get_field_value());
            let new = Self::constant(tmp.unwrap(), params);
            return Ok(new);
        }

        let mut new_binary_limbs = vec![];
        for l in self.binary_limbs.iter()
        {
            let mut new_term = l.term.clone();
            new_term.scale(&two);
            let new_max_value = l.max_value.clone() * BigUint::from(2u64);

            let limb = Limb::<E>::new(new_term, new_max_value);
            new_binary_limbs.push(limb);
        }
        let mut new_base_limb = self.base_field_limb.clone();
        new_base_limb.scale(&two);
        let new_value = self.get_field_value().add(&self.get_field_value());

        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_base_limb,
            value: new_value,
            representation_params: params
        };
        new.reduce_if_necessary(cs, mode)
    }

    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mode = if self.representation_params.allow_individual_limb_overflow {
            ReductionMode::NoReduction
        } else {
            ReductionMode::Loose
        };
        self.double_with_reduction(cs, mode)
    }

    pub fn sub_with_reduction<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, other: &Self, mode: ReductionMode
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
            let result = self.add_with_reduction(cs, &other_negated, mode)?;
            return Ok(result);
        }

        // now we can determine how many moduluses of the represented field we have to add to never underflow
        let max_val = other.get_maximal_possible_stored_value();
        let mut multiples_to_add_at_least = params.represented_field_modulus.clone();
        while multiples_to_add_at_least < max_val {
            multiples_to_add_at_least += params.represented_field_modulus.clone();
        }

        let mut const_constituent_chunks = Vec::with_capacity(params.num_binary_limbs);
        let mut tmp = multiples_to_add_at_least.clone();

        for (_is_first, is_last, var_limb) in other.binary_limbs.iter().identify_first_last() {
            if !is_last { 
                let bitlen = var_limb.max_value().bits();
                let modulus = BigUint::one() << bitlen;
                let rem = tmp.clone() % modulus.clone();
                if rem >= var_limb.max_value() {
                    const_constituent_chunks.push(rem);
                    tmp >>= bitlen;
                    continue;
                } else {
                    let chunk = rem + (modulus << 1u64);
                    const_constituent_chunks.push(chunk);
                    tmp >>= bitlen;
                    tmp -= 1u64;
                    continue;
                }
            } else { 
                const_constituent_chunks.push(tmp.clone());
            };
        }

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
        let new = Self {
            binary_limbs: new_binary_limbs,
            base_field_limb: new_field_limb,
            value: new_value,
            representation_params: params
        };
        new.reduce_if_necessary(cs, mode)
    }

    pub fn sub<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        let mode = if self.representation_params.allow_individual_limb_overflow {
            ReductionMode::NoReduction
        } else {
            ReductionMode::Loose
        };
        self.sub_with_reduction(cs, other, mode)
    }

    pub fn mul<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        Self::fma(cs, &self, &other, &[], false)
    }

    pub fn culminative_mul<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> 
    {
        Self::fma(cs, &self, &other, &[], true)
    }

    pub fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::fma(cs, &self, &self, &[], false)
    }

    pub fn culminative_square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::fma(cs, &self, &self, &[], true)
    }

    pub fn div<CS: ConstraintSystem<E>>(&self, cs: &mut CS, den: &Self) -> Result<Self, SynthesisError> {
        self.div_impl(cs, den, false)
    }
    
    pub fn culminative_div<CS: ConstraintSystem<E>>(&self, cs: &mut CS, den: &Self) -> Result<Self, SynthesisError> {
        self.div_impl(cs, den, true)
    } 

    #[track_caller]
    fn div_impl<CS>(&self, cs: &mut CS, den: &Self, is_culminative: bool) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let params = self.representation_params;
        assert!(Self::check_params_equivalence(self, den));
        // we do self/den = result mod p, where we assume that den != 0
        // so naively we should constraint: result * den = q * p + self
        assert!(!den.get_field_value().unwrap_or(F::one()).is_zero());

        if self.is_constant() && den.is_constant() {
            let mut tmp = den.get_field_value().unwrap().inverse().unwrap();
            tmp.mul_assign(&self.get_field_value().unwrap());
            let new = Self::constant(tmp, params);
            return Ok(new);
        }
        
        let (result_wit, q_wit) = match (self.get_raw_value(), den.get_raw_value()) {
            (Some(this), Some(den)) => {
                let inv = mod_inverse(&den, &params.represented_field_modulus);
                let result = (this.clone() * &inv) % &params.represented_field_modulus;
                let value = den.clone() * &result - &this;
                let (q, rem) = value.div_rem(&params.represented_field_modulus);
                
                assert!(rem.is_zero(), "remainder = {}", rem.to_str_radix(16));
                (Some(result), Some(q))
            },
            _ => (None, None),
        };

        let bit_width = params.represented_field_modulus_bitlength;
        let coarsely = params.allow_coarse_allocation;
        let res = Self::alloc_for_known_bitwidth(cs, result_wit, bit_width, params, coarsely && !is_culminative)?;
        assert!(res.needs_reduction(ReductionMode::Strict) == false);

        // estimate q bit width: result * den = q * p + self, 
        // so we say that self min value == 0 (as it goes into LHS with - sign) and worst case for q is
        let q_max_value = {
            let tmp = res.get_maximal_possible_stored_value() * den.get_maximal_possible_stored_value();
            tmp / &params.represented_field_modulus
        };
        let q_max_bits = q_max_value.bits();
        let q_elem = Self::alloc_for_known_bitwidth(cs, q_wit, q_max_bits as usize, params, coarsely)?;

        Self::constraint_fma(cs, &den, &res, &[], &q_elem, &self)?;
        Ok(res)
    }

    #[track_caller]
    fn fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, a: &Self, b: &Self, to_add: &[Self], is_culminative: bool
    ) -> Result<Self, SynthesisError> {
        let params = &a.representation_params;
        assert!(Self::check_params_equivalence(a, b));
        assert!(to_add.iter().all(|x| Self::check_params_equivalence(a, x)));

        let mut final_value = a.get_field_value();
        final_value = final_value.mul(&b.get_field_value());
        for r in to_add.iter() {
            final_value = final_value.add(&r.get_field_value());
        }

        let mut raw_value_is_none = false;
        let mut raw_value = BigUint::from(0u64);
        match (a.get_raw_value(), b.get_raw_value()) {
            (Some(t), Some(m)) => raw_value += t * m,
            _ => raw_value_is_none = true,
        }
        
        let mut all_constants = a.is_constant() && b.is_constant();
        for r in to_add.iter() {
            if let Some(v) = r.get_raw_value() {
                raw_value += v;
            } else {
                raw_value_is_none = true;
            }
            all_constants = all_constants & r.is_constant();
        } 
        let (q, r) = raw_value.div_rem(&params.represented_field_modulus);

        if all_constants {
            let r = biguint_to_fe::<F>(r);
            let new = Self::constant(r, params);
            return Ok(new);
        }

        // so we constraint a * b + [to_add] = q * p + r
        // we we estimate q width
        let mut lhs_max_value = a.get_maximal_possible_stored_value() * b.get_maximal_possible_stored_value();
        for el in to_add.iter() {
            lhs_max_value += el.get_maximal_possible_stored_value();
        }
        let q_max_value = lhs_max_value / &params.represented_field_modulus;
        let q_max_bits = q_max_value.bits();

        let (q, r) = if raw_value_is_none { (None, None) } else { (Some(q), Some(r)) };
        let coarsely = params.allow_coarse_allocation;
        let r_max_bits = params.represented_field_modulus_bitlength;

        let q_elem = Self::alloc_for_known_bitwidth(cs, q, q_max_bits as usize, params, coarsely)?;
        let r_elem = Self::alloc_for_known_bitwidth(cs, r, r_max_bits as usize, params, coarsely || is_culminative)?;

        Self::constraint_fma(cs, &a, &b, to_add, &q_elem, &r_elem)?;
        Ok(r_elem)
    }

    #[track_caller]
    pub fn enforce_equal<CS>(cs: &mut CS, this: Self, other: Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        assert!(Self::check_params_equivalence(&this, &other));
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            assert!(a == b);
            return Ok(())
        }
      
        let this = this.reduce_if_necessary(cs, ReductionMode::Loose)?;
        let other = other.reduce_if_necessary(cs, ReductionMode::Loose)?;

        // now we know that both this and other are < 2 * F::char, hence to enforce that they are equal
        // However, in all user scenarious we may assume that reduction is complete, i.e:
        // both values are in range [0; F::char)
        // it is enough to chech equality only mod native field and mod limb_width 
        // which is justified by 2 * p < native_field_modulus * 2^{limb_width}
        this.binary_limbs[0].term.enforce_equal(cs, &other.binary_limbs[0].term)?;
        this.base_field_limb.enforce_equal(cs, &other.base_field_limb)?;

        Ok(())
    }

     #[track_caller]
    pub fn enforce_not_equal<CS>(cs: &mut CS, this: Self, other: Self) -> Result<(), SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        assert!(Self::check_params_equivalence(&this, &other));   
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            assert!(a != b);
            return Ok(())
        }

        let this = this.reduce_if_necessary(cs, ReductionMode::Strict)?;
        let other = other.reduce_if_necessary(cs, ReductionMode::Strict)?;

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
        lc.add_assign_product_of_terms(&a, &other.binary_limbs[0].term);
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

    #[track_caller]
    pub fn equals<CS: ConstraintSystem<E>>(cs: &mut CS, this: Self, other: Self) -> Result<Boolean, SynthesisError> {
        assert!(Self::check_params_equivalence(&this, &other));
        if this.is_constant() && other.is_constant() {
            let a = this.get_field_value().unwrap();
            let b = other.get_field_value().unwrap();
            return Ok(Boolean::constant(a == b));
        }

        let this = this.reduce_if_necessary(cs, ReductionMode::Strict)?;
        let other = other.reduce_if_necessary(cs, ReductionMode::Strict)?;

        let mut out_0 = Boolean::zero();
        let mut out_1 = Boolean::zero();
        let iter = std::array::IntoIter::new([
            (&this.binary_limbs[0].term, &other.binary_limbs[0].term, &mut out_0), 
            (&this.base_field_limb, &other.base_field_limb, &mut out_1)
        ]);
        
        for (a, b, out) in iter {
            let a = a.collapse_into_num(cs)?;
            let b = b.collapse_into_num(cs)?;
            let equals = Num::equals(cs, &a, &b)?;
            *out = equals;
        }

        let equals = Boolean::and(cs, &out_0, &out_1)?;
        Ok(equals)
    }

    #[track_caller]
    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, mul_a: &Self, mul_b: &Self, addition_elements: &[Self], quotient: &Self, remainder: &Self
    ) -> Result<(), SynthesisError> {
        let params = &mul_a.representation_params;
        let bin_limb_width = params.binary_limb_width;
        let mut two = E::Fr::one();
        two.double();
        
        // We start with finding the RNS binary modulus - we perform an exhaustive check here: 
        // a * b + [addition_elements] < RNS composite_modulus = RNS_binary_modulus * RNS_native_modulus
        // result_quotient * p + r < RNS composite_modulus
        let mut lhs_max_value = BigUint::zero();
        lhs_max_value += mul_a.get_maximal_possible_stored_value() * mul_b.get_maximal_possible_stored_value();
        for el in addition_elements.iter() {
            lhs_max_value += el.get_maximal_possible_stored_value();
        }
        let mut rhs_max_value = BigUint::zero();
        rhs_max_value += quotient.get_maximal_possible_stored_value() * &params.represented_field_modulus;
        rhs_max_value += remainder.get_maximal_possible_stored_value();
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
        let rns_binary_modulus_width_in_limbs = round_up(rns_binary_modulus_width, params.num_binary_limbs);      
        // find how many limbs we could process during single lc processing
        let limbs_per_cycle = {
            let max_btilen = params.represented_field_modulus_bitlength;
            (max_btilen - MAX_INTERMIDIATE_OVERFLOW_WIDTH - 1) / params.binary_limb_width - 1
        };

        // construct shifts:
        let mut shifts = Vec::with_capacity(limbs_per_cycle as usize);
        let shift = params.shift_left_by_limb_constant.clone();
        let mut el = E::Fr::one();
        for _ in 0..limbs_per_cycle {
            shifts.push(el);
            el.mul_assign(&shift);
        }

        // total goal is to prove that a*b + \sum addition_elements = q * p + r
        // we transform it into the following form for each limb : 
        // new_of * shift + /sum_{i+j = k} a[i] * b[j] + \sum addition_elements[k] - q[k] * p[k] - r[k] + old_shift
        // NB that all p[i] are constants, so in principle we have less multiplications
        let mut left_border : usize = 0;
        let mut input_carry = Term::zero();
        let p_limbs = Self::split_const_into_limbs(params.represented_field_modulus.clone(), params);

        while left_border < rns_binary_modulus_width {
            let mut lc = AmplifiedLinearCombination::zero();
            lc.add_assign_term(&input_carry);
            let right_border = std::cmp::min(left_border + limbs_per_cycle, rns_binary_modulus_width_in_limbs);
            
            // add terms like a[i] * b[j], where i+j /in [left_border, right_border)
            let iter = get_limbs_product_in_diapason(&mul_a.binary_limbs, &mul_b.binary_limbs, left_border, right_border);
            for (idx, a_limb, b_limb) in iter {
                let shift = shifts[idx - left_border];
                lc.add_assign_product_of_terms_with_coeff(&a_limb.term, &b_limb.term, shift);
            }
               
            // add limbs of addition_elements:
            for elem in addition_elements.iter() {
                for (i, limb) in get_limbs_in_diapason(&elem.binary_limbs, left_border, right_border) {
                    lc.add_assign_term_with_coeff(&limb.term, shifts[i - left_border]);
                }
            }

            // sub limbs for q * p
            let iter = get_limbs_product_in_diapason(&quotient.binary_limbs, &p_limbs, left_border, right_border);
            for (idx, q_limb, p_limb) in iter {
                let mut shift = shifts[idx - left_border];
                shift.negate();
                lc.add_assign_product_of_terms_with_coeff(&q_limb.term, &p_limb.term, shift);
            }

            // sub remainder
            for (i, limb) in get_limbs_in_diapason(&remainder.binary_limbs, left_border, right_border) {
                lc.sub_assign_term_with_coeff(&limb.term, shifts[i - left_border]);
            }

            input_carry = Term::from_num(lc.into_num(cs)?);
            // carry could be both positive and negative but in any case the bitwidth of it absolute value is 
            // [0, chunk_bitlen + MAX_INTERMIDIATE_OVERFLOW_WIDTH]
            let (abs_flag_wit, abs_wit) = match input_carry.get_value() {
                Some(x) => {
                    let x_as_biguint = fe_to_biguint(&x);
                    if x_as_biguint <= BigUint::one() << (bin_limb_width + MAX_INTERMIDIATE_OVERFLOW_WIDTH) {
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
                cs, &abs_carry, bin_limb_width + MAX_INTERMIDIATE_OVERFLOW_WIDTH, params.range_check_strategy, true
            )?;
            let abs_carry = Term::from_num(Num::Variable(abs_carry)); 

            // we need to constraint: carry == (2 * abs_flag - 1) * abs_carry
            // 2 * abs_flag * abs_carry - carry - abs_carry == 0
            let mut lc = AmplifiedLinearCombination::zero();
            lc.add_assign_product_of_terms_with_coeff(&abs_flag, &abs_carry, two);
            lc.sub_assign_term(&input_carry);
            lc.sub_assign_term(&abs_carry);
            lc.enforce_zero(cs)?;

            left_border = right_border;
        }
        
        // now much more trivial part - multiply elements modulo base field
        // a * b + \sum addition_elements - q * p - r == 0 (mod base_field)
        let mut lc = AmplifiedLinearCombination::zero();
        lc.add_assign_product_of_terms(&mul_a.base_field_limb, &mul_b.base_field_limb);
        for elem in addition_elements.iter() {
            lc.add_assign_term(&elem.base_field_limb)
        }
        lc.sub_assign_term_with_coeff(&quotient.base_field_limb, params.f_char_mod_fr_char);
        lc.sub_assign_term(&remainder.base_field_limb);
        lc.enforce_zero(cs)?;

        Ok(())
    }   
}



    

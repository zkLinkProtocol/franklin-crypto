use super::*;
use super::bigint::*;
use num_traits::{Zero, One};

use num_bigint::BigUint;
use super::super::allocated_num::{AllocatedNum, Num};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;
use crate::plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;


// Parameters of the representation
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsParameters<E: Engine, F: PrimeField>{
    pub binary_limb_width: usize,
    pub num_binary_limbs: usize,
    pub binary_limb_capacity: usize,
    pub range_check_strategy: RangeConstraintStrategy,
    
    pub base_field_modulus: BigUint,
    pub represented_field_modulus: BigUint,
    // we calculate maximal value of the limb counting both mandatory and addtional capacity bits
    pub limb_max_value: BigUint,
    pub represented_field_modulus_bitlength: usize, 
    
    pub shift_left_by_limb_constant: E::Fr,
    pub limb_max_value_on_alloc: BigUint,

    // these fields are required only for if_zero method
    pub f_char_mod_fr_char: E::Fr,
    pub f_char_mod_binary_shift: E::Fr,

    pub (crate) _marker_engine: std::marker::PhantomData<E>,
    pub (crate) _marker_fr: std::marker::PhantomData<F>
}

impl<'a, E: Engine, F: PrimeField> RnsParameters<E, F>{
    pub fn new_optimal<CS>(cs: &mut CS, limb_size: usize, min_additional_capacity_bits: usize) -> Self 
    where CS: ConstraintSystem<E>
    {
        // we have to find minimal number of limbs in binary representation. 
        // the following relation should hold: 2^{num_limbs * limb_size} * E::Fr >= (F::char)^2
        let strategy = get_optimal_strategy(cs);
        let range_check_granularity = strategy.get_range_check_granularity();
        assert!(limb_size % range_check_granularity == 0, "limb size is not a multiple of range check quant");

        let base_field_modulus = repr_to_biguint::<E::Fr>(&E::Fr::char());
        let represented_field_modulus = repr_to_biguint::<F>(&F::char());
        let represented_field_modulus_bitlength = represented_field_modulus.bits();

        let mut t = represented_field_modulus.pow(2);
        t = (t + base_field_modulus.clone() - BigUint::one()) / base_field_modulus.clone();
        let num_binary_limbs = t.bits() as usize / limb_size;

        let rem = min_additional_capacity_bits % range_check_granularity;
        let additional_capacity_bits =  if rem == 0 { 0 } else { range_check_granularity - rem };
        let binary_limb_capacity = limb_size + additional_capacity_bits + range_check_granularity;  

        let limb_max_value = (BigUint::one() << binary_limb_capacity) - BigUint::one(); 
        let shift = BigUint::one() << limb_size;
        let shift_left_by_limb_constant = biguint_to_fe::<E::Fr>(shift.clone());
        let limb_max_value_on_alloc = shift.clone() - BigUint::one();

        // (verifying that k * Fr::modulus != 0 (mod 2^{limb_width}) for all positive values of k, such that:
        // bitlength(k * Fr::modulus) <= represented_field_modulus_bitlength bits
        // for the testimony of the necessity of this check look the comments in "iz_zero" function
        let mut multiple_of_fr_char = base_field_modulus.clone();
        while multiple_of_fr_char.bits() <= represented_field_modulus_bitlength {
            if (multiple_of_fr_char.clone() % shift.clone()).is_zero() {
                panic!("k * Fr::modulus == 0 (mod 2^limb_width)");
            }
            multiple_of_fr_char += base_field_modulus.clone(); 
        }

        let f_char_mod_fr_char = biguint_to_fe::<E::Fr>(represented_field_modulus.clone());
        let f_char_mod_binary_shift = biguint_to_fe::<E::Fr>(represented_field_modulus.clone() % shift);

        RnsParameters::<E, F> {
            binary_limb_width : limb_size,
            num_binary_limbs,
            binary_limb_capacity,
            range_check_strategy : strategy,
            base_field_modulus,
            represented_field_modulus,
            represented_field_modulus_bitlength : represented_field_modulus_bitlength as usize,
            limb_max_value, 
            shift_left_by_limb_constant,
            limb_max_value_on_alloc,
            f_char_mod_fr_char,
            f_char_mod_binary_shift,
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
        if let Some(v) = self.get_binary_value() {
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


pub fn split_into_limbs<E: Engine, F: PrimeField>(value: F, params: &RnsParameters<E, F>) -> (Vec<E::Fr>, E::Fr) {
    let value_as_bigint = fe_to_biguint(&value);
    let binary_limb_values = split_into_fixed_number_of_limbs(
        value_as_bigint, params.binary_limb_width, params.num_binary_limbs
    );
    assert_eq!(binary_limb_values.len(), params.num_binary_limbs);

    let base_limb = fe_to_biguint(&value) % &params.base_field_modulus;
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
pub fn slice_into_limbs_non_exact(
    value: Option<BigUint>, max_width: usize, limb_width: usize
) -> (Vec<Option<BigUint>>, usize, BigUint) 
{
    let rem = max_width % limb_width;
    let highest_limb_bit_width = if rem == 0 { limb_width } else { rem };
    let num_limbs = (max_width + limb_width - 1) / limb_width;
    
    let most_significant_limb_max_value = (BigUint::one() << highest_limb_bit_width) - BigUint::one(); 
    let limbs = split_some_into_fixed_number_of_limbs(value, limb_width, num_limbs);
    
    (limbs, highest_limb_bit_width, most_significant_limb_max_value)
}


impl<'a, E: Engine, F: PrimeField> FieldElement<'a, E, F> {
    pub(crate) fn get_binary_value(&self) -> Option<BigUint> {
        let shift = self.representation_params.binary_limb_width;
        let mut result = BigUint::zero();

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


    // we do not do the range check of the limbs: this function assumes that every limb is at most
    // params.binary_limb_bitwidth bits long
    #[track_caller]
    pub fn alloc_from_limbs_unchecked<CS: ConstraintSystem<E>>(
        cs: &mut CS, raw_limbs: &[Num<E>], params: &'a RnsParameters<E, F>
    ) -> Result<Self, SynthesisError> {
        let max_value = &params.limb_max_value_on_alloc;
        let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);
        
        let mut base_field_lc = LinearCombination::zero();
        let shift_constant = params.shift_left_by_limb_constant;
        let mut current_constant = E::Fr::one();

        for raw_limb in raw_limbs.iter() {
            let limb = match raw_limb {
                Num::Constant(cnst) => Limb::<E>::constant_from_field_value(*cnst),
                Num::Variable(var) => {
                    let term = Term::<E>::from_allocated_num(var.clone());
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
        cs: &mut CS, value: Option<BigUint>, bit_width: usize, params: &'a RnsParameters<E, F>
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

        let (limb_values, left_most_limb_width, left_most_limb_maxval) = slice_into_limbs_non_exact(
            value.clone(), params.represented_field_modulus_bitlength, params.binary_limb_width
        );    
        for (_is_first, is_last, value) in limb_values.into_iter().identify_first_last() 
        {
            let value_as_fe = some_biguint_to_fe::<E::Fr>(&value);
            let a = AllocatedNum::alloc(
                cs, 
                || {
                    Ok(*value_as_fe.get()?)
                }
            )?;

            let max_value = if is_last { left_most_limb_maxval.clone() } else { params.limb_max_value_on_alloc.clone() };
            let bitlength = if is_last { left_most_limb_width } else { params.binary_limb_width };
            let decomposition = constraint_num_bits_ext_with_strategy(cs, &a, bitlength, params.range_check_strategy)?; 
            decompositions.push(decomposition);

            let term = Term::<E>::from_allocated_num(a.clone());
            let limb = Limb::<E>::new(term, max_value);

            binary_limbs_allocated.push(limb);

            base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
            current_constant.mul_assign(&shift_constant);
        }
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

    #[track_caller]
    pub fn alloc<CS>(cs: &mut CS, value: Option<F>, params: &'a RnsParameters<E, F>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> {
        
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
        Self::alloc_impl(cs, value_as_biguint, bit_width, params)
    }

    pub fn constant(v: F, params: &'a RnsParameters<E, F>) -> Self {
        let value = fe_to_biguint(&v);
        let binary_limb_values = split_into_fixed_number_of_limbs(
            value.clone(), params.binary_limb_width, params.num_binary_limbs
        );
        let base_limb_value = value.clone() % &params.base_field_modulus;

        let base_limb = biguint_to_fe::<E::Fr>(base_limb_value.clone());
        let base_limb = Term::<E>::from_constant(base_limb);
        assert_eq!(fe_to_biguint(&v) % &params.base_field_modulus, fe_to_biguint(&base_limb.get_value().unwrap()));

        let mut binary_limbs_allocated = Vec::with_capacity(binary_limb_values.len());
        for l in binary_limb_values.into_iter()
        {
            let f = biguint_to_fe(l.clone());
            let term = Term::<E>::from_constant(f);
            let limb = Limb::<E>::new(term, l);
            binary_limbs_allocated.push(limb);
        }

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

    pub fn is_zero<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(Boolean, Self), SynthesisError> 
    {
        let params = self.representation_params.clone();
        let mut x = self.reduce_if_necessary(cs)?;
       
        // after reduction the value of x is in interval [0; 2*F) and all limbs occupy exactly limb_width bits
        // (i.e. capacity bits are not involved)
        // so, to test if x is zero we need to consider to cases: x == 0 or x == F
        // x == 0 <=> field_limb == 0 and least_significant_binary_limb == 0 
        // (but we should check additionaly check that k * Fr::modulus % 2^{limb_width} != 0 for small positive k)
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

    // we call value to be reduced if it's value fits in [0, 2 * F::char) range and all binary limbs
    // do not overflow (i.e. do not exploit additionally capacity bits)
    fn needs_reduction(&self) -> bool {
        if self.is_constant() {
            return false;
        }

        let max_value = self.get_maximal_possible_stored_value();
        let mut needs_reduction = max_value > self.representation_params.represented_field_modulus;

        let limb_max_value = self.representation_params.limb_max_value_on_alloc.clone();
        for binary_limb in self.binary_limbs.iter() {
            needs_reduction = needs_reduction || (binary_limb.max_value() > limb_max_value);
        }

        needs_reduction
    }

    #[track_caller]
    pub fn reduce_if_necessary<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self, SynthesisError> {
        if self.is_constant() {
            return Ok(self);
        }
        // if self.needs_reduction() {
        //     return self.reduction_impl(cs);
        // }

        Ok(self)
    }

//     #[track_caller]
//     fn reduction_impl<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self, SynthesisError> {
//         let params = self.representation_params;
//         let mut binary_limbs_allocated = Vec::with_capacity(params.num_binary_limbs);
//         let shift_constant = params.shift_left_by_limb_constant;
//         let mut of = Num::zero();
        
//         for limb in self.binary_limbs.iter() {
//             // 
//         }
            
//         for (_is_first, is_last, value) in limb_values.into_iter().identify_first_last() 
//         {
//             let value_as_fe = some_biguint_to_fe::<E::Fr>(&value);
//             let a = AllocatedNum::alloc(
//                 cs, 
//                 || {
//                     Ok(*value_as_fe.get()?)
//                 }
//             )?;

//             let max_value = if is_last { most_significant_limb_max_val } else { params.limb_max_value_on_alloc.clone() };
//             let bitlength = if is_last { most_significant_limb_width } else { params.binary_limb_width };
//             let decomposition = constraint_num_bits_ext_with_strategy(cs, &a, bitlength, params.range_check_strategy)?; 
//             decompositions.push(decomposition);

//             let term = Term::<E>::from_allocated_num(a.clone());
//             let limb = Limb::<E>::new(term, max_value);

//             binary_limbs_allocated.push(limb);

//             base_field_lc.add_assign_variable_with_coeff(&a, current_constant);
//             current_constant.mul_assign(&shift_constant);
//         }
//         binary_limbs_allocated.resize(params.num_binary_limbs, Self::zero_limb());

//     }

//     pub fn add<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//         other: Self
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         let params = self.representation_params;

//         let this = self.reduce_if_necessary(cs)?;
//         let other = other.reduce_if_necessary(cs)?;

//         // perform addition without reduction, so it will eventually be reduced later on

//         let mut new_binary_limbs = vec![];

//         for (l, r) in this.binary_limbs.iter()
//                         .zip(other.binary_limbs.iter()) 
//         {
//             let new_term = l.term.add(cs, &r.term)?;
//             let new_max_value = l.max_value.clone() + &r.max_value;

//             let limb = Limb::<E>::new(new_term, new_max_value);
//             new_binary_limbs.push(limb);
//         }

//         let new_base_limb = this.base_field_limb.add(cs, &other.base_field_limb)?;

//         let new_value = this.get_field_value().add(&other.get_field_value());

//         let new = Self {
//             binary_limbs: new_binary_limbs,
//             base_field_limb: new_base_limb,
//             value: new_value,
//             representation_params: params
//         };

//         Ok((new, (this, other)))
//     }

//     pub fn double<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//     ) -> Result<(Self, Self), SynthesisError> {
//         let params = self.representation_params;

//         let this = self.reduce_if_necessary(cs)?;

//         // perform addition without reduction, so it will eventually be reduced later on

//         let mut two = E::Fr::one();
//         two.double();

//         let mut new_binary_limbs = vec![];

//         for l in this.binary_limbs.iter()
//         {
//             let mut new_term = l.term.clone();
//             new_term.scale(&two);
//             let new_max_value = l.max_value.clone() * BigUint::from(2u64);

//             let limb = Limb::<E>::new(new_term, new_max_value);
//             new_binary_limbs.push(limb);
//         }

//         let mut new_base_limb = this.base_field_limb.clone();
//         new_base_limb.scale(&two);

//         let new_value = this.get_field_value().add(&this.get_field_value());

//         let new = Self {
//             binary_limbs: new_binary_limbs,
//             base_field_limb: new_base_limb,
//             value: new_value,
//             representation_params: params
//         };

//         Ok((new, this))
//     }

//     pub fn sub<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//         other: Self
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         let params = self.representation_params;

//         // subtraction is a little more involved

//         // first do the constrant propagation
//         if self.is_constant() && other.is_constant() {
//             let tmp = self.get_field_value().sub(&other.get_field_value());

//             let new = Self::new_constant(tmp.unwrap(), params);

//             return Ok((new, (self, other)));
//         }

//         if other.is_constant() {
//             let tmp = other.get_field_value().negate();

//             let other_negated = Self::new_constant(tmp.unwrap(), params);

//             // do the constant propagation in addition

//             let (result, (this, _)) = self.add(cs, other_negated)?;

//             return Ok((result, (this, other)));
//         }

//         let this = self.reduce_if_necessary(cs)?;
//         let other = other.reduce_if_necessary(cs)?;

//         // keep track for potential borrows and subtract binary limbs

//         // construct data on from what positions we would borrow

//         let mut borrow_max_values = vec![];
//         let mut borrow_bit_widths = vec![];

//         let mut previous = None;

//         // let mut max_subtracted = BigUint::from(0u64);

//         for l in other.binary_limbs.iter() {
//             let mut max_value = l.max_value();
//             if let Some(previous_shift) = previous.take() {
//                 max_value += BigUint::from(1u64) << (previous_shift - params.binary_limbs_params.limb_size_bits);
//             }

//             let borrow_bits = std::cmp::max(params.binary_limbs_params.limb_size_bits, (max_value.bits() as usize) + 1);

//             borrow_max_values.push(max_value);
//             borrow_bit_widths.push(borrow_bits);

//             previous = Some(borrow_bits);
//         }

//         // now we can determine how many moduluses of the represented field 
//         // we have to add to never underflow

//         let shift = params.binary_limbs_params.limb_size_bits * (params.num_binary_limbs - 1);

//         let mut multiples_to_add_at_least = borrow_max_values.last().unwrap().clone() << shift;
//         multiples_to_add_at_least = multiples_to_add_at_least / &params.represented_field_modulus;

//         let mut multiples = multiples_to_add_at_least * &params.represented_field_modulus;

//         let mut loop_limit = 100;

//         loop {
//             let start = params.binary_limbs_params.limb_size_bits * (params.num_binary_limbs - 1);
//             let end = start + params.binary_limbs_params.limb_size_bits;

//             let slice = get_bit_slice(
//                 multiples.clone(), 
//                 start, 
//                 end
//             );

//             if &slice < borrow_max_values.last().unwrap() {
//                 multiples += &params.represented_field_modulus;
//             } else {
//                 break;
//             }
//             loop_limit -= 1;
//             if loop_limit == 0 {
//                 panic!();
//             }
//         }

//         let multiple_slices = split_into_fixed_number_of_limbs(
//             multiples.clone(), 
//             params.binary_limbs_params.limb_size_bits, 
//             params.num_binary_limbs
//         );

//         // create new limbs

//         let mut previous = None;

//         let last_idx = this.binary_limbs.len() - 1;

//         let mut new_binary_limbs = vec![];

//         let mut new_multiple = BigUint::from(0u64);

//         for (idx, (((l, r), &bits), multiple)) in this.binary_limbs.iter()
//                                             .zip(other.binary_limbs.iter())
//                                             .zip(borrow_bit_widths.iter())
//                                             .zip(multiple_slices.iter())
//                                             .enumerate()
//         {
//             let mut tmp = BigUint::from(1u64) << bits;
//             if let Some(previous_bits) = previous.take() {
//                 if idx != last_idx {
//                     tmp -= BigUint::from(1u64) << (previous_bits - params.binary_limbs_params.limb_size_bits);
//                 } else {
//                     tmp = BigUint::from(1u64) << (previous_bits - params.binary_limbs_params.limb_size_bits);
//                 }
//             }
//             let constant = if idx != last_idx {
//                 tmp + multiple
//             } else {
//                 multiple.clone() - tmp
//             };

//             new_multiple += constant.clone() << (params.binary_limbs_params.limb_size_bits * idx);

//             let constant_as_fe = biguint_to_fe::<E::Fr>(constant.clone());

//             let mut tmp = l.term.clone();
//             tmp.add_constant(&constant_as_fe);

//             let mut other_negated = r.term.clone();
//             other_negated.negate();

//             let r = tmp.add(cs, &other_negated)?;

//             let new_max_value = l.max_value() + constant;

//             let limb = Limb::<E>::new(
//                 r,
//                 new_max_value
//             );

//             new_binary_limbs.push(limb);

//             previous = Some(bits);
//         }

//         // let residue_to_add = multiples % &params.base_field_modulus;
//         let residue_to_add = new_multiple % &params.base_field_modulus;
//         let constant_as_fe = biguint_to_fe::<E::Fr>(residue_to_add.clone());

//         let mut tmp = this.base_field_limb.clone();
//         tmp.add_constant(&constant_as_fe);

//         let mut other_negated = other.base_field_limb.clone();
//         other_negated.negate();

//         let new_base_limb = tmp.add(cs, &other_negated)?;

//         let new_value = this.get_field_value().sub(&other.get_field_value());

//         let new = Self {
//             binary_limbs: new_binary_limbs,
//             base_field_limb: new_base_limb,
//             value: new_value,
//             representation_params: params
//         };

//         Ok((new, (this, other)))
//     }

//     pub fn mul<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//         other: Self
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         let params = self.representation_params;

//         let this = self.reduce_if_necessary(cs)?;
//         let other = other.reduce_if_necessary(cs)?;

//         if this.is_constant() && other.is_constant() {
//             let r = this.get_field_value().mul(&other.get_field_value());
//             let new = Self::new_constant(r.unwrap(), params);

//             return Ok((new, (this, other)));
//         }

//         let (q, r) = match (this.get_value(), other.get_value()) {
//             (Some(t), Some(o)) => {
//                 let value = t * o;
//                 let (q, r) = value.div_rem(&params.represented_field_modulus);

//                 (Some(q), Some(r))
//             }
//             _ => (None, None)
//         };

//         // estimate q bit width
//         let q_max_value = this.get_max_value() * other.get_max_value() / &params.represented_field_modulus;
//         let q_max_bits = q_max_value.bits();
//         let q_elem = Self::coarsely_allocate_for_known_bit_width(cs, q, q_max_bits as usize, params)?;

//         // let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

//         let r_elem = Self::new_allocated(
//             cs, 
//             some_biguint_to_fe(&r), 
//             params
//         )?;

//         // we constraint a * b = q*p + rem

//         Self::constraint_fma_with_multiple_additions(
//             cs, 
//             &this,
//             &other,
//             &[],
//             &q_elem,
//             &[r_elem.clone()],
//         )?;

//         Ok((r_elem, (this, other)))
//     }

//     pub fn square<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//     ) -> Result<(Self, Self), SynthesisError> {
//         let params = self.representation_params;

//         let this = self.reduce_if_necessary(cs)?;

//         if this.is_constant() {
//             let r = this.get_field_value().mul(&this.get_field_value());
//             let new = Self::new_constant(r.unwrap(), params);

//             return Ok((new, this));
//         }

//         let (q, r) = match this.get_value() {
//             Some(t) => {
//                 let value = t.clone() * t;
//                 let (q, r) = value.div_rem(&params.represented_field_modulus);

//                 (Some(q), Some(r))
//             }
//             _ => (None, None)
//         };

//         let r_elem = Self::new_allocated(
//             cs, 
//             some_biguint_to_fe(&r), 
//             params
//         )?;

//         // we constraint a * a = q*p + rem

//         // estimate q bit width
//         let q_max_value = this.get_max_value() * this.get_max_value() / &params.represented_field_modulus;
//         let q_max_bits = q_max_value.bits();
//         let q_elem = Self::coarsely_allocate_for_known_bit_width(cs, q, q_max_bits as usize, params)?;

//         // let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

//         Self::constraint_square_with_multiple_additions(
//             cs, 
//             &this,
//             &[],
//             &q_elem,
//             &[r_elem.clone()],
//         )?;

//         Ok((r_elem, this))
//     }

//     pub fn fma_with_addition_chain<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//         to_mul: Self,
//         to_add: Vec<Self>
//     ) -> Result<(Self, (Self, Self, Vec<Self>)), SynthesisError> {
//         let params = self.representation_params;

//         let mut final_value = self.get_field_value();
//         final_value = final_value.mul(&to_mul.get_field_value());
//         for a in to_add.iter() {
//             final_value = final_value.add(&a.get_field_value());
//         }

//         let this = self.reduce_if_necessary(cs)?;
//         let to_mul = to_mul.reduce_if_necessary(cs)?;

//         let mut value_is_none = false;
//         let mut value = BigUint::from(0u64);
//         match (this.get_value(), to_mul.get_value()) {
//             (Some(t), Some(m)) => {
//                 value += t * m;
//             },
//             _ => {
//                 value_is_none = true;
//             }
//         }
        
//         let mut all_constants = this.is_constant() && to_mul.is_constant();
//         for a in to_add.iter() {
//             if let Some(v) = a.get_value() {
//                 value += v;
//             } else {
//                 value_is_none = true;
//             }
//             all_constants = all_constants & a.is_constant();
//         } 
//         let (q, r) = value.div_rem(&params.represented_field_modulus);

//         if all_constants {
//             let r = biguint_to_fe::<F>(r);
//             let new = Self::new_constant(r, params);
//             return Ok((new, (this, to_mul, to_add)));
//         }

//         let (q, r) = if value_is_none {
//             (None, None)
//         } else {
//             (Some(q), Some(r))
//         };

//         // so we constraint self * to_mul + [to_add] = q * p + r
//         // we we estimate q width

//         let mut lhs_max_value = this.get_max_value() * to_mul.get_max_value();
//         for el in to_add.iter() {
//             lhs_max_value += el.get_max_value();
//         }
//         let q_max_value = lhs_max_value / &params.represented_field_modulus;
//         let q_max_bits = q_max_value.bits();
//         let q_elem = Self::coarsely_allocate_for_known_bit_width(cs, q, q_max_bits as usize, params)?;

//         // let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

//         let r_elem = Self::new_allocated(
//             cs, 
//             some_biguint_to_fe(&r), 
//             params
//         )?;

//         Self::constraint_fma_with_multiple_additions(
//             cs, 
//             &this,
//             &to_mul,
//             &to_add,
//             &q_elem,
//             &[r_elem.clone()],
//         )?;

//         return Ok((r_elem, (this, to_mul, to_add)));
//     }

//     #[track_caller]
//     pub fn div<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//         den: Self,
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         let params = self.representation_params;
//         // we do self/den = result mod p
//         // so we constraint result * den = q * p + self

//         // Self::div_from_addition_chain(
//         //     cs,
//         //     &[self.clone()],
//         //     den
//         // )

//         // code here is duplicated a little to avoid reduction mess

//         let this = self.reduce_if_necessary(cs)?;
//         let den = den.reduce_if_necessary(cs)?;

//         if this.is_constant() && den.is_constant() {
//             let mut tmp = den.get_field_value().unwrap().inverse().unwrap();
//             tmp.mul_assign(&this.get_field_value().unwrap());

//             let new = Self::new_constant(tmp, params);

//             return Ok((new, (this, den)));
//         }

//         let (_inv, result, q, _rem) = match (this.get_value(), den.get_value()) {
//             (Some(this), Some(den)) => {
//                 let inv = mod_inverse(&den, &params.represented_field_modulus);
//                 let result = (this.clone() * &inv) % &params.represented_field_modulus;

//                 let value = den.clone() * &result - &this;
//                 let (q, rem) = value.div_rem(&params.represented_field_modulus);

//                 use crate::num_traits::Zero;
//                 assert!(rem.is_zero(), "remainder = {}", rem.to_str_radix(16));

//                 (Some(inv), Some(result), Some(q), Some(rem))
//             },
//             _ => {
//                 (None, None, None, None)
//             }
//         };

//         let inv_wit = Self::new_allocated(
//             cs, 
//             some_biguint_to_fe::<F>(&result),
//             params
//         )?;

//         // estimate q bit width
//         // result * den = q * p + self, so we say that self min value == 0 (as it goes into LHS with - sign) and worst case for q is

//         let q_max_value = inv_wit.get_max_value() * den.get_max_value() / &params.represented_field_modulus;
//         let q_max_bits = q_max_value.bits();
//         let q_elem = Self::coarsely_allocate_for_known_bit_width(cs, q, q_max_bits as usize, params)?;

//         // let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

//         Self::constraint_fma_with_multiple_additions(
//             cs, 
//             &den,
//             &inv_wit,
//             &[],
//             &q_elem,
//             &[this.clone()],
//         )?;

//         Ok((inv_wit, (this, den)))
//     }

//     #[track_caller]
//     pub(crate) fn div_from_addition_chain<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         nums: Vec<Self>,
//         den: Self
//     ) -> Result<(Self, (Vec<Self>, Self)), SynthesisError> {
//         let params = den.representation_params;

//         // we do (a1 + a2 + ... + an) /den = result mod p
//         // a1 + a2 + ... + an = result * den mod p
//         // result*den = q*p + (a1 + a2 + ... + an)
//         // so we place nums into the remainders (don't need to negate here)

//         let den = den.reduce_if_necessary(cs)?;

//         let mut value_is_none = false;

//         let inv = if let Some(den) = den.get_value() {
//             let inv = mod_inverse(&den, &params.represented_field_modulus);

//             Some(inv)
//         } else {
//             value_is_none = true;

//             None
//         };

//         let mut num_value = BigUint::from(0u64);
//         let mut all_constant = den.is_constant();

//         let mut reduced_nums = Vec::with_capacity(nums.len());

//         for n in nums.into_iter() {
//             let n = n.reduce_if_necessary(cs)?;
//             if let Some(value) = n.get_value() {
//                 num_value += value;
//             } else {
//                 value_is_none = true;
//             }

//             all_constant = all_constant & n.is_constant();
//             reduced_nums.push(n);
//         }
//         let num_value = if value_is_none {
//             None
//         } else {
//             Some(num_value)
//         };

//         let (result, q, _rem) = match (num_value, den.get_value(), inv.clone()) {
//             (Some(num_value), Some(den), Some(inv)) => {
//                 let mut lhs = num_value.clone();

//                 let mut rhs = BigUint::from(0u64);

//                 let result = (num_value.clone() * &inv) % &params.represented_field_modulus;

//                 rhs += result.clone() * &den;
//                 let value = den * &result - num_value;
        
//                 let (q, rem) = value.div_rem(&params.represented_field_modulus);

//                 lhs += q.clone() * &params.represented_field_modulus;

//                 assert_eq!(lhs, rhs);
        
//                 use crate::num_traits::Zero;
//                 assert!(rem.is_zero(), "remainder = {}", rem.to_str_radix(16));

//                 (Some(result), Some(q), Some(rem))
//             },
//             _ => {
//                 (None, None, None)
//             }
//         };

//         if all_constant {
//             let v = biguint_to_fe::<F>(result.unwrap());
//             let new = Self::new_constant(v, params);
//             return Ok((new, (reduced_nums, den)));
//         }

//         let result_wit = Self::new_allocated(
//             cs, 
//             some_biguint_to_fe::<F>(&result),
//             params
//         )?;

//         // result*den = q*p + (a1 + a2 + ... + an), but since we have to subtract (a1 + a2 + ... + an) we do not use them
//         // in this estimation
//         let q_max_value = result_wit.get_max_value() * den.get_max_value() / &params.represented_field_modulus;
//         let q_max_bits = q_max_value.bits();
//         let q_elem = Self::coarsely_allocate_for_known_bit_width(cs, q, q_max_bits as usize, params)?;

//         // let q_elem = Self::coarsely_allocate_for_unknown_width(cs, q, params)?;

//         Self::constraint_fma_with_multiple_additions(
//             cs, 
//             &den,
//             &result_wit,
//             &[],
//             &q_elem,
//             &reduced_nums,
//         )?;

//         Ok((result_wit, (reduced_nums, den)))
//     }

//     // returns first if true and second if false
//     pub fn select<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         flag: &Boolean,
//         first: Self,
//         second: Self
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         match flag {
//             Boolean::Constant(c) => {
//                 if *c {
//                     return Ok((first.clone(), (first, second)));
//                 } else {
//                     return Ok((second.clone(), (first, second)));
//                 }
//             },
//             _ => {}
//         }

//         let first = first.reduce_if_necessary(cs)?;
//         let second = second.reduce_if_necessary(cs)?;

//         let flag_as_term = Term::<E>::from_boolean(flag);

//         // flag * a + (1-flag)*b = flag * (a-b) + b

//         let mut new_binary_limbs = vec![];

//         for (l, r) in first.binary_limbs.iter()
//                     .zip(second.binary_limbs.iter()) 
//         {
//             let mut minus_b = r.term.clone();
//             minus_b.negate();
//             let a_minus_b = l.term.add(cs, &minus_b)?;

//             let n = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &r.term)?;

//             let new_max = std::cmp::max(l.max_value(), r.max_value());

//             let new_limb = Limb::new(
//                 n,
//                 new_max
//             );

//             new_binary_limbs.push(new_limb);
//         }

//         let mut minus_b = second.base_field_limb.clone();
//         minus_b.negate();
//         let a_minus_b = first.base_field_limb.add(cs, &minus_b)?;

//         let new_base_limb = Term::<E>::fma(cs, &flag_as_term, &a_minus_b, &second.base_field_limb)?;

//         let new_value = if let Some(f) = flag.get_value() {
//             if f {
//                 first.get_field_value()
//             } else {
//                 second.get_field_value()
//             }
//         } else {
//             None
//         };

//         let new = Self {
//             binary_limbs: new_binary_limbs,
//             base_field_limb: new_base_limb,
//             value: new_value,
//             representation_params: first.representation_params
//         };

//         Ok((new, (first, second)))
//     }

//     // negates if true
//     pub fn conditional_negation<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         flag: &Boolean,
//         this: Self,
//     ) -> Result<(Self, (Self, Self)), SynthesisError> {
//         let (negated, this) = this.negated(cs)?;

//         let (selected, (negated, this)) = Self::select(cs, flag, negated, this)?;

//         Ok((selected, (this, negated)))
//     }

//     /// check that element is in a field and is strictly less
//     /// than modulus
//     pub fn enforce_is_normalized<CS: ConstraintSystem<E>>(
//         self,
//         cs: &mut CS,
//     ) -> Result<Self, SynthesisError> {
//         if self.is_constant() {
//             return Ok(self);
//         }

//         let params = self.representation_params;

//         let this = self.reduce_if_necessary(cs)?;

//         let modulus_limbs = split_into_fixed_number_of_limbs(
//             params.represented_field_modulus.clone(), 
//             params.binary_limbs_params.limb_size_bits, 
//             params.num_binary_limbs
//         ); 

//         let borrow_witnesses = if let Some(v) = this.get_value() {
//             let value_limbs = split_into_fixed_number_of_limbs(
//                 v, 
//                 params.binary_limbs_params.limb_size_bits, 
//                 params.num_binary_limbs
//             ); 
//             let mut wit = Vec::with_capacity(params.num_binary_limbs - 1);

//             let mut previous = None;

//             for (m, v) in modulus_limbs.iter().zip(value_limbs.into_iter()).rev().skip(1).rev() {
//                 let mut v = v;
//                 if let Some(p) = previous.take() {
//                     v -= p;
//                 }
//                 if &v > m {
//                     wit.push(Some(true));
//                     previous = Some(BigUint::from(1u64));
//                 } else {
//                     wit.push(Some(false));
//                     previous = Some(BigUint::from(0u64));
//                 }
//             }

//             assert_eq!(wit.len(), params.num_binary_limbs - 1);

//             wit
//         } else {
//             vec![None; params.num_binary_limbs - 1]
//         };

//         let mut modulus_limbs_as_fe = Vec::with_capacity(modulus_limbs.len());
//         for m in modulus_limbs.into_iter() {
//             let m = biguint_to_fe::<E::Fr>(m);
//             modulus_limbs_as_fe.push(m);
//         }

//         let mut borrow_bits = vec![];
//         for w in borrow_witnesses.into_iter() {
//             let b = Boolean::from(AllocatedBit::alloc(
//                 cs,
//                 w
//             )?);
//             borrow_bits.push(b)
//         }

//         let mut previous = None;

//         let mut results = Vec::with_capacity(params.num_binary_limbs);

//         for ((l, b), m) in this.binary_limbs.iter()
//                             .zip(borrow_bits.into_iter())
//                             .zip(modulus_limbs_as_fe.iter()) 
//         {
//             let mut tmp = l.term.clone();
//             tmp.negate();
//             tmp.add_constant(m);

//             let mut this_borrow = Term::<E>::from_boolean(&b);
//             this_borrow.scale(&params.binary_limbs_params.shift_left_by_limb_constant);

//             if let Some(p) = previous {
//                 let mut previous_borrow = Term::<E>::from_boolean(&p);
//                 previous_borrow.negate();

//                 let r = tmp.add_multiple(cs, &[this_borrow, previous_borrow])?;
//                 results.push(r);
//             } else {
//                 let r = tmp.add(cs, &this_borrow)?;
//                 results.push(r);
//             }

//             previous = Some(b);
//         }

//         assert!(previous.is_some());

//         let p = previous.unwrap();

//         let mut tmp = this.binary_limbs.last().unwrap().term.clone();
//         tmp.negate();
//         tmp.add_constant(modulus_limbs_as_fe.last().unwrap());

//         let mut previous_borrow = Term::<E>::from_boolean(&p);
//         previous_borrow.negate();
//         let r = tmp.add(cs, &previous_borrow)?;
//         results.push(r);

//         for r in results.into_iter() {
//             let el = r.collapse_into_num(cs)?;
//             let el = el.get_variable();
//             let expected_width = params.binary_limbs_params.limb_size_bits;
//             match params.range_check_info.strategy {
//                 RangeConstraintStrategy::MultiTable => {
//                     self::range_constraint_functions::coarsely_enforce_using_multitable(cs, &el, expected_width)?;
//                 },
//                 RangeConstraintStrategy::SingleTableInvocation => {
//                     self::single_table_range_constraint::enforce_using_single_column_table(cs, &el, expected_width)?;
//                 },
//                 RangeConstraintStrategy::CustomTwoBitGate => {
//                     let _ = create_range_constraint_chain(cs, &el, expected_width)?;
//                 }
//                 _ => {unimplemented!("range constraint strategies other than multitable, single table or custom gate are not yet handled")}
//             }
//         }

//         Ok(this)
//     }

//     #[track_caller]
//     pub fn enforce_equal<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         this: Self,
//         other: Self
//     ) -> Result<(), SynthesisError> {
//         match (this.is_constant(), other.is_constant()) {
//             (true, true) => {
//                 let a = this.get_field_value().unwrap();
//                 let b = other.get_field_value().unwrap();
//                 assert!(a == b);

//                 return Ok(())
//             },
//             _ => {

//             }
//         };

//         let before = cs.get_current_step_number();

//         let this = this.force_reduce_close_to_modulus(cs)?.enforce_is_normalized(cs)?;
//         let other = other.force_reduce_close_to_modulus(cs)?.enforce_is_normalized(cs)?;

//         for (a, b) in this.binary_limbs.iter().zip(other.binary_limbs.iter()) {
//             let a = a.term.into_num();
//             let b = b.term.into_num();
//             a.enforce_equal(cs, &b)?;
//         }

//         let a = this.base_field_limb.into_num();
//         let b = other.base_field_limb.into_num();

//         a.enforce_equal(cs, &b)?;

//         crate::plonk::circuit::counter::increment_counter_by(cs.get_current_step_number() - before);

//         Ok(())
//     }
        
//     #[track_caller]
//     pub fn equals<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         this: Self,
//         other: Self
//     ) -> Result<(Boolean, (Self, Self)), SynthesisError> {
//         match (this.is_constant(), other.is_constant()) {
//             (true, true) => {
//                 let a = this.get_field_value().unwrap();
//                 let b = other.get_field_value().unwrap();

//                 return Ok((Boolean::constant(a == b), (this, other)));
//             },
//             _ => {

//             }
//         };

//         let before = cs.get_current_step_number();

//         let this = this.force_reduce_close_to_modulus(cs)?;
//         let other = other.force_reduce_close_to_modulus(cs)?;

//         let result = Self::equals_assuming_reduced(cs, this.clone(), other.clone())?;

//         crate::plonk::circuit::counter::increment_counter_by(cs.get_current_step_number() - before);

//         Ok((result, (this, other)))
//     }

//     #[track_caller]
//     pub fn equals_assuming_reduced<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         first: Self,
//         second: Self
//     ) -> Result<Boolean, SynthesisError> {
//         match (first.is_constant(), second.is_constant()) {
//             (true, true) => {
//                 let a = first.get_field_value().unwrap();
//                 let b = second.get_field_value().unwrap();

//                 return Ok(Boolean::constant(a == b));
//             },
//             _ => {

//             }
//         };

//         let mut lc = LinearCombination::zero();

//         let this = first.enforce_is_normalized(cs)?;
//         let other = second.enforce_is_normalized(cs)?;

//         for (a, b) in this.binary_limbs.iter().zip(other.binary_limbs.iter()) {
//             let a = a.term.collapse_into_num(cs)?;
//             let b = b.term.collapse_into_num(cs)?;
//             let not_equal = Num::equals(cs, &a, &b)?.not();
//             lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());
//         }

//         let a = this.base_field_limb.collapse_into_num(cs)?;
//         let b = other.base_field_limb.collapse_into_num(cs)?;
//         let not_equal = Num::equals(cs, &a, &b)?.not();
//         lc.add_assign_boolean_with_coeff(&not_equal, E::Fr::one());

//         let as_num = lc.into_num(cs)?;
//         // if any of the terms was not equal then lc != 0
//         let equal = as_num.is_zero(cs)?;

//         Ok(equal)
//     }

//     #[track_caller]
//     pub fn enforce_not_equal<CS: ConstraintSystem<E>>(
//         cs: &mut CS,
//         this: Self,
//         other: Self
//     ) -> Result<(Self, Self), SynthesisError> {
//         let this = this.force_reduce_close_to_modulus(cs)?;
//         let other = other.force_reduce_close_to_modulus(cs)?;
//         let equal = Self::equals_assuming_reduced(cs, this.clone(), other.clone())?;
//         Boolean::enforce_equal(cs, &equal, &Boolean::constant(false))?;

//         Ok((this, other))
//     }
// }

// pub mod test {
//     use super::*;
//     use crate::plonk::circuit::*;

//     #[test]
//     pub fn test_bn_254() {
//         use crate::bellman::pairing::bn256::{Fq, Bn256, Fr};

//         let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

//         let init_function = move || {
//             let cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();

//             cs
//         };

//         test_allocation_on_random_witnesses(&params, &init_function);
//         test_add_on_random_witnesses(&params, &init_function);
//         test_sub_on_random_witnesses(&params, &init_function);
//         test_mul_on_random_witnesses(&params, &init_function);
//         test_square_on_random_witnesses(&params, &init_function);
//         test_negation_on_random_witnesses(&params, &init_function);
//         test_equality_on_random_witnesses(&params, &init_function);
//         test_non_equality_on_random_witnesses(&params, &init_function);
//         test_select_on_random_witnesses(&params, &init_function);
//         test_conditional_negation_on_random_witnesses(&params, &init_function);
//         test_long_addition_chain_on_random_witnesses(&params, &init_function);
//         test_long_negation_chain_on_random_witnesses(&params, &init_function);
//         test_long_subtraction_chain_on_random_witnesses(&params, &init_function);
//         test_inv_mul_on_random_witnesses(&params, &init_function);
//     }

//     #[test]
//     fn test_bls_12_381() {
//         use crate::bellman::pairing::bls12_381::{Bls12, Fr, Fq};

//         let params = RnsParameters::<Bls12, Fq>::new_for_field(64, 110, 8);
//         // let params = RnsParameters::<Bls12, Fq>::new_for_field(88, 120, 6);

//         println!("Max representable = {}, with {} bits", params.max_representable_value().to_str_radix(16), params.max_representable_value().bits());

//         let init_function = move || {
//             let cs = TrivialAssembly::<Bls12, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

//             cs
//         };

//         test_allocation_on_random_witnesses(&params, &init_function);
//         test_add_on_random_witnesses(&params, &init_function);
//         test_sub_on_random_witnesses(&params, &init_function);
//         test_mul_on_random_witnesses(&params, &init_function);
//         test_square_on_random_witnesses(&params, &init_function);
//         test_negation_on_random_witnesses(&params, &init_function);
//         test_equality_on_random_witnesses(&params, &init_function);
//         test_non_equality_on_random_witnesses(&params, &init_function);
//         test_select_on_random_witnesses(&params, &init_function);
//         test_conditional_negation_on_random_witnesses(&params, &init_function);
//         test_long_addition_chain_on_random_witnesses(&params, &init_function);
//         test_long_negation_chain_on_random_witnesses(&params, &init_function);
//         test_long_subtraction_chain_on_random_witnesses(&params, &init_function);
//         test_inv_mul_on_random_witnesses(&params, &init_function);
//     }


//     fn test_mul_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..1 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f),
//                 &params
//             ).unwrap();

//             let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
//             let (result, (a, b)) = a.mul(&mut cs, b).unwrap();

//             assert!(cs.is_satisfied());

//             let mut m = a_f;
//             m.mul_assign(&b_f);

//             assert_eq!(result.value.unwrap(), m);
//             println!("a_full: {}, b_full: {}, res_full: {}", a.get_value().unwrap(), b.get_value().unwrap(),
//             result.get_value().unwrap());
//             println!("a_fr: {}, b_fr: {}, res_fr: {}", a.base_field_limb.get_value().unwrap(), b.base_field_limb.get_value().unwrap(),
//             result.base_field_limb.get_value().unwrap());
//             assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

//             if i == 0 {
//                 let a = a.reduce_if_necessary(&mut cs).unwrap();
//                 let _b = b.reduce_if_necessary(&mut cs).unwrap();
//                 let base = cs.n();
//                 use std::sync::atomic::Ordering;
//                 let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
//                 let _ = result.mul(&mut cs, a).unwrap();
//                 let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
//                 println!("Single multiplication taken {} gates", cs.n() - base);
//                 println!("Range checks take {} gates", k);
//             }
//         }
//     }

//     fn test_allocation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_const = FieldElement::new_constant(
//                 a_f, 
//                 &params
//             );

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
//             assert_eq!(a_base, a_const.base_field_limb.get_value().unwrap());

//             for (l, r) in a.binary_limbs.iter().zip(a_const.binary_limbs.iter()) {
//                 assert_eq!(l.get_field_value().unwrap(), r.get_field_value().unwrap());
//                 assert_eq!(l.get_value().unwrap(), r.get_value().unwrap());
//             }
//         }
//     }

//     fn test_equality_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_const = FieldElement::new_constant(
//                 a_f, 
//                 &params
//             );

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, a.clone(), b.clone()).unwrap();
//             let _ = FieldElement::enforce_equal(&mut cs, a.clone(), a_const.clone()).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_non_equality_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();

//             let _a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let _a_const = FieldElement::new_constant(
//                 a_f, 
//                 &params
//             );

//             let _b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f), 
//                 &params
//             ).unwrap();

//             let _b_const = FieldElement::new_constant(
//                 b_f, 
//                 &params
//             );

//             //TODO

//             // a.enforce_not_equal(&mut cs, &b).unwrap();
//             // a.enforce_not_equal(&mut cs, &b_const).unwrap();
//             // a_const.enforce_not_equal(&mut cs, &b_const).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_negation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let mut neg = a_f;
//             neg.negate();

//             let n_const = FieldElement::new_constant(neg, &params);

//             let (n, a) = a.negated(&mut cs).unwrap();
//             assert!(n.get_value().unwrap() <= n.get_max_value());

//             let n = n.reduction_impl(&mut cs).unwrap();
//             let _ = FieldElement::enforce_equal(&mut cs, n.clone(), n_const.clone()).unwrap();

//             let (nn, _n) = n.negated(&mut cs).unwrap();
//             let nn = nn.reduction_impl(&mut cs).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, nn.clone(), a.clone()).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_square_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let _b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
    
//             // let (result, (a, _)) = a.square_with_addition_chain(&mut cs, vec![]).unwrap();

//             let (result, a) = a.square(&mut cs).unwrap();

//             assert!(cs.is_satisfied());

//             let mut m = a_f;
//             m.square();

//             assert_eq!(result.value.unwrap(), m);

//             assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));

//             // let mut ab_in_base_field = a_base;
//             // ab_in_base_field.mul_assign(&b_base);

//             // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

//             if i == 0 {
//                 let a = a.reduce_if_necessary(&mut cs).unwrap();
//                 let base = cs.n();
//                 use std::sync::atomic::Ordering;
//                 let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst);
//                 let _ = a.square_with_addition_chain(&mut cs, vec![]).unwrap();
//                 let k = super::super::RANGE_GATES_COUNTER.load(Ordering::SeqCst) - k;
//                 println!("Single squaring taken {} gates", cs.n() - base);
//                 println!("Range checks take {} gates", k);
//             }
//         }
//     }

//     fn test_add_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f),
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
//             assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
//             let (result, (a, _b)) = a.add(&mut cs, b).unwrap();

//             assert!(cs.is_satisfied());

//             let mut m = a_f;
//             m.add_assign(&b_f);

//             let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
//             assert_eq!(res, fe_to_biguint(&m));

//             assert_eq!(result.value.unwrap(), m);

//             // let mut ab_in_base_field = a_base;
//             // ab_in_base_field.add_assign(&b_base);

//             // assert_eq!(result.base_field_limb.get_value().unwrap(), ab_in_base_field);

//             if i == 0 {
//                 let t0 = a.reduce_if_necessary(&mut cs).unwrap();
//                 let t1 = result.reduce_if_necessary(&mut cs).unwrap();
//                 assert!(t0.needs_reduction() == false);
//                 assert!(t1.needs_reduction() == false);
//                 let base = cs.n();
//                 let _ = t0.add(&mut cs, t1).unwrap();
//                 println!("Single addition taken {} gates", cs.n() - base);
//             }
//         }
//     }

//     fn test_long_addition_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..10 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let _b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let mut t = a;

//             for _ in 0..100 {
//                 let (tt, _) = t.clone().add(&mut cs, t).unwrap();
//                 t = tt;
//             }

//             let another = FieldElement::new_allocated(
//                 &mut cs, 
//                 t.get_field_value(), 
//                 &params
//             ).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_long_subtraction_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..10 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let _b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let mut t = a;

//             for _ in 0..100 {
//                 let (tt, _) = t.clone().sub(&mut cs, t).unwrap();
//                 t = tt;
//             }

//             let another = FieldElement::new_allocated(
//                 &mut cs, 
//                 t.get_field_value(), 
//                 &params
//             ).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_long_negation_chain_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..10 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let _b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let mut t = a;

//             for _ in 0..100 {
//                 let (tt, _) = t.negated(&mut cs).unwrap();
//                 t = tt;
//             }

//             let another = FieldElement::new_allocated(
//                 &mut cs, 
//                 t.get_field_value(), 
//                 &params
//             ).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, another, t).unwrap();

//             assert!(cs.is_satisfied());
//         }
//     }

//     fn test_sub_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f),
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
//             assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
//             let (result, (a, b)) = a.sub(&mut cs, b).unwrap();

//             assert!(cs.is_satisfied());

//             let mut m = a_f;
//             m.sub_assign(&b_f);

//             let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
//             assert_eq!(res, fe_to_biguint(&m));

//             assert_eq!(result.value.unwrap(), m);

//             let (rr, (_b, a)) = b.sub(&mut cs, a).unwrap();

//             let (rrr, rr) = rr.negated(&mut cs).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, rrr.clone(), result.clone()).unwrap();

//             let (rrrr, _rrr) = rrr.negated(&mut cs).unwrap();

//             let _ = FieldElement::enforce_equal(&mut cs, rrrr, rr).unwrap();

//             if i == 0 {
//                 let t0 = a.reduce_if_necessary(&mut cs).unwrap();
//                 let t1 = result.reduce_if_necessary(&mut cs).unwrap();
//                 let base = cs.n();
//                 let _ = t0.sub(&mut cs, t1).unwrap();
//                 println!("Single subtraction taken {} gates", cs.n() - base);
//             }
//         }
//     }

//     fn test_select_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..100 {
//             let mut cs = init();

//             let flag: bool = rng.gen();

//             use crate::plonk::circuit::boolean::AllocatedBit;

//             let bit = AllocatedBit::alloc(
//                 &mut cs,
//                 Some(flag)
//             ).unwrap();

//             let bit = Boolean::Not(bit);
//             // let bit = Boolean::Is(bit);

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f),
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());
//             assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
//             let (result, (a, _)) = FieldElement::select(&mut cs, &bit, a, b).unwrap();

//             assert!(cs.is_satisfied());

//             let m = if !flag {
//                 a_f
//             }  else {
//                 b_f
//             };

//             let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
//             assert_eq!(res, fe_to_biguint(&m));

//             assert_eq!(result.value.unwrap(), m);

//             if i == 0 {
//                 let t0 = a.reduce_if_necessary(&mut cs).unwrap();
//                 let t1 = result.reduce_if_necessary(&mut cs).unwrap();
//                 let base = cs.n();
//                 let _ = FieldElement::select(&mut cs, &bit, t0, t1).unwrap();
//                 println!("Single selection taken {} gates", cs.n() - base);
//             }
//         }
//     }

//     fn test_conditional_negation_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for i in 0..100 {
//             let mut cs = init();

//             let flag: bool = rng.gen();

//             use crate::plonk::circuit::boolean::AllocatedBit;

//             let bit = AllocatedBit::alloc(
//                 &mut cs,
//                 Some(flag)
//             ).unwrap();

//             let bit = Boolean::Not(bit);
//             // let bit = Boolean::Is(bit);

//             let a_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));

//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

//             let (result, (a, minus_a)) = FieldElement::conditional_negation(&mut cs, &bit, a).unwrap();

//             let mut minus_a_f = a_f;
//             minus_a_f.negate();

//             assert_eq!(minus_a.get_field_value().unwrap(), minus_a_f);
//             assert_eq!(a.get_field_value().unwrap(), a_f);

//             assert_eq!(minus_a.get_value().unwrap() % repr_to_biguint::<F>(&F::char()), fe_to_biguint(&minus_a_f));
//             assert_eq!(a.get_value().unwrap() % repr_to_biguint::<F>(&F::char()), fe_to_biguint(&a_f));

//             assert!(cs.is_satisfied());

//             let m = if flag {
//                 a_f
//             }  else {
//                 minus_a_f
//             };

//             let res = result.get_value().unwrap() % repr_to_biguint::<F>(&F::char());
//             assert_eq!(res, fe_to_biguint(&m));

//             assert_eq!(result.value.unwrap(), m);

//             if i == 0 {
//                 let t0 = a.reduce_if_necessary(&mut cs).unwrap();
//                 let base = cs.n();
//                 let _ = FieldElement::conditional_negation(&mut cs, &bit, t0).unwrap();
//                 println!("Conditional negation taken {} gates", cs.n() - base);
//             }
//         }
//     }

//     fn test_inv_mul_on_random_witnesses<E: Engine, F: PrimeField, P: PlonkConstraintSystemParams<E>, I: Fn() -> TrivialAssembly::<E, P, Width4MainGateWithDNext>>(
//         params: &RnsParameters<E, F>,
//         init: &I
//     ){
//         use rand::{XorShiftRng, SeedableRng, Rng};
//         let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//         for _i in 0..100 {
//             let mut cs = init();

//             let a_f: F = rng.gen();
//             let b_f: F = rng.gen();
//             let a = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(a_f), 
//                 &params
//             ).unwrap();

//             let a_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&a_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(a_base, a.base_field_limb.get_value().unwrap());

//             let b = FieldElement::new_allocated(
//                 &mut cs, 
//                 Some(b_f),
//                 &params
//             ).unwrap();

//             let b_base = biguint_to_fe::<E::Fr>(fe_to_biguint(&b_f) % repr_to_biguint::<E::Fr>(&E::Fr::char()));
//             assert_eq!(b_base, b.base_field_limb.get_value().unwrap());
    
//             let (result, _) = a.div(&mut cs, b).unwrap();

//             assert!(cs.is_satisfied());

//             let mut m = b_f.inverse().unwrap();
//             m.mul_assign(&a_f);

//             assert_eq!(result.value.unwrap(), m);

//             assert_eq!(result.get_value().unwrap(), fe_to_biguint(&m));
//         }
//     }
}
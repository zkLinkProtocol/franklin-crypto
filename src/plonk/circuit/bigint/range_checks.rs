use super::*;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::plonk::circuit::linear_combination::*;


pub static NUM_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
// shorts range checks are range checks that occupy a single gate
pub static NUM_SHORT_RANGE_CHECK_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);
pub static NUM_GATES_SPENT_ON_RANGE_CHECKS: AtomicUsize = AtomicUsize::new(0);

pub fn reset_stats() {
    NUM_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.store(0, Ordering::Relaxed);
    NUM_GATES_SPENT_ON_RANGE_CHECKS.store(0, Ordering::Relaxed);
}

fn increment_invocation_count() {
    NUM_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_short_checks_count() {
    NUM_SHORT_RANGE_CHECK_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
}

fn increment_total_gates_count(val: usize) {
    NUM_GATES_SPENT_ON_RANGE_CHECKS.fetch_add(val, Ordering::SeqCst);
}

pub fn print_stats() {
    let total_checks = NUM_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let short_checks = NUM_SHORT_RANGE_CHECK_INVOCATIONS.load(Ordering::Relaxed);
    let total_gates = NUM_GATES_SPENT_ON_RANGE_CHECKS.load(Ordering::Relaxed);
    println!(
        "Has made in total of {} range checks, with {} being short (singe gate) and {} gates in total", 
        total_checks, short_checks, total_gates
    );
}


pub enum DecompositionType<E: Engine> {
    BitDecomposition(Vec<AllocatedBit>),
    ChunkDecomposition(Vec<AllocatedNum<E>>),
}

pub struct RangeCheckDecomposition<E: Engine>
{
    chunks_bitlength: usize,
    decomposition: DecompositionType<E>
}


// enforces that bitlength(var) <= shift and returns the decomposition of var into smaller chunks
// the actual bitsize and type of chunks depends on the chosen strategy
pub fn constraint_num_bits_ext<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize
) -> Result<RangeCheckDecomposition<E>, SynthesisError> {
    let range_check_strategy = get_optimal_strategy(cs);
    let shift = E::Fr::one();
    match range_check_strategy {
        RangeConstraintStrategy::NaiveSingleBit => enforce_range_check_using_naive_approach(cs, var, shift, num_bits),
        RangeConstraintStrategy::CustomTwoBitGate => enforce_range_check_using_custom_gate(cs, var, shift, num_bits),
        RangeConstraintStrategy::WithBitwiseOpTable => enforce_range_check_using_bitop_table(cs, var, shift, num_bits)    
    }
}

pub fn constraint_num_bits<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, num_bits: usize
) -> Result<(), SynthesisError> {
    let _decomposition = constraint_num_bits_ext(cs, var, num_bits)?;
    Ok(())
}


pub fn allocate_gate_with_linear_only_terms<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, vars: &[Variable], coefs: &[E::Fr], d_next_coef: &E::Fr
) -> Result<(), SynthesisError> {
    let dummy = CS::get_dummy_variable();
    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let next_row_term_idx = CS::MainGate::range_of_next_step_linear_terms().last().unwrap();
    
    let gate_term = MainGateTerm::new();
    let (_, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
    for (i, idx) in range_of_linear_terms.enumerate() {
        local_coeffs[idx] = coefs[i].clone();
    } 
    local_coeffs[next_row_term_idx] = d_next_coef.clone();

    let mg = CS::MainGate::default();
    let local_vars = Vec::from_iterator(vars.iter());
    cs.new_single_gate_for_trace_step(&mg, &local_coeffs, &local_vars, &[])?;
}


// enforce that bitlength(var * shift) <= num_bits using naive approach which is the following:
// we decompose var * shift into single bits [f0, f1, ..., fn], for each f_i we enforce that f_i is actually a bit
// by f_i * (f_i - 1) == 0
// and then construct the long linear combination: var * shift = \sum 2^i * f_i
pub fn enforce_range_check_using_naive_approach<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, shift: E::Fr, num_bits: usize
) -> Result<RangeCheckDecomposition<E>, SynthesisError> {
    increment_invocation_count();
    // count all constraints of the form f * (f - 1) == 0
    increment_total_gates_count(num_bits);
    // we should additionally count gates used in long linear combination:
    // if num_bits <= 3, then there is a single gate: f0 + 2*f1 + 4*f2 = var
    // if 4 <= num_bits <= 6 there will be two gates: f0 + 2*f1 + 4*f2 + 8*f3 = d_next, d_next + 16*f4 + 32*f5 = var
    // if num_bits > 6, then the first gate will be of the form:
    //      f0 + 2*f1 + 4*f2 + 8*f3 = d_next - and hence contain 4 variables
    // the last gate will be of the form: 
    //      d_last + 2^(n-1)*f_(n-1) +2^n * f_n = var and hence containt 2 variables f_i
    // all intermediate gates will be of the form: 
    //      2^i f_i + 2^(i+1) f_(i+1) + 2^(i+2) f_(i+2) + d_cur = d_next and hence containt 3 variables f_i
    // hence the total number of gates in linear combination will be: 2 + x, where x is the smallest integer,
    // such that 3 * x + 6 >= num_bits => x = ceil(num_bits / 3) - 2
    let lc_gates : usize = match num_bits {
        1..=3 => 1,
        4..=6 => 2,
        _ => (num_bits + 2) / 3 - 2, 
    };
    increment_total_gates_count(lc_gates);

    let has_value = var.get_value().is_some();
    let shifted_value = var.get_value().map(|x| {
        let mut tmp = x;
        tmp.mul_assign(&shift);
        tmp
    }).unwrap_or(E::Fr::zero());
    
    let bits : Vec<bool> = BitIterator::new(shifted_value).take(num_bits).collect();
    let allocated_bits : Vec<AllocatedBit> = bits.into_iter().map(|bit| {
        let t = if has_value { Some(bit) } else { None };
        AllocatedBit::alloc(cs, t)
    }).collect::<Result<Vec<_>>>()?;

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    if num_bits <= 3 {
        let mut lc = LinearCombination::zero();
        let mut coef = E::Fr::one();
        for bit in allocated_bits.iter() {
            lc.add_assign_bit_with_coeff(bit, coef.clone());
            coef.double();
        }
        lc.add_assign_variable_with_coeff(var, minus_one)
    }
    else {
        let mut coef = E::Fr::one();
        let first_gate_allocated_bits = allocated_bits.split_off(CS::Params::STATE_WIDTH);
        //let first_gate_vars : Vec<Variable> = first_gate_allocated_bits
    }

    Ok(RangeCheckDecomposition
    {
        chunks_bitlength: 1,
        decomposition: DecompositionType::BitDecomposition(bits),
    })
}


// enforce bitlength(var * shift) <= num_bits via custom gate of the form:
// { d_next - 4a /in [0, 3], a - 4b /in [0, 3], b - 4c /in [0, 3], c - 4d /in [0, 3]
pub fn enforce_range_check_using_custom_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, var: &AllocatedNum<E>, shift: E::Fr, num_bits: usize
) -> Result<RangeCheckDecomposition<E>, SynthesisError>
assert!(num_bits > 0);
    assert!(num_bits & 1 == 0);
    assert_eq!(CS::Params::STATE_WIDTH, 4, "this only works for a state of width 4 for now");
    if let Some(v) = to_constraint.get_value() {
        let t = self::bigint::fe_to_biguint(&v);
        assert!(t.bits() as usize <= num_bits, "value is {} that is {} bits, while expected {} bits", t.to_str_radix(16), t.bits(), num_bits);
    }
    let num_elements = num_bits / 2;
    let mut slices: Vec<Option<E::Fr>> = if let Some(v) = to_constraint.get_value() {
        split_into_bit_constraint_slices(&v, 2, num_elements).into_iter().map(|el| Some(el)).collect()
    } else {
        vec![None; num_elements]
    };

    let last_val = slices.pop().unwrap();
    if let Some(last_val) = last_val {
        if let Some(v) = to_constraint.get_value() {
            assert_eq!(last_val, v);
        }
    }
    
    let mut result = vec![];
    for v in slices.into_iter() {
        let a = AllocatedNum::alloc(
            cs, 
            || {
                Ok(*v.get()?)
            }
        )?;

        result.push(a);
    }

    // last element is actually an element we want to constraint
    result.push(to_constraint.clone());

    let mut num_gates = num_bits / 8;
    if num_gates % 8 != 0 {
        num_gates += 1;
    }

    let mut raw_variables = Vec::with_capacity(result.len() + 1);
    // let zero_var = AllocatedNum::zero(cs).get_variable();
    // raw_variables.push(zero_var);
    raw_variables.push(cs.get_explicit_zero()?);
    // we start at D(x) with 0
    for el in result.iter() {
        raw_variables.push(el.get_variable());
    }

    if raw_variables.len() % 4 != 1 {
        let to_add = (5 - (raw_variables.len() % 4)) % 4;

        let mut four = E::Fr::one();
        four.double();
        four.double();

        let four = Some(four);

        use crate::plonk::circuit::SomeField;

        let mut previous_value = to_constraint.get_value();

        for _ in 0..to_add {
            let new_value = previous_value.mul(&four);
            let padding = cs.alloc(
                || {
                    Ok(*new_value.get()?)
                }
            )?;

            raw_variables.push(padding);

            previous_value = new_value;
        }
    }

    assert_eq!(raw_variables.len() % 4, 1, "variables len = {}", raw_variables.len());

    let mut rows = raw_variables.chunks_exact(4);

    let gate = TwoBitDecompositionRangecheckCustomGate::default();

    for row in &mut rows {
        let mut row = row.to_vec();
        row.reverse();
        cs.new_single_gate_for_trace_step(
            &gate, 
            &[], 
            &row, 
            &[]
        )?;
    }

    let last = rows.remainder();
    assert!(last.len() == 1);

    let last = last[0];

    let dummy = CS::get_dummy_variable();

    // cause we touch D_Next place an empty gate to the next row

    let (mut variables, coeffs) = CS::MainGate::format_term(MainGateTerm::new(), dummy)?;
    *variables.last_mut().unwrap() = last;

    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    RANGE_GATES_COUNTER.fetch_add(num_gates+1, Ordering::SeqCst);

    Ok(result)
}






// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
pub fn enforce_using_single_column_table_for_shifted_variable<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    shift: E::Fr,
    num_bits: usize
) -> Result<(), SynthesisError> {
    // we ensure that var * shift <= N bits
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert_eq!(strategies[0].strategy, RangeConstraintStrategy::SingleTableInvocation);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].linear_terms_used;

    assert_eq!(linear_terms_used, 3);
    assert_eq!(width_per_gate, minimal_per_gate);

    if num_bits <= width_per_gate {
        return enforce_shorter_range_into_single_gate_for_shifted_variable(
            cs,
            to_constraint,
            shift,
            num_bits
        );
    }

    increment_invocation_count();

    // initial_d = 2^k * num_to_constraint;
    // we split this initial_d into chunks of equal_length W: [a0, a1, ..., an]
    // 2^W d_next = d - a_i
    // we do two things simultaneously:
    // - arithmetic constraint like d - a_i + d + 2^W d_next = 0
    // - range constraint that a has width W
    // NB: on the last row the arithmetic constraint would be simply:
    // d - a_n = 0

    let dummy_var = CS::get_dummy_variable();
    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(next_term_range.len(), 1, "for now works only if only one variable is accessible on the next step");
    let next_step_coeff_idx = next_term_range.next().expect("must give at least one index");
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut table_width_shift = E::Fr::one();
    for _ in 0..width_per_gate {
        table_width_shift.double();
    }
    let mut table_width_shift_negated = table_width_shift.clone();
    table_width_shift_negated.negate();
    let table_width_shift_inverse = table_width_shift.inverse().unwrap();

    let mut num_gates_for_coarse_constraint = num_bits / width_per_gate;
    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits != 0 {
        num_gates_for_coarse_constraint += 1;
    }
    let num_slices = num_gates_for_coarse_constraint;

    use crate::plonk::circuit::SomeField;

    let value_to_constraint = to_constraint.get_value().mul(&Some(shift));
    let slices = split_some_into_slices(value_to_constraint, width_per_gate, num_slices);
    let mut it = slices.into_iter().peekable();
    
    let table = cs.get_table(RANGE_CHECK_SINGLE_APPLICATION_TABLE_NAME)?;
    let mut cur_value = to_constraint.clone();
    let mut coeffs = [minus_one, E::Fr::zero(), E::Fr::zero(), shift];

    while let Some(slice_fr) = it.next() {
        let d_next_coef = if it.peek().is_some() {
            table_width_shift_negated
        } else {
            E::Fr::zero()
        };

        let slice = AllocatedNum::alloc(cs, || slice_fr.grab())?;
        let vars = [slice.get_variable(), dummy_var, dummy_var, cur_value.get_variable()];  

        cs.begin_gates_batch_for_step()?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
    
        let gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy_var)?;

        for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
            gate_coefs[idx] = *coef;
        }
        gate_coefs[next_step_coeff_idx] = d_next_coef;

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(
            &mg,
            &gate_coefs,
            &vars,
            &[]
        )?;
        cs.end_gates_batch_for_step()?;

        cur_value = if it.peek().is_some() {
            AllocatedNum::alloc(cs, || {
                let mut res = cur_value.get_value().grab()?;
                res.mul_assign(&coeffs.last().unwrap());
                let tmp = slice.get_value().grab()?;
                res.sub_assign(&tmp);
                res.mul_assign(&table_width_shift_inverse);
                Ok(res)
            })?
        }
        else {
            AllocatedNum::zero(cs)
        };
        *coeffs.last_mut().unwrap() = E::Fr::one();
    }
      
    increment_total_gates_count(num_gates_for_coarse_constraint + (remainder_bits != 0) as usize);
    Ok(())
}


pub fn enforce_range_check_using_bitop_table(cs, var, shift, num_bits)<CS: ConstraintSystem<E>>(
    cs: &mut CS,
    value: Option<BigUint>,
    alloc_full: bool
) -> Result<Self> {     
    let mut slices_u8 = split_some_into_fixed_number_of_limbs(value.clone(), 8, 32);
    let mut slices_u32 = split_some_into_fixed_number_of_limbs(value, 32, 8);
    let mut split_u8 = [UInt8::<E>::zero(); 32];
    let mut split_u32 = [UInt32::<E>::zero(); 8];
    let table = cs.get_table(crate::vm::state::VM_BITWISE_LOGICAL_OPS_TABLE_NAME)?;
    let dummy = CS::get_dummy_variable();

    let shifts = compute_shifts::<E::Fr>();
    let shift_b_start = shifts[8].clone();
    let shift_inc = shifts[16].clone();
    let mut minus_one = E::Fr::one();
    minus_one.negate();
    let shift32 = shifts[32].clone();

    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
    let idx_of_last_linear_term = range_of_next_step_linear_terms.last().expect("must have an index");
    let iter = itertools::multizip(
        (slices_u8.chunks(4), slices_u32.iter(), split_u32.iter_mut(), split_u8.chunks_mut(4))
    );

    for (in_chunks_u8, in_chunk_32, out_chunk_32, out_chunks_u8) in iter {
        let mut shift_a = E::Fr::one();
        let mut shift_b = shift_b_start.clone();
        let full = Num::Variable(AllocatedNum::alloc(cs, || {
            let fe = some_biguint_to_fe::<E::Fr>(in_chunk_32);
            fe.grab()
        })?);
        let mut acc = full.get_variable();
        let mut idx = 0;
        
        for (_is_first, is_final, in_subchunk) in in_chunks_u8.chunks(2).identify_first_last() {
            let a = Num::Variable(AllocatedNum::alloc(cs, || {
                let fe = some_biguint_to_fe::<E::Fr>(&in_subchunk[0]);
                fe.grab()
            })?);
            let b = Num::Variable(AllocatedNum::alloc(cs, || {
                let fe = some_biguint_to_fe::<E::Fr>(&in_subchunk[1]);
                fe.grab()
            })?);

            out_chunks_u8[idx] = UInt8::from_num_unchecked(a.clone());
            out_chunks_u8[idx+1] = UInt8::from_num_unchecked(b.clone());
            idx += 2;
            
            let a_xor_b = match (a.get_value(), b.get_value()) {
                (Some(a_val), Some(b_val)) => {
                    let res = table.query(&[a_val, b_val])?;
                    AllocatedNum::alloc(cs, || Ok(res[0]))?
                },  
                (_, _) => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
            };
    
            let new_acc = if !is_final {
                AllocatedNum::alloc(cs, || {
                    let mut res = acc.get_value().grab()?;               
                    let mut tmp = a.get_value().grab()?;
                    tmp.mul_assign(&shift_a);
                    res.sub_assign(&tmp);
                    tmp = b.get_value().grab()?;
                    tmp.mul_assign(&shift_b);
                    res.sub_assign(&tmp);
                    Ok(res)
                })?
            }
            else {
                AllocatedNum::zero(cs)
            };

            // new_acc = prev_acc - a * shift_a - b * shift_b
            // or: a * shift_a + b * shift_b + new_acc - prev_acc = 0;
            let vars = [
                a.get_variable().get_variable(), b.get_variable().get_variable(), 
                a_xor_b.get_variable(), acc.get_variable()
            ];
            let coeffs = [shift_a.clone(), shift_b, E::Fr::zero(), minus_one];
    
            cs.begin_gates_batch_for_step()?;
            cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        
            let gate_term = MainGateTerm::new();
            let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
    
            for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
                gate_coefs[idx] = *coef;
            }
            if !is_final {
                gate_coefs[idx_of_last_linear_term] = E::Fr::one();
            }
    
            let mg = CS::MainGate::default();
            cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
            cs.end_gates_batch_for_step()?;
    
            acc = new_acc;
            shift_a.mul_assign(&shift_inc);
            shift_b.mul_assign(&shift_inc);
        }
        *out_chunk_32 = UInt32::from_num_unchecked(full);
    }

    let full = if alloc_full {
        let mut full = UInt256::zero();
        for (in_chunks_u32, out_chunks_u64) in split_u32.chunks(2).zip(full.inner.iter_mut()) {
            let mut lc = LinearCombination::zero();
            lc.add_assign_number_with_coeff(&in_chunks_u32[0].inner, E::Fr::one());
            lc.add_assign_number_with_coeff(&in_chunks_u32[1].inner, shift32.clone());
            let res = lc.into_num(cs)?;
            *out_chunks_u64 = UInt64::from_num_unchecked(res);
        }
        Some(full)
    }
    else {
        None
    };

    Ok(MemoryInput {
        full,
        split_u8,
        split_u32
    })
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn check_two_bit_gate() {
        use crate::bellman::pairing::bn256::{Bn256, Fr};
        use crate::bellman::plonk::better_better_cs::cs::*;
        use crate::plonk::circuit::bigint::*;
        use crate::plonk::circuit::linear_combination::*;
        use crate::plonk::circuit::allocated_num::*;

        struct Tester;

        impl Circuit<Bn256> for Tester {
            type MainGate = Width4MainGateWithDNext;

            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<Bn256>>>, SynthesisError> {
                Ok(
                    vec![
                        Self::MainGate::default().into_internal(),
                        TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
                    ]
                )
            }
            fn synthesize<CS: ConstraintSystem<Bn256>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let variables: Vec<_> = (0..5).map(|_| AllocatedNum::alloc(
                    cs, 
                    || {
                        Ok(Fr::one())
                    }
                ).unwrap()).collect();
        
                let mut lc = LinearCombination::<Bn256>::zero();
                lc.add_assign_constant(Fr::one());
                let mut current = Fr::one();
                for v in variables.iter() {
                    lc.add_assign_variable_with_coeff(v, current);
                    current.double();
                }
        
                let _result = lc.into_allocated_num(cs).unwrap();
            
                let num = AllocatedNum::alloc(
                    cs,
                    || {
                        Ok(Fr::from_str("40000").unwrap())
                    }
                ).unwrap();
        
                let _ = create_range_constraint_chain(cs, &num, 18)?;

                Ok(())
            }
        }

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = Tester;
        circuit.synthesize(&mut assembly).unwrap();
        assert!(assembly.is_satisfied());

        let gate = assembly.sorted_gates[1].box_clone();
        dbg!(assembly.aux_gate_density.0.get(&gate));

        assembly.finalize();

        use crate::bellman::worker::Worker;

        let worker = Worker::new();

        let setup = assembly.create_setup::<Tester>(&worker).unwrap();

        use crate::bellman::kate_commitment::*;
        use crate::bellman::plonk::commitments::transcript::{*, keccak_transcript::RollingKeccakTranscript};

        let crs_mons =
            Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.gate_selectors_monomials[0].size(), &worker);

        let _proof = assembly.create_proof::<_, RollingKeccakTranscript<Fr>>(
            &worker, 
            &setup, 
            &crs_mons,
            None
        ).unwrap();
    }
}
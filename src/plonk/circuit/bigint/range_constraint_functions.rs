use crate::bellman::pairing::{
    Engine,
};

use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator
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
    PlonkCsWidth4WithNextStepParams,
    TrivialAssembly
};

use crate::circuit::Assignment;
use super::*;
use super::bigint::*;

use crate::plonk::circuit::allocated_num::{AllocatedNum, Num};
use crate::plonk::circuit::simple_term::{Term};

// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
pub fn coarsely_enforce_using_multitable<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::MultiTable);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].multiples_per_gate;

    assert_eq!(linear_terms_used, 3);

    if num_bits <= width_per_gate {
        return coarsely_enforce_using_multitable_into_single_gate(
            cs,
            to_constraint,
            num_bits
        );
    }

    // we do two things simultaneously:
    // - arithmetic constraint a + 2^k * b + 2^2k * c + d - d_next = 0
    // - range constraint that a, b, c have width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
    assert_eq!(next_term_range.len(), 1, "for now works only if only one variable is accessible on the next step");
    let next_step_coeff_idx = next_term_range.next().expect("must give at least one index");

    let mut minus_one = E::Fr::one();
    minus_one.negate();

    let mut shift = E::Fr::one();
    for _ in 0..minimal_per_gate {
        shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    let num_full_gates = num_bits / width_per_gate;
    let mut num_terms_in_partial_gate = 0;
    let remainder_bits = num_bits % width_per_gate;
    if remainder_bits != 0 {
        num_terms_in_partial_gate = remainder_bits / minimal_per_gate;
        if remainder_bits % minimal_per_gate != 0 {
            num_terms_in_partial_gate += 1;
        }
    }

    let num_slices = num_full_gates * linear_terms_used + num_terms_in_partial_gate;

    let slices = split_some_into_slices(to_constraint.get_value(), minimal_per_gate, num_slices);

    let mut it = slices.into_iter();

    use crate::circuit::SomeField;

    let mut next_step_variable_from_previous_gate: Option<AllocatedNum<E>> = None;
    let mut next_step_value = None;

    let table = cs.get_multitable(RANGE_CHECK_MULTIAPPLICATION_TABLE_NAME)?;

    use std::sync::Arc;

    for full_gate_idx in 0..num_full_gates {
        if next_step_value.is_none() {
            next_step_value = Some(E::Fr::zero());
        }

        let mut term = MainGateTerm::<E>::new();
        for _ in 0..3 {
            let value = (&mut it).next().unwrap();
            let allocated = AllocatedNum::alloc(cs, || {
                Ok(*value.get()?)
            })?;

            let scaled = value.mul(&Some(current_term_coeff));
            next_step_value = next_step_value.add(&scaled);

            term.add_assign(ArithmeticTerm::from_variable_and_coeff(allocated.get_variable(), current_term_coeff));

            current_term_coeff.mul_assign(&shift);
        }

        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
        } else {
            term.add_assign(ArithmeticTerm::from_variable(explicit_zero_var));
        }

        let (variables, mut coeffs) = CS::MainGate::format_term(term, dummy_var)?;

        coeffs[next_step_coeff_idx] = minus_one;

        let is_last_gate = (full_gate_idx == num_full_gates - 1) && num_terms_in_partial_gate == 0;

        if is_last_gate == false {
            let next_var = AllocatedNum::alloc(cs, || {
                Ok(*next_step_value.get()?)
            })?;
            next_step_variable_from_previous_gate = Some(next_var);
        } else {
            next_step_variable_from_previous_gate = Some(to_constraint.clone());
        }

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(
            &CS::MainGate::default(), 
            &coeffs, 
            &variables, 
            &[]
        )?;

        cs.apply_multi_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    // make at most one gate where not all the inputs are usefull
    if num_terms_in_partial_gate != 0 {
        let mut term = MainGateTerm::<E>::new();
        for value in it {
            let allocated = AllocatedNum::alloc(cs, || {
                Ok(*value.get()?)
            })?;

            let scaled = value.mul(&Some(current_term_coeff));
            next_step_value = next_step_value.add(&scaled);

            term.add_assign(ArithmeticTerm::from_variable_and_coeff(allocated.get_variable(), current_term_coeff));

            current_term_coeff.mul_assign(&shift);
        }

        for _ in num_terms_in_partial_gate..linear_terms_used {
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
        }

        if let Some(from_previous) = next_step_variable_from_previous_gate.take() {
            term.add_assign(ArithmeticTerm::from_variable(from_previous.get_variable()));
        } else {
            term.add_assign(ArithmeticTerm::from_variable(explicit_zero_var));
        }

        let (variables, mut coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;
        coeffs[next_step_coeff_idx] = minus_one;
        
        next_step_variable_from_previous_gate = Some(to_constraint.clone());

        cs.begin_gates_batch_for_step()?;

        cs.new_gate_in_batch(
            &CS::MainGate::default(), 
            &coeffs, 
            &variables, 
            &[]
        )?;

        cs.apply_multi_lookup_gate(&variables[0..linear_terms_used], Arc::clone(&table))?;

        cs.end_gates_batch_for_step()?;
    }

    let final_val = next_step_variable_from_previous_gate.unwrap();

    let (mut vars, coeffs) = CS::MainGate::format_term(MainGateTerm::<E>::new(), dummy_var)?;

    *vars.last_mut().unwrap() = final_val.get_variable();

    cs.new_single_gate_for_trace_step(
        &CS::MainGate::default(), 
        &coeffs, 
        &vars,
        &[]
    )?;
    
    Ok(())
}


// enforces that this value is either `num_bits` long or a little longer 
// up to a single range constraint width from the table
pub fn coarsely_enforce_using_multitable_into_single_gate<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS, 
    to_constraint: &AllocatedNum<E>, 
    num_bits: usize
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::MultiTable);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].multiples_per_gate;

    assert_eq!(linear_terms_used, 3);
    assert!(num_bits <= width_per_gate);

    // we do two things simultaneously:
    // - arithmetic constraint a + 2^k * b + 2^2k * c - d = 0
    // - range constraint that a, b, c have width W

    let explicit_zero_var = cs.get_explicit_zero()?;
    let dummy_var = CS::get_dummy_variable();

    let mut shift = E::Fr::one();
    for _ in 0..minimal_per_gate {
        shift.double();
    }

    let mut current_term_coeff = E::Fr::one();

    use super::bigint::make_multiple;

    let num_terms = make_multiple(num_bits, minimal_per_gate) / minimal_per_gate;

    assert!(num_terms <= linear_terms_used);

    let slices = split_some_into_slices(to_constraint.get_value(), minimal_per_gate, num_terms);
    assert_eq!(slices.len(), num_terms);

    use crate::circuit::SomeField;

    let mut term = MainGateTerm::<E>::new();
    for value in slices.into_iter() {
        let allocated = AllocatedNum::alloc(cs, || {
            Ok(*value.get()?)
        })?;

        let scaled = value.mul(&Some(current_term_coeff));

        term.add_assign(ArithmeticTerm::from_variable_and_coeff(allocated.get_variable(), current_term_coeff));

        current_term_coeff.mul_assign(&shift);
    }

    for _ in num_terms..linear_terms_used {
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(explicit_zero_var, E::Fr::zero()));
    }

    term.sub_assign(ArithmeticTerm::from_variable(to_constraint.get_variable()));

    let (variables, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy_var)?;

    cs.begin_gates_batch_for_step()?;

    cs.new_gate_in_batch(
        &CS::MainGate::default(), 
        &coeffs, 
        &variables, 
        &[]
    )?;

    let table = cs.get_multitable(RANGE_CHECK_MULTIAPPLICATION_TABLE_NAME)?;

    cs.apply_multi_lookup_gate(&variables[0..linear_terms_used], table)?;

    cs.end_gates_batch_for_step()?;
    
    Ok(())
}

pub fn adaptively_coarsely_constraint_multiple<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    terms: &[Term<E>],
    widths: &[usize]
) -> Result<(), SynthesisError> {
    let strategies = get_range_constraint_info(&*cs);
    assert_eq!(CS::Params::STATE_WIDTH, 4);
    assert!(strategies.len() > 0);
    assert!(strategies[0].strategy == RangeConstraintStrategy::MultiTable);

    let width_per_gate = strategies[0].optimal_multiple;
    let minimal_per_gate = strategies[0].minimal_multiple;
    let linear_terms_used = strategies[0].multiples_per_gate;

    assert_eq!(linear_terms_used, 3);

    // first let's go over constants
    // and short constraints

    assert_eq!(terms.len(), widths.len());

    let mut remaining = Vec::with_capacity(terms.len());
    let mut short_constraints = Vec::with_capacity(terms.len());

    for (t, &w) in terms.iter().zip(widths.iter()) {
        if t.is_constant() {
            let value = t.get_constant_value();
            let value = fe_to_biguint(&value);
            assert!(value.bits() as usize <= w);
        } else {
            if w <= minimal_per_gate {
                let collapsed = t.collapse_into_num(cs)?;
                short_constraints.push(collapsed.get_variable().get_variable());
            } else {
                remaining.push((t.clone(), w));
            }
        }
    }

    // first let's do the simple part: make simple constraints for values that are short.
    // For this we just span a table over individual elements

    let table = cs.get_multitable(RANGE_CHECK_MULTIAPPLICATION_TABLE_NAME)?;

    use std::sync::Arc;

    {
        let mut it = short_constraints.chunks_exact(linear_terms_used);

        for chunk in &mut it {
            cs.begin_gates_batch_for_step()?;

            cs.apply_multi_lookup_gate(chunk, Arc::clone(&table))?;

            cs.end_gates_batch_for_step()?;
        }

        let remainder = it.remainder();
        let remainder_len = remainder.len();
        if remainder_len != 0 {
            let explicit_zero_var = cs.get_explicit_zero()?;

            let mut variables = vec![explicit_zero_var; linear_terms_used];

            for (idx, el) in remainder.iter().enumerate() {
                variables[idx] = *el;
            }

            cs.begin_gates_batch_for_step()?;

            cs.apply_multi_lookup_gate(&variables, Arc::clone(&table))?;

            cs.end_gates_batch_for_step()?;
        }
    }

    // now let's think what to do with terms that do not fit into smallest granularity

    // for now let's just try to coarsely constraint them and expect that is most of the cases it would
    // be an optimal way

    for (term, width) in remaining.into_iter() {
        let r = term.collapse_into_num(cs)?.get_variable();
        coarsely_enforce_using_multitable(cs, &r, width)?;
    }

    Ok(())
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::plonk::circuit::*;
    use crate::bellman::plonk::better_better_cs::lookup_tables::*;
    use crate::bellman::plonk::better_better_cs::cs::*;

    #[test]
    fn make_ideal_case_range_constraint() {
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;

        let mut cs = TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<E>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let value = Fr::from_str(&"123456").unwrap();
        let num = AllocatedNum::alloc(
            &mut cs,
            || {
                Ok(value)
            }
        ).unwrap();

        coarsely_enforce_using_multitable(
            &mut cs,
            &num,
            48
        ).unwrap();

        assert!(cs.n() == 2);

        assert!(cs.is_satisfied());
    }

    #[test]
    fn make_coarse_case_range_constraint() {
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;

        let mut cs = TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<E>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let value = Fr::from_str(&"123456").unwrap();
        let num = AllocatedNum::alloc(
            &mut cs,
            || {
                Ok(value)
            }
        ).unwrap();

        coarsely_enforce_using_multitable(
            &mut cs,
            &num,
            60
        ).unwrap();

        assert!(cs.n() == 3);

        assert!(cs.is_satisfied());
    }


    #[test]
    fn make_coarse_short_range_constraint() {
        type E = crate::bellman::pairing::bn256::Bn256;
        type Fr = crate::bellman::pairing::bn256::Fr;

        let mut cs = TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let over = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
        let table = MultiTableApplication::<E>::new_range_table_of_width_3(16, over).unwrap();

        cs.add_multitable(table).unwrap();

        let value = Fr::from_str(&"123456").unwrap();
        let num = AllocatedNum::alloc(
            &mut cs,
            || {
                Ok(value)
            }
        ).unwrap();

        coarsely_enforce_using_multitable(
            &mut cs,
            &num,
            20
        ).unwrap();

        assert!(cs.n() == 1);

        assert!(cs.is_satisfied());
    }
}
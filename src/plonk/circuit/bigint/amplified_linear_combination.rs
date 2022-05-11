use super::*;
use crate::bellman::plonk::better_better_cs::cs::{Variable, ConstraintSystem, ArithmeticTerm, MainGateTerm};
use super::super::simple_term::Term;
use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
use std::collections::HashMap;

// module containing amplified version of linear combination that supports both linear and multiplicative terms
pub struct AmplifiedLinearCombination<E: Engine> {
    value: Option<E::Fr>,
    linear_terms: Vec<(E::Fr, Variable)>,
    quadratic_terms: Vec<(E::Fr, Variable, Variable)>,
    constant: E::Fr
}

impl<E: Engine> std::fmt::Debug for AmplifiedLinearCombination<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AmplifiedLinearCombination")
            .field("value", &self.value)
            .field("number of terms", &(self.linear_terms.len() + self.quadratic_terms.len()))
            .field("linear_terms", &self.linear_terms)
            .field("quadratic_terms", &self.quadratic_terms)
            .field("constant", &self.constant)
            .finish()
    }
}

impl<E: Engine> From<AllocatedNum<E>> for AmplifiedLinearCombination<E> {
    fn from(num: AllocatedNum<E>) -> AmplifiedLinearCombination<E> {
        Self {
            value: num.value,
            linear_terms: vec![(E::Fr::one(), num.variable)],
            quadratic_terms: vec![],
            constant: E::Fr::zero()
        }
    }
}

impl<E: Engine> From<Num<E>> for AmplifiedLinearCombination<E> {
    fn from(num: Num<E>) -> AmplifiedLinearCombination<E> {
        match num {
            Num::Variable(allocated) => {
                Self::from(allocated)
            },
            Num::Constant(constant) => {
                Self {
                    value: Some(constant),
                    linear_terms: vec![],
                    quadratic_terms: vec![],
                    constant: constant
                }
            }
        }
    }
}

impl<E: Engine> Clone for AmplifiedLinearCombination<E> {
    fn clone(&self) -> Self {
        Self {
            value: self.value,
            linear_terms: self.linear_terms.clone(),
            quadratic_terms: self.quadratic_terms.clone(),
            constant: self.constant,
        }
    }
}

impl<E: Engine> AmplifiedLinearCombination<E> {
    pub fn zero() -> Self {
        Self {
            value: Some(E::Fr::zero()),
            linear_terms: vec![],
            quadratic_terms: vec![],
            constant: E::Fr::zero(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        self.linear_terms.len() + self.quadratic_terms.len()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn scale(&mut self, coeff: &E::Fr) {
        if coeff.is_zero() {
            self.linear_terms.truncate(0);
            self.quadratic_terms.truncate(0);
            self.constant = E::Fr::zero();
            self.value = Some(E::Fr::zero());
            return;
        }

        if let Some(ref mut val) = self.value.as_mut() {
            val.mul_assign(&coeff);
        }

        for (c, _) in self.linear_terms.iter_mut() {
            c.mul_assign(&coeff);
        }

        for (c, _, _) in self.quadratic_terms.iter_mut() {
            c.mul_assign(&coeff);
        }

        self.constant.mul_assign(&coeff);
    }

    pub fn add_assign_number_with_coeff(&mut self, number: &Num<E>, coeff: E::Fr) {
        match number {
            Num::Variable(ref allocated_number) => {
                self.add_assign_variable_with_coeff(allocated_number, coeff);
            },
            Num::Constant(constant) => {
                let mut res = coeff;
                res.mul_assign(&constant);
                self.add_assign_constant(res);
            } 
        }
    }

    pub fn add_assign_variable_with_coeff(&mut self, variable: &AllocatedNum<E>, coeff: E::Fr) {
        if coeff.is_zero() {
            return;
        }

        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            },
            _ => None
        };

        self.value = newval;
        self.linear_terms.push((coeff, variable.variable));
    }

    pub fn add_assign_term(&mut self, term: &Term<E>)
    {
        if term.is_constant() {
            self.add_assign_constant(term.get_constant_value());
            return;
        }

        // otherwise add constant and scaled num separately
        self.add_assign_constant(term.constant_term);
        self.add_assign_number_with_coeff(&term.num, term.coeff);
    }

    pub fn add_assign_term_with_coeff(&mut self, term: &Term<E>, coeff: E::Fr)
    {
        let mut scaled_term = term.clone();
        scaled_term.scale(&coeff);
        self.add_assign_term(&scaled_term)
    }
   
    pub fn add_assign_boolean_with_coeff(&mut self, bit: &Boolean, coeff: E::Fr) {
        if coeff.is_zero() {
            return;
        }

        let new_value = match (self.value, bit.get_value()) {
            (Some(mut val), Some(bit_value)) => {
                if bit_value {
                    val.add_assign(&coeff);
                }
                Some(val)
            },
            _ => None
        };
        self.value = new_value;

        match bit {
            &Boolean::Constant(c) => {
                if c {
                    self.constant.add_assign(&coeff);
                }
            },
            &Boolean::Is(ref v) => {
                self.linear_terms.push((coeff, v.get_variable()));
            },
            &Boolean::Not(ref v) => {
                let mut coeff_negated = coeff;
                coeff_negated.negate();
                self.linear_terms.push((coeff_negated, v.get_variable()));
                self.constant.add_assign(&coeff);
            }
        }
    }

    pub fn add_assign_bit_with_coeff(&mut self, bit: &AllocatedBit,coeff: E::Fr) {
        if coeff.is_zero() {
            return;
        }

        let new_value = match (self.value, bit.get_value()) {
            (Some(mut val), Some(bit_value)) => {
                if bit_value {
                    val.add_assign(&coeff);
                }
                Some(val)
            },
            _ => None
        };

        self.value = new_value;
        self.linear_terms.push((coeff, bit.get_variable()))
    }

    pub fn add_assign_constant(&mut self, coeff: E::Fr){
        if coeff.is_zero() {
            return;
        }

        let newval = match self.value {
            Some(mut curval) => {
                curval.add_assign(&coeff);

                Some(curval)
            },
            None => {
                None
            }
        };

        self.value = newval;
        self.constant.add_assign(&coeff);
    }

    pub fn sub_assign_constant(&mut self, coeff: E::Fr) {
        let mut c = coeff;
        c.negate();
        self.add_assign_constant(c);
    }

    pub fn into_num<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<Num<E>, SynthesisError> {
        if self.len() == 0 {
            return Ok(Num::Constant(self.constant));
        }
        let allocated = self.into_allocated_num(cs)?;

        Ok(Num::Variable(allocated))
    }

    #[track_caller]
    pub fn enforce_zero<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        if let Some(value) = self.get_value() {
            assert!(value.is_zero(), "ALC is not actually zero with value {}", value);
        }
        assert!(CS::Params::CAN_ACCESS_NEXT_TRACE_STEP)
   
        // we assume that terms are deduplicated
        let one_fr = E::Fr::one();
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        // trivial case - single variable
        if self.len() == 0 {
            return Ok(());
        }

        let num_terms = terms.len();

        let mg = CS::MainGate::default();

        // we have two options: 
        // - fit everything into a single gate (in case of number terms in the linear combination
        // smaller than a width of the state)
        // - make a required number of extra variables and chain it

        
        if num_terms <= CS::Params::STATE_WIDTH {
            // we can just make a single gate

            let mut gate_term = MainGateTerm::new();

            for (c, var) in terms.into_iter() {
                let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                gate_term.add_assign(t);
            }

            let t = ArithmeticTerm::constant(constant_term);
            gate_term.add_assign(t);

            cs.allocate_main_gate(gate_term)?;
        } else {
            // we can take:
            // - STATE_WIDTH variables to form the first gate and place their sum into the last wire of the next gate
            // - every time take STATE_WIDTH-1 variables and place their sum + last wire into the next gate last wire

            // we have also made a final variable already, so there is NO difference
            let cycles = ((terms.len() - CS::Params::STATE_WIDTH) + (CS::Params::STATE_WIDTH - 2)) / (CS::Params::STATE_WIDTH - 1); // ceil 
            let mut it = terms.into_iter();

            use crate::bellman::plonk::better_better_cs::cs::{Gate, MainGate};

            let mut next_term_range = CS::MainGate::range_of_next_step_linear_terms();
            assert_eq!(next_term_range.len(), 1, "for now works only if only one variable is accessible on the next step");
            let next_step_coeff_idx = next_term_range.next().expect("must give at least one index");

            // this is a placeholder variable that must go into the 
            // corresponding trace polynomial at the NEXT time step 
            let (mut next_step_var_in_chain, mut next_step_var_in_chain_value) = {
                let chunk: Vec<_> = (&mut it).take(CS::Params::STATE_WIDTH).collect();
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    constant_term
                );

                let some_value = match &may_be_new_intermediate_value {
                    Ok(val) => Some(*val),
                    Err(_) => None
                };

                // we manually allocate the new variable
                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let t = ArithmeticTerm::constant(constant_term);
                gate_term.add_assign(t);

                let dummy = CS::get_dummy_variable();

                let (vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
                coeffs[next_step_coeff_idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                (new_intermediate_var, some_value)
            };

            // run over the rest

            // we can only take one less cause 
            // we've already used one of the variable
            let consume_from_lc = CS::Params::STATE_WIDTH - 1; 
            for _ in 0..(cycles-1) {
                // we need to keep in mind that last term of the linear combination is taken
                // so we have to fill only CS::Params::STATE_WIDTH - 1 and then manually 
                // place the next_step_var_in_chain 
                let chunk: Vec<_> = (&mut it).take(consume_from_lc).collect();
                
                // this is a sum of new terms
                let may_be_new_intermediate_value = Self::evaluate_term_value(
                    &*cs, 
                    &chunk, 
                    E::Fr::zero()
                ).map(|val| {
                    // and 
                    let mut tmp = val;
                    tmp.add_assign(next_step_var_in_chain_value.as_ref().expect("value must be known"));

                    tmp
                });

                let some_value = match &may_be_new_intermediate_value {
                    Ok(val) => Some(*val),
                    Err(_) => None
                };

                // we manually allocate the new variable
                // and also add value of one in a chain
                let new_intermediate_var = cs.alloc(|| {
                    may_be_new_intermediate_value
                })?;

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let t = ArithmeticTerm::from_variable_and_coeff(next_step_var_in_chain, one_fr);
                gate_term.add_assign(t);

                let dummy = CS::get_dummy_variable();

                let (vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;
                coeffs[next_step_coeff_idx] = minus_one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;

                next_step_var_in_chain = new_intermediate_var;
                next_step_var_in_chain_value = some_value;
            }

            // final step - we just make a single gate, last one
            // we also make sure that chained variable only goes into the last term
            {
                let chunk: Vec<_> = (&mut it).collect();
                assert!(chunk.len() <= CS::Params::STATE_WIDTH - 1);

                let mut gate_term = MainGateTerm::<E>::new();

                for (c, var) in chunk.into_iter() {
                    let t = ArithmeticTerm::from_variable_and_coeff(var, c);
                    gate_term.add_assign(t);
                }

                let dummy = CS::get_dummy_variable();

                let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
                let idx_of_last_linear_term = range_of_linear_terms.last().expect("must have an index");

                let (mut vars, mut coeffs) = CS::MainGate::format_term(gate_term, dummy)?;

                *vars.last_mut().unwrap() = next_step_var_in_chain;
                coeffs[idx_of_last_linear_term] = one_fr;

                cs.new_single_gate_for_trace_step(
                    &mg, 
                    &coeffs, 
                    &vars,
                    &[]
                )?;
            }
            assert!(it.next().is_none());
        }

        Ok(())
    }
}

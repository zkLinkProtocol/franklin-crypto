use bellman::pairing::Engine;

use bellman::pairing::ff::{BitIterator, Field, PrimeField};

use super::Assignment;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use circuit::expression::Expression;

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone, Debug)]
pub struct AllocatedBit {
    variable: Variable,
    value: Option<bool>,
}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_value_field<E: Engine>(&self) -> Option<E::Fr> {
        let value = self.get_value();
        match value {
            None => None,
            Some(value) => {
                if value {
                    Some(E::Fr::one())
                } else {
                    Some(E::Fr::zero())
                }
            }
        }
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value. Further, constrain that the boolean is false
    /// unless the condition is false.
    pub fn alloc_conditionally<E, CS>(
        mut cs: CS,
        value: Option<bool>,
        must_be_false: &AllocatedBit,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let var = cs.alloc(
            || "boolean",
            || {
                if *value.get()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain: (1 - must_be_false - a) * a = 0
        // if must_be_false is true, the equation
        // reduces to -a * a = 0, which implies a = 0.
        // if must_be_false is false, the equation
        // reduces to (1 - a) * a = 0, which is a
        // traditional boolean constraint.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - must_be_false.variable - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(AllocatedBit {
            variable: var,
            value: value,
        })
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<E, CS>(mut cs: CS, value: Option<bool>) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let var = cs.alloc(
            || "boolean",
            || {
                if *value.get()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(AllocatedBit {
            variable: var,
            value: value,
        })
    }
    pub fn inputize<E, CS>(&self, mut cs: CS, _witness: &AllocatedBit) -> Result<(), SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let input = cs.alloc_input(
            || "input variable",
            || {
                if self.get_value().grab()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;
        cs.enforce(
            || "enforce input is correct",
            |lc| lc + input,
            |lc| lc + CS::one(),
            |lc| lc + self.get_variable(),
        );
        Ok(())
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<E, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "xor result",
            || {
                if *a.value.get()? ^ *b.value.get()? {
                    result_value = Some(true);

                    Ok(E::Fr::one())
                } else {
                    result_value = Some(false);

                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c
        cs.enforce(
            || "xor constraint",
            |lc| lc + a.variable + a.variable,
            |lc| lc + b.variable,
            |lc| lc + a.variable + b.variable - result_var,
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and<E, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "and result",
            || {
                if *a.value.get()? & *b.value.get()? {
                    result_value = Some(true);

                    Ok(E::Fr::one())
                } else {
                    result_value = Some(false);

                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        cs.enforce(
            || "and constraint",
            |lc| lc + a.variable,
            |lc| lc + b.variable,
            |lc| lc + result_var,
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<E, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "and not result",
            || {
                if *a.value.get()? & !*b.value.get()? {
                    result_value = Some(true);

                    Ok(E::Fr::one())
                } else {
                    result_value = Some(false);

                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        cs.enforce(
            || "and not constraint",
            |lc| lc + a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var,
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value,
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<E, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let mut result_value = None;

        let result_var = cs.alloc(
            || "nor result",
            || {
                if !*a.value.get()? & !*b.value.get()? {
                    result_value = Some(true);

                    Ok(E::Fr::one())
                } else {
                    result_value = Some(false);

                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        cs.enforce(
            || "nor constraint",
            |lc| lc + CS::one() - a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var,
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value,
        })
    }
}

pub fn u64_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    value: Option<u64>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let values = match value {
        Some(ref value) => {
            let mut tmp = Vec::with_capacity(64);

            for i in 0..64 {
                tmp.push(Some(*value >> i & 1 == 1));
            }

            tmp
        }
        None => {
            vec![None; 64]
        }
    };

    let bits = values
        .into_iter()
        .enumerate()
        .map(|(i, b)| {
            Ok(Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                b,
            )?))
        })
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

pub fn u128_into_constant_boolean_vec_le(value: u128, length: usize) -> Vec<Boolean> {
    assert!(value < 2u128.pow(length as u32));
    let mut values = Vec::with_capacity(length);
    for i in 0..length {
        values.push(value >> i & 1 == 1);
    }

    let bits = values
        .into_iter()
        .map(Boolean::constant)
        .collect::<Vec<_>>();

    bits
}

pub fn u128_into_constant_boolean_vec_be(value: u128, length: usize) -> Vec<Boolean> {
    let mut boolean_vec = u128_into_constant_boolean_vec_le(value, length);
    boolean_vec.reverse();
    boolean_vec
}

// changes an order of the bits to transform bits in LSB first order into
// LE bytes. Takes 8 bit chunks and reverses them
pub fn le_bits_into_le_bytes(bits: Vec<Boolean>) -> Vec<Boolean> {
    assert_eq!(bits.len() % 8, 0);

    let mut result = vec![];
    for chunk in bits.chunks(8) {
        for b in chunk.iter().rev() {
            result.push(b.clone());
        }
    }

    result
}

pub fn field_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: CS,
    value: Option<F>,
) -> Result<Vec<Boolean>, SynthesisError> {
    let v = field_into_allocated_bits_le::<E, CS, F>(cs, value)?;

    Ok(v.into_iter().map(|e| Boolean::from(e)).collect())
}

pub fn field_into_allocated_bits_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    mut cs: CS,
    value: Option<F>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let mut field_char = BitIterator::new(F::char());

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in BitIterator::new(value.into_repr()) {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        }
        None => {
            vec![None; F::NUM_BITS as usize]
        }
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

pub fn field_into_allocated_bits_le_fixed<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    mut cs: CS,
    value: Option<F>,
    bit_length: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    assert!(bit_length <= F::NUM_BITS as usize);
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let mut field_char = BitIterator::new(F::char());

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in BitIterator::new(value.into_repr()) {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        }
        None => vec![None; F::NUM_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .enumerate()
        .take(bit_length)
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone, Debug)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(AllocatedBit),
    /// Negated view of the boolean variable
    Not(AllocatedBit),
    /// Constant (not an allocated variable)
    Constant(bool),
}

impl AsRef<Boolean> for Boolean {
    fn as_ref(&self) -> &Boolean {
        self
    }
}

impl Boolean {
    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false,
        }
    }

    pub fn get_variable(&self) -> Option<&AllocatedBit> {
        match *self {
            Boolean::Is(ref v) => Some(v),
            Boolean::Not(ref v) => Some(v),
            Boolean::Constant(_) => None,
        }
    }

    pub fn enforce_equal<E, CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            }
            (&Boolean::Constant(true), a) | (a, &Boolean::Constant(true)) => {
                cs.enforce(
                    || "enforce equal to one",
                    |lc| lc,
                    |lc| lc,
                    |lc| lc + CS::one() - &a.lc(CS::one(), E::Fr::one()),
                );

                Ok(())
            }
            (&Boolean::Constant(false), a) | (a, &Boolean::Constant(false)) => {
                cs.enforce(
                    || "enforce equal to zero",
                    |lc| lc,
                    |lc| lc,
                    |_| a.lc(CS::one(), E::Fr::one()),
                );

                Ok(())
            }
            (a, b) => {
                cs.enforce(
                    || "enforce equal",
                    |lc| lc,
                    |lc| lc,
                    |_| a.lc(CS::one(), E::Fr::one()) - &b.lc(CS::one(), E::Fr::one()),
                );

                Ok(())
            }
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        match self {
            &Boolean::Constant(c) => Some(c),
            &Boolean::Is(ref v) => v.get_value(),
            &Boolean::Not(ref v) => v.get_value().map(|b| !b),
        }
    }

    pub fn get_value_field<E: Engine>(&self) -> Option<E::Fr> {
        let value = self.get_value();
        match value {
            None => None,
            Some(value) => {
                if value {
                    Some(E::Fr::one())
                } else {
                    Some(E::Fr::zero())
                }
            }
        }
    }

    pub fn lc<E: Engine>(&self, one: Variable, coeff: E::Fr) -> LinearCombination<E> {
        match self {
            &Boolean::Constant(c) => {
                if c {
                    LinearCombination::<E>::zero() + (coeff, one)
                } else {
                    LinearCombination::<E>::zero()
                }
            }
            &Boolean::Is(ref v) => LinearCombination::<E>::zero() + (coeff, v.get_variable()),
            &Boolean::Not(ref v) => {
                LinearCombination::<E>::zero() + (coeff, one) - (coeff, v.get_variable())
            }
        }
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// if condition is true, return x, or return y.
    pub fn conditionally_select<E: Engine, CS: ConstraintSystem<E>>(
        mut cs: CS,
        x: &Boolean,
        y: &Boolean,
        condition: &Boolean
    ) -> Result<Self, SynthesisError> {
        match condition {
            Boolean::Constant(true) => Ok(x.clone()),
            Boolean::Constant(false) => Ok(y.clone()),
            cond @ Boolean::Not(_) => Self::conditionally_select(cs.namespace(||"not condition"),  y, x, &cond.not()),
            cond @ Boolean::Is(_) => match (x, y) {
                (x, &Boolean::Constant(false)) => Boolean::and(
                    cs.namespace(||"x and cond"),
                    cond,
                    x
                ),
                (&Boolean::Constant(false), x) => Boolean::and(
                    cs.namespace(||"x and !cond"),
                    &cond.not(),
                    x
                ),
                (&Boolean::Constant(true), x) => Ok(Boolean::and(
                    cs.namespace(||"x or cond"),
                    &cond.not(),
                    &x.not()
                )?.not()),
                (x, &Boolean::Constant(true)) => Ok(Boolean::and(
                    cs.namespace(||"x or cond"),
                    &cond,
                    &x.not()
                )?.not()),
                (a, b) => {
                    let result  = Boolean::from(AllocatedBit::alloc(
                    cs.namespace(||"condition"),
                    {
                        if let (Some(a), Some(b), Some(cond)) = (a.get_value(), b.get_value(), cond.get_value()) {
                            Some(if cond { a } else { b })
                        } else {
                            None
                        }
                    })?);
                    // a = self; b = other; c = cond;
                    //
                    // r = c * a + (1  - c) * b
                    // r = b + c * (a - b)
                    // c * (a - b) = r - b
                    //
                    // If a, b, cond are all boolean, so is r.
                    //
                    // self | other | cond | result
                    // -----|-------|----------------
                    //   0  |   0   |   1  |    0
                    //   0  |   1   |   1  |    0
                    //   1  |   0   |   1  |    1
                    //   1  |   1   |   1  |    1
                    //   0  |   0   |   0  |    0
                    //   0  |   1   |   0  |    1
                    //   1  |   0   |   0  |    0
                    //   1  |   1   |   0  |    1
                    cs.enforce(
                        || "condition select",
                        |_lc| cond.lc(CS::one(), E::Fr::one()),
                        |_lc| a.lc(CS::one(), E::Fr::one()) - &b.lc(CS::one(), E::Fr::one()),
                        |_lc| result.lc(CS::one(), E::Fr::one()) - &b.lc(CS::one(), E::Fr::one()),
                    );

                    Ok(result)
                }
            }
        }
    }

    pub fn conditional_enforce_equal<E: Engine, CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        use self::Boolean::*;
        let one = CS::one();
        let difference = match (self, other) {
            // 1 == 1; 0 == 0
            (Constant(true), Constant(true)) | (Constant(false), Constant(false)) => return Ok(()),
            // false != true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
            // 1 - a
            (Constant(true), Is(a)) | (Is(a), Constant(true)) => LinearCombination::zero() + one - a.get_variable(),
            // a - 0 = a
            (Constant(false), Is(a)) | (Is(a), Constant(false)) => LinearCombination::zero() + a.get_variable(),
            // 1 - !a = 1 - (1 - a) = a
            (Constant(true), Not(a)) | (Not(a), Constant(true)) => LinearCombination::zero() + a.get_variable(),
            // !a - 0 = !a = 1 - a
            (Constant(false), Not(a)) | (Not(a), Constant(false)) => LinearCombination::zero() + one - a.get_variable(),
            // b - a,
            (Is(a), Is(b)) => LinearCombination::zero() + b.get_variable() - a.get_variable(),
            // !b - a = (1 - b) - a
            (Is(a), Not(b)) | (Not(b), Is(a)) => LinearCombination::zero() + one - b.get_variable() - a.get_variable(),
            // !b - !a = (1 - b) - (1 - a) = a - b,
            (Not(a), Not(b)) => LinearCombination::zero() + a.get_variable() - b.get_variable(),
        };

        if !matches!(should_enforce, Constant(false)) {
            cs.enforce(
                || "conditionally enforce equal",
                |lc| lc + &difference,
                |_| should_enforce.lc(one, E::Fr::one()),
                |lc| lc
            );
        }
        Ok(())
    }

    pub fn conditional_enforce_not_equal<E: Engine, CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        if matches!(should_enforce, Constant(false)) { return Ok(()) }

        use self::Boolean::*;
        let one = CS::one();
        let difference = match (self, other) {
            // 1 != 0; 0 != 1
            (Constant(true), Constant(false)) | (Constant(false), Constant(true)) => return Ok(()),
            // false == false and true == true
            (Constant(_), Constant(_)) => return Err(SynthesisError::AssignmentMissing),
            // 1 - a
            (Constant(true), Is(a)) | (Is(a), Constant(true)) => LinearCombination::zero() + one - a.get_variable(),
            // a - 0 = a
            (Constant(false), Is(a)) | (Is(a), Constant(false)) => LinearCombination::zero() + a.get_variable(),
            // 1 - !a = 1 - (1 - a) = a
            (Constant(true), Not(a)) | (Not(a), Constant(true)) => LinearCombination::zero() + a.get_variable(),
            // !a - 0 = !a = 1 - a
            (Constant(false), Not(a)) | (Not(a), Constant(false)) => LinearCombination::zero() + one - a.get_variable(),
            // b - a,
            (Is(a), Is(b)) => {
                let multiplier = cs.alloc(
                    || "conditional select result",
                    || if *should_enforce.get_value().get()? {
                        let mut diff = if *b.get_value().get()? { E::Fr::one() } else { E::Fr::zero() };
                        let a = if *a.get_value().get()? { E::Fr::one() } else { E::Fr::zero() };
                        diff.sub_assign(&a);
                        Ok(diff.inverse().unwrap_or(E::Fr::zero()))
                    } else {
                        Ok(E::Fr::zero())
                    }
                )?;

                cs.enforce(
                    || "conditionally enforce not equal",
                    |_| LinearCombination::zero() + b.get_variable() - a.get_variable(),
                    |lc| lc + multiplier,
                    |_| should_enforce.lc(one, E::Fr::one()),
                );
                return Ok(())
            },
            // !b - a = (1 - b) - a
            (Is(a), Not(b)) | (Not(b), Is(a)) => {
                let multiplier = cs.alloc(
                    || "conditional select result",
                    || if *should_enforce.get_value().get()? {
                        let mut diff = if *b.get_value().get()? { E::Fr::zero() } else { E::Fr::one() };
                        let a = if *a.get_value().get()? { E::Fr::one() } else { E::Fr::zero() };
                        diff.sub_assign(&a);
                        Ok(diff.inverse().unwrap_or(E::Fr::zero()))
                    } else {
                        Ok(E::Fr::zero())
                    }
                )?;

                cs.enforce(
                    || "conditionally enforce not equal",
                    |_| LinearCombination::zero() + one - b.get_variable() - a.get_variable(),
                    |lc| lc + multiplier,
                    |_| should_enforce.lc(one, E::Fr::one()),
                );
                return Ok(())
            },
            // !b - !a = (1 - b) - (1 - a) = a - b,
            (Not(a), Not(b)) => {
                let multiplier = cs.alloc(
                    || "conditional select result",
                    || if *should_enforce.get_value().get()? {
                        let mut diff = if *a.get_value().get()? { E::Fr::one() } else { E::Fr::zero() };
                        let b = if *b.get_value().get()? { E::Fr::one() } else { E::Fr::zero() };
                        diff.sub_assign(&b);
                        Ok(diff.inverse().unwrap_or(E::Fr::zero()))
                    } else {
                        Ok(E::Fr::zero())
                    }
                )?;

                cs.enforce(
                    || "conditionally enforce not equal",
                    |_| LinearCombination::zero() + a.get_variable() - b.get_variable(),
                    |lc| lc + multiplier,
                    |_| should_enforce.lc(one, E::Fr::one()),
                );
                return Ok(())
            },
        };

        cs.enforce(
            || "conditionally enforce not equal",
            |_| difference,
            |_| should_enforce.lc(one, E::Fr::one()),
            |_| should_enforce.lc(one, E::Fr::one()),
        );
        Ok(())
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match self {
            &Boolean::Constant(c) => Boolean::Constant(!c),
            &Boolean::Is(ref v) => Boolean::Not(v.clone()),
            &Boolean::Not(ref v) => Boolean::Is(v.clone()),
        }
    }

    /// Perform XOR over two boolean operands
    pub fn xor<'a, E, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_))
            | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor(cs, is, &not.not())?.not())
            }
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b))
            | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::xor(cs, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a, E, CS>(cs: CS, a: &'a Self, b: &'a Self) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => {
                Ok(Boolean::Constant(false))
            }
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not))
            | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Is(AllocatedBit::and_not(cs, is, not)?))
            }
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor(cs, a, b)?))
            }
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and(cs, a, b)?))
            }
        }
    }

    /// Computes (a and b) xor ((not a) and c)
    pub fn sha256_ch<'a, E, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let ch_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor ((not a) and c)
                Some((a & b) ^ ((!a) & c))
            }
            _ => None,
        };

        match (a, b, c) {
            (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(ch_value.expect("they're all constants")));
            }
            (&Boolean::Constant(false), _, c) => {
                // If a is false
                // (a and b) xor ((not a) and c)
                // equals
                // (false) xor (c)
                // equals
                // c
                return Ok(c.clone());
            }
            (a, &Boolean::Constant(false), c) => {
                // If b is false
                // (a and b) xor ((not a) and c)
                // equals
                // ((not a) and c)
                return Boolean::and(cs, &a.not(), &c);
            }
            (a, b, &Boolean::Constant(false)) => {
                // If c is false
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b)
                return Boolean::and(cs, &a, &b);
            }
            (a, b, &Boolean::Constant(true)) => {
                // If c is true
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b) xor (not a)
                // equals
                // not (a and (not b))
                return Ok(Boolean::and(cs, &a, &b.not())?.not());
            }
            (a, &Boolean::Constant(true), c) => {
                // If b is true
                // (a and b) xor ((not a) and c)
                // equals
                // a xor ((not a) and c)
                // equals
                // not ((not a) and (not c))
                return Ok(Boolean::and(cs, &a.not(), &c.not())?.not());
            }
            (&Boolean::Constant(true), _, _) => {
                // If a is true
                // (a and b) xor ((not a) and c)
                // equals
                // b xor ((not a) and c)
                // So we just continue!
            }
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {}
        }

        let ch = cs.alloc(
            || "ch",
            || {
                ch_value
                    .get()
                    .map(|v| if *v { E::Fr::one() } else { E::Fr::zero() })
            },
        )?;

        // a(b - c) = ch - c
        cs.enforce(
            || "ch computation",
            |_| b.lc(CS::one(), E::Fr::one()) - &c.lc(CS::one(), E::Fr::one()),
            |_| a.lc(CS::one(), E::Fr::one()),
            |lc| lc + ch - &c.lc(CS::one(), E::Fr::one()),
        );

        Ok(AllocatedBit {
            value: ch_value,
            variable: ch,
        }
        .into())
    }

    /// Computes (a and b) xor (a and c) xor (b and c)
    pub fn sha256_maj<'a, E, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let maj_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor (a and c) xor (b and c)
                Some((a & b) ^ (a & c) ^ (b & c))
            }
            _ => None,
        };

        match (a, b, c) {
            (&Boolean::Constant(_), &Boolean::Constant(_), &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(maj_value.expect("they're all constants")));
            }
            (&Boolean::Constant(false), b, c) => {
                // If a is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b and c)
                return Boolean::and(cs, b, c);
            }
            (a, &Boolean::Constant(false), c) => {
                // If b is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and c)
                return Boolean::and(cs, a, c);
            }
            (a, b, &Boolean::Constant(false)) => {
                // If c is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b)
                return Boolean::and(cs, a, b);
            }
            (a, b, &Boolean::Constant(true)) => {
                // If c is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b) xor (a) xor (b)
                // equals
                // not ((not a) and (not b))
                return Ok(Boolean::and(cs, &a.not(), &b.not())?.not());
            }
            (a, &Boolean::Constant(true), c) => {
                // If b is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a) xor (a and c) xor (c)
                return Ok(Boolean::and(cs, &a.not(), &c.not())?.not());
            }
            (&Boolean::Constant(true), b, c) => {
                // If a is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b) xor (c) xor (b and c)
                return Ok(Boolean::and(cs, &b.not(), &c.not())?.not());
            }
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_))
            | (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_)) => {}
        }

        let maj = cs.alloc(
            || "maj",
            || {
                maj_value
                    .get()
                    .map(|v| if *v { E::Fr::one() } else { E::Fr::zero() })
            },
        )?;

        // ¬(¬a ∧ ¬b) ∧ ¬(¬a ∧ ¬c) ∧ ¬(¬b ∧ ¬c)
        // (1 - ((1 - a) * (1 - b))) * (1 - ((1 - a) * (1 - c))) * (1 - ((1 - b) * (1 - c)))
        // (a + b - ab) * (a + c - ac) * (b + c - bc)
        // -2abc + ab + ac + bc
        // a (-2bc + b + c) + bc
        //
        // (b) * (c) = (bc)
        // (2bc - b - c) * (a) = bc - maj

        let bc = Self::and(cs.namespace(|| "b and c"), b, c)?;

        cs.enforce(
            || "maj computation",
            |_| {
                bc.lc(CS::one(), E::Fr::one()) + &bc.lc(CS::one(), E::Fr::one())
                    - &b.lc(CS::one(), E::Fr::one())
                    - &c.lc(CS::one(), E::Fr::one())
            },
            |_| a.lc(CS::one(), E::Fr::one()),
            |_| bc.lc(CS::one(), E::Fr::one()) - maj,
        );

        Ok(AllocatedBit {
            value: maj_value,
            variable: maj,
        }
        .into())
    }
}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}

#[cfg(test)]
mod test {
    use std::ops::Not;
    use super::{field_into_allocated_bits_le, u64_into_boolean_vec_le, AllocatedBit, Boolean};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{Field, PrimeField};
    use bellman::{ConstraintSystem, SynthesisError};
    use circuit::test::*;

    #[test]
    fn test_allocated_bit() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        AllocatedBit::alloc(&mut cs, Some(true)).unwrap();
        assert!(cs.get("boolean") == Fr::one());
        assert!(cs.is_satisfied());
        cs.set("boolean", Fr::zero());
        assert!(cs.is_satisfied());
        cs.set("boolean", Fr::from_str("2").unwrap());
        assert!(!cs.is_satisfied());
        assert!(cs.which_is_unsatisfied() == Some("boolean constraint"));
    }

    #[test]
    fn test_xor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Bls12>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::xor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val ^ *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("xor result")
                        == if *a_val ^ *b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "xor result",
                    if *a_val ^ *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Bls12>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::and(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & *b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and result")
                        == if *a_val & *b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and result",
                    if *a_val & *b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_and_not() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Bls12>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::and_not(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), *a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("and not result")
                        == if *a_val & !*b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "and not result",
                    if *a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_nor() {
        for a_val in [false, true].iter() {
            for b_val in [false, true].iter() {
                let mut cs = TestConstraintSystem::<Bls12>::new();
                let a = AllocatedBit::alloc(cs.namespace(|| "a"), Some(*a_val)).unwrap();
                let b = AllocatedBit::alloc(cs.namespace(|| "b"), Some(*b_val)).unwrap();
                let c = AllocatedBit::nor(&mut cs, &a, &b).unwrap();
                assert_eq!(c.value.unwrap(), !*a_val & !*b_val);

                assert!(cs.is_satisfied());
                assert!(cs.get("a/boolean") == if *a_val { Field::one() } else { Field::zero() });
                assert!(cs.get("b/boolean") == if *b_val { Field::one() } else { Field::zero() });
                assert!(
                    cs.get("nor result")
                        == if !*a_val & !*b_val {
                            Field::one()
                        } else {
                            Field::zero()
                        }
                );

                // Invert the result and check if the constraint system is still satisfied
                cs.set(
                    "nor result",
                    if !*a_val & !*b_val {
                        Field::zero()
                    } else {
                        Field::one()
                    },
                );
                assert!(!cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_enforce_equal() {
        for a_bool in [false, true].iter().cloned() {
            for b_bool in [false, true].iter().cloned() {
                for a_neg in [false, true].iter().cloned() {
                    for b_neg in [false, true].iter().cloned() {
                        {
                            let mut cs = TestConstraintSystem::<Bls12>::new();

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
                            );
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
                            );

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Bls12>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_bool)).unwrap(),
                            );

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Bls12>::new();

                            let mut a = Boolean::from(
                                AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_bool)).unwrap(),
                            );
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            Boolean::enforce_equal(&mut cs, &a, &b).unwrap();

                            assert_eq!(cs.is_satisfied(), (a_bool ^ a_neg) == (b_bool ^ b_neg));
                        }
                        {
                            let mut cs = TestConstraintSystem::<Bls12>::new();

                            let mut a = Boolean::Constant(a_bool);
                            let mut b = Boolean::Constant(b_bool);

                            if a_neg {
                                a = a.not();
                            }
                            if b_neg {
                                b = b.not();
                            }

                            let result = Boolean::enforce_equal(&mut cs, &a, &b);

                            if (a_bool ^ a_neg) == (b_bool ^ b_neg) {
                                assert!(result.is_ok());
                                assert!(cs.is_satisfied());
                            } else {
                                assert!(result.is_err());
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_negation() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let mut b = Boolean::from(AllocatedBit::alloc(&mut cs, Some(true)).unwrap());

        match b {
            Boolean::Is(_) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Not(_) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Is(_) => {}
            _ => panic!("unexpected value"),
        }

        b = Boolean::constant(true);

        match b {
            Boolean::Constant(true) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Constant(false) => {}
            _ => panic!("unexpected value"),
        }

        b = b.not();

        match b {
            Boolean::Constant(true) => {}
            _ => panic!("unexpected value"),
        }
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    enum OperandType {
        True,
        False,
        AllocatedTrue,
        AllocatedFalse,
        NegatedAllocatedTrue,
        NegatedAllocatedFalse,
    }

    impl OperandType {
        fn is_constant(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => true,
                OperandType::AllocatedTrue => false,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => false,
            }
        }

        fn val(&self) -> bool {
            match *self {
                OperandType::True => true,
                OperandType::False => false,
                OperandType::AllocatedTrue => true,
                OperandType::AllocatedFalse => false,
                OperandType::NegatedAllocatedTrue => false,
                OperandType::NegatedAllocatedFalse => true,
            }
        }
    }

    #[test]
    fn test_boolean_xor() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Bls12>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::xor(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Is(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::False, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Is(_)) => {}
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedTrue, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::NegatedAllocatedFalse, OperandType::False, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Not(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("xor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    _ => panic!("this should never be encountered"),
                }
            }
        }
    }

    #[test]
    fn test_boolean_conditional_select() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for (index1, first_operand) in variants.iter().cloned().enumerate() {
            for (index2, second_operand) in variants.iter().cloned().enumerate() {
                for (index3, condition_operand) in variants.iter().cloned().enumerate() {
                    let mut cs = TestConstraintSystem::<Bls12>::new();

                    let a;
                    let b;
                    let condition;

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.namespace(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                                }
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        condition = dyn_construct(condition_operand, "condition_operand");
                    }

                    println!("condition: {:?}", condition);
                    let c = Boolean::conditionally_select(&mut cs, &a, &b, &condition).unwrap();

                    assert!(cs.is_satisfied());

                    println!("operand: {:?} {:?} {:?} => {:?}", first_operand, second_operand, condition_operand, c.get_value());
                    match c {
                        Boolean::Is(c) => match condition_operand {
                            OperandType::True | OperandType::AllocatedTrue | OperandType::NegatedAllocatedFalse => {
                                assert_eq!(c.get_value(), a.get_value(), "allocated");
                            }
                            OperandType::False | OperandType::AllocatedFalse | OperandType::NegatedAllocatedTrue => {
                                assert_eq!(c.get_value(), b.get_value(), "allocated");
                            }
                        },
                        Boolean::Constant(c) => match condition_operand {
                            OperandType::True | OperandType::AllocatedTrue | OperandType::NegatedAllocatedFalse => {
                                assert_eq!(Some(c), a.get_value(), "constant");
                            }
                            OperandType::False | OperandType::AllocatedFalse | OperandType::NegatedAllocatedTrue => {
                                assert_eq!(Some(c), b.get_value(), "constant");
                            }
                        },
                        Boolean::Not(c) => match condition_operand {
                            OperandType::True | OperandType::AllocatedTrue | OperandType::NegatedAllocatedFalse => {
                                assert_eq!(c.get_value().map(Not::not), a.get_value(), "allocated not");
                            }
                            OperandType::False | OperandType::AllocatedFalse | OperandType::NegatedAllocatedTrue => {
                                assert_eq!(c.get_value().map(Not::not), b.get_value(), "allocated not");
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_conditional_enforce() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for (index1, first_operand) in variants.iter().cloned().enumerate() {
            for (index2, second_operand) in variants.iter().cloned().enumerate() {
                for (index2, should_enforce_operand) in variants.iter().cloned().enumerate() {
                    let mut dyn_construct = |operand, name, mut cs: &mut TestConstraintSystem<Bls12>| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };
                    // test enforce equal
                    let mut cs = TestConstraintSystem::<Bls12>::new();
                    let a = dyn_construct(first_operand, "a", &mut cs);
                    let b = dyn_construct(second_operand, "b", &mut cs);
                    let should_enforce = dyn_construct(should_enforce_operand, "should_enforce", &mut cs);

                    let err = a.conditional_enforce_equal(&mut cs, &b, &should_enforce);

                    println!("Testing: {:?} enforce {:?} == {:?} ", should_enforce_operand, first_operand, second_operand);
                    if first_operand.is_constant()
                        && second_operand.is_constant() && first_operand != second_operand {
                        assert!(matches!(err, Err(SynthesisError::AssignmentMissing)));
                    } else {
                        if should_enforce_operand.val() {
                            assert!(err.is_ok());
                            if dbg!(first_operand.val()) == dbg!(second_operand.val()) {
                                assert!(cs.is_satisfied());
                            } else {
                                assert!(!cs.is_satisfied());
                            }
                        } else {
                            assert!(cs.is_satisfied());
                        }
                    }
                    println!("test enforce equal successfully");

                    // test enforce not equal
                    cs = TestConstraintSystem::<Bls12>::new();
                    let a = dyn_construct(first_operand, "a", &mut cs);
                    let b = dyn_construct(second_operand, "b", &mut cs);
                    let condition = dyn_construct(should_enforce_operand, "condition_operand", &mut cs);

                    let err = a.conditional_enforce_not_equal(&mut cs, &b, &should_enforce);

                    println!("Testing: {:?} enforce {:?} != {:?} ", should_enforce_operand, first_operand, second_operand);
                    if should_enforce_operand.is_constant() && should_enforce_operand.val() == false {
                        println!("test not enforce successfully");
                        continue;
                    }
                    if first_operand.is_constant() && second_operand.is_constant() && first_operand == second_operand {
                        assert!(matches!(err, Err(SynthesisError::AssignmentMissing)));
                        println!("test enforce not equal return AssignmentMissing");
                    } else {
                        if should_enforce_operand.val() {
                            assert!(err.is_ok());
                            if dbg!(first_operand.val()) != dbg!(second_operand.val()){
                                assert!(cs.is_satisfied());
                                println!("test enforce not equal successfully");
                            } else {
                                assert!(!cs.is_satisfied());
                                println!("test enforce not satisfied not equal successfully");
                            }
                        } else {
                            assert!(cs.is_satisfied());
                            println!("test not enforce not equal successfully");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_and() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                let mut cs = TestConstraintSystem::<Bls12>::new();

                let a;
                let b;

                {
                    let mut dyn_construct = |operand, name| {
                        let cs = cs.namespace(|| name);

                        match operand {
                            OperandType::True => Boolean::constant(true),
                            OperandType::False => Boolean::constant(false),
                            OperandType::AllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                            }
                            OperandType::AllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                            }
                            OperandType::NegatedAllocatedTrue => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap()).not()
                            }
                            OperandType::NegatedAllocatedFalse => {
                                Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap()).not()
                            }
                        }
                    };

                    a = dyn_construct(first_operand, "a");
                    b = dyn_construct(second_operand, "b");
                }

                let c = Boolean::and(&mut cs, &a, &b).unwrap();

                assert!(cs.is_satisfied());

                match (first_operand, second_operand, c) {
                    (OperandType::True, OperandType::True, Boolean::Constant(true)) => {}
                    (OperandType::True, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::True, OperandType::AllocatedTrue, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::AllocatedFalse, Boolean::Is(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedTrue, Boolean::Not(_)) => {}
                    (OperandType::True, OperandType::NegatedAllocatedFalse, Boolean::Not(_)) => {}

                    (OperandType::False, OperandType::True, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::False, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedTrue, Boolean::Constant(false)) => {}
                    (OperandType::False, OperandType::AllocatedFalse, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::False,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Constant(false),
                    ) => {}

                    (OperandType::AllocatedTrue, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedTrue, OperandType::False, Boolean::Constant(false)) => {}
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    (OperandType::AllocatedFalse, OperandType::True, Boolean::Is(_)) => {}
                    (OperandType::AllocatedFalse, OperandType::False, Boolean::Constant(false)) => {
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedTrue, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }

                    (OperandType::NegatedAllocatedFalse, OperandType::True, Boolean::Not(_)) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::False,
                        Boolean::Constant(false),
                    ) => {}
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::AllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("and not result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::zero());
                        assert_eq!(v.value, Some(false));
                    }
                    (
                        OperandType::NegatedAllocatedFalse,
                        OperandType::NegatedAllocatedFalse,
                        Boolean::Is(ref v),
                    ) => {
                        assert!(cs.get("nor result") == Field::one());
                        assert_eq!(v.value, Some(true));
                    }

                    _ => {
                        panic!(
                            "unexpected behavior at {:?} AND {:?}",
                            first_operand, second_operand
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_u64_into_boolean_vec_le() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let bits = u64_into_boolean_vec_le(&mut cs, Some(17234652694787248421)).unwrap();

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 64);

        assert_eq!(bits[63 - 0].get_value().unwrap(), true);
        assert_eq!(bits[63 - 1].get_value().unwrap(), true);
        assert_eq!(bits[63 - 2].get_value().unwrap(), true);
        assert_eq!(bits[63 - 3].get_value().unwrap(), false);
        assert_eq!(bits[63 - 4].get_value().unwrap(), true);
        assert_eq!(bits[63 - 5].get_value().unwrap(), true);
        assert_eq!(bits[63 - 20].get_value().unwrap(), true);
        assert_eq!(bits[63 - 21].get_value().unwrap(), false);
        assert_eq!(bits[63 - 22].get_value().unwrap(), false);
    }

    #[test]
    fn test_field_into_allocated_bits_le() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let r = Fr::from_str(
            "9147677615426976802526883532204139322118074541891858454835346926874644257775",
        )
        .unwrap();

        let bits = field_into_allocated_bits_le(&mut cs, Some(r)).unwrap();

        assert!(cs.is_satisfied());

        assert_eq!(bits.len(), 255);

        assert_eq!(bits[254 - 0].value.unwrap(), false);
        assert_eq!(bits[254 - 1].value.unwrap(), false);
        assert_eq!(bits[254 - 2].value.unwrap(), true);
        assert_eq!(bits[254 - 3].value.unwrap(), false);
        assert_eq!(bits[254 - 4].value.unwrap(), true);
        assert_eq!(bits[254 - 5].value.unwrap(), false);
        assert_eq!(bits[254 - 20].value.unwrap(), true);
        assert_eq!(bits[254 - 23].value.unwrap(), true);
    }

    #[test]
    fn test_boolean_sha256_ch() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TestConstraintSystem::<Bls12>::new();

                    let a;
                    let b;
                    let c;

                    // ch = (a and b) xor ((not a) and c)
                    let expected = (first_operand.val() & second_operand.val())
                        ^ ((!first_operand.val()) & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.namespace(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                        .not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                        .not()
                                }
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let maj = Boolean::sha256_ch(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(maj.get_value().unwrap(), expected);

                    if first_operand.is_constant()
                        || second_operand.is_constant()
                        || third_operand.is_constant()
                    {
                        if first_operand.is_constant()
                            && second_operand.is_constant()
                            && third_operand.is_constant()
                        {
                            assert_eq!(cs.num_constraints(), 0);
                        }
                    } else {
                        assert_eq!(cs.get("ch"), {
                            if expected {
                                Fr::one()
                            } else {
                                Fr::zero()
                            }
                        });
                        cs.set("ch", {
                            if expected {
                                Fr::zero()
                            } else {
                                Fr::one()
                            }
                        });
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "ch computation");
                    }
                }
            }
        }
    }

    #[test]
    fn test_boolean_sha256_maj() {
        let variants = [
            OperandType::True,
            OperandType::False,
            OperandType::AllocatedTrue,
            OperandType::AllocatedFalse,
            OperandType::NegatedAllocatedTrue,
            OperandType::NegatedAllocatedFalse,
        ];

        for first_operand in variants.iter().cloned() {
            for second_operand in variants.iter().cloned() {
                for third_operand in variants.iter().cloned() {
                    let mut cs = TestConstraintSystem::<Bls12>::new();

                    let a;
                    let b;
                    let c;

                    // maj = (a and b) xor (a and c) xor (b and c)
                    let expected = (first_operand.val() & second_operand.val())
                        ^ (first_operand.val() & third_operand.val())
                        ^ (second_operand.val() & third_operand.val());

                    {
                        let mut dyn_construct = |operand, name| {
                            let cs = cs.namespace(|| name);

                            match operand {
                                OperandType::True => Boolean::constant(true),
                                OperandType::False => Boolean::constant(false),
                                OperandType::AllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                }
                                OperandType::AllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                }
                                OperandType::NegatedAllocatedTrue => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(true)).unwrap())
                                        .not()
                                }
                                OperandType::NegatedAllocatedFalse => {
                                    Boolean::from(AllocatedBit::alloc(cs, Some(false)).unwrap())
                                        .not()
                                }
                            }
                        };

                        a = dyn_construct(first_operand, "a");
                        b = dyn_construct(second_operand, "b");
                        c = dyn_construct(third_operand, "c");
                    }

                    let maj = Boolean::sha256_maj(&mut cs, &a, &b, &c).unwrap();

                    assert!(cs.is_satisfied());

                    assert_eq!(maj.get_value().unwrap(), expected);

                    if first_operand.is_constant()
                        || second_operand.is_constant()
                        || third_operand.is_constant()
                    {
                        if first_operand.is_constant()
                            && second_operand.is_constant()
                            && third_operand.is_constant()
                        {
                            assert_eq!(cs.num_constraints(), 0);
                        }
                    } else {
                        assert_eq!(cs.get("maj"), {
                            if expected {
                                Fr::one()
                            } else {
                                Fr::zero()
                            }
                        });
                        cs.set("maj", {
                            if expected {
                                Fr::zero()
                            } else {
                                Fr::one()
                            }
                        });
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "maj computation");
                    }
                }
            }
        }
    }
}

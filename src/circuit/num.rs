use bellman::pairing::Engine;

use bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use bellman::{ConstraintSystem, LinearCombination, SynthesisError, Variable};

use super::Assignment;

use super::boolean::{self, AllocatedBit, Boolean};

use std::ops::{Add, Sub};
use circuit::expression::Expression;

pub struct AllocatedNum<E: Engine> {
    value: Option<E::Fr>,
    variable: Variable,
}

impl<E: Engine> Clone for AllocatedNum<E> {
    fn clone(&self) -> Self {
        AllocatedNum {
            value: self.value,
            variable: self.variable,
        }
    }
}

impl<E: Engine> AllocatedNum<E> {
    pub fn alloc_constant<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let value = value()?;
        let temp = AllocatedNum::alloc(cs.namespace(|| "num"), || Ok(value))?;
        temp.assert_number(cs.namespace(|| "assert temp"), &value)?;
        Ok(temp)
    }

    pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(
            || "num",
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            },
        )?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var,
        })
    }

    pub fn one<CS>() -> Self
    where
        CS: ConstraintSystem<E>,
    {
        let new_value = Some(E::Fr::one());

        AllocatedNum {
            value: new_value,
            variable: CS::one(),
        }
    }

    pub fn zero<CS>(mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let new_value = Some(E::Fr::zero());

        let var = cs.alloc(|| "zero num", || Ok(E::Fr::zero()))?;

        cs.enforce(
            || "enforce one is actually one",
            |lc| lc + var,
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(AllocatedNum {
            value: new_value,
            variable: var,
        })
    }

    pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let input = cs.alloc_input(|| "input variable", || Ok(*self.value.get()?))?;

        cs.enforce(
            || "enforce input is correct",
            |zero| zero + input,
            |zero| zero + CS::one(),
            |zero| zero + self.variable,
        );

        Ok(())
    }

    /// Deconstructs this allocated number into its
    /// boolean representation in little-endian bit
    /// order, requiring that the representation
    /// strictly exists "in the field" (i.e., a
    /// congruency is not allowed.)
    pub fn into_bits_le_strict<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        pub fn kary_and<E, CS>(
            mut cs: CS,
            v: &[AllocatedBit],
        ) -> Result<AllocatedBit, SynthesisError>
        where
            E: Engine,
            CS: ConstraintSystem<E>,
        {
            assert!(v.len() > 0);

            // Let's keep this simple for now and just AND them all
            // manually
            let mut cur = None;

            for (i, v) in v.iter().enumerate() {
                if cur.is_none() {
                    cur = Some(v.clone());
                } else {
                    cur = Some(AllocatedBit::and(
                        cs.namespace(|| format!("and {}", i)),
                        cur.as_ref().unwrap(),
                        v,
                    )?);
                }
            }

            Ok(cur.expect("v.len() > 0"))
        }

        // We want to ensure that the bit representation of a is
        // less than or equal to r - 1.
        let mut a = self.value.map(|e| BitIterator::new(e.into_repr()));
        let mut b = E::Fr::char();
        b.sub_noborrow(&1.into());

        let mut result = vec![];

        // Runs of ones in r
        let mut last_run = None;
        let mut current_run = vec![];

        let mut found_one = false;
        let mut i = 0;
        for b in BitIterator::new(b) {
            let a_bit = a.as_mut().map(|e| e.next().unwrap());

            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                // a_bit should also be false
                a_bit.map(|e| assert!(!e));
                continue;
            }

            if b {
                // This is part of a run of ones. Let's just
                // allocate the boolean with the expected value.
                let a_bit = AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), a_bit)?;
                // ... and add it to the current run of ones.
                current_run.push(a_bit.clone());
                result.push(a_bit);
            } else {
                if current_run.len() > 0 {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    if last_run.is_some() {
                        current_run.push(last_run.clone().unwrap());
                    }
                    last_run = Some(kary_and(
                        cs.namespace(|| format!("run ending at {}", i)),
                        &current_run,
                    )?);
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.

                let a_bit = AllocatedBit::alloc_conditionally(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit,
                    &last_run.as_ref().expect("char always starts with a one"),
                )?;
                result.push(a_bit);
            }

            i += 1;
        }

        // char is prime, so we'll always end on
        // a run of zeros.
        assert_eq!(current_run.len(), 0);

        // Now, we have `result` in big-endian order.
        // However, now we have to unpack self!

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in result.iter().rev() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        cs.enforce(
            || "unpacking constraint",
            |_| packed_lc,
            |zero| zero + CS::one(),
            |zero| zero + self.get_variable(),
        );

        // Convert into booleans, and reverse for little-endian bit order
        Ok(result.into_iter().map(|b| Boolean::from(b)).rev().collect())
    }

    /// Convert the allocated number into its little-endian representation.
    /// Note that this does not strongly enforce that the commitment is
    /// "in the field."
    pub fn into_bits_le<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let bits = boolean::field_into_allocated_bits_le(&mut cs, self.value)?;

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        cs.enforce(
            || "unpacking constraint",
            |_| packed_lc,
            |zero| zero + CS::one(),
            |zero| zero + self.get_variable(),
        );

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }
    /// Return fixed amount of bits of the allocated number.
    /// Should be used when there is a priori knowledge of bit length of the number
    pub fn into_bits_le_fixed<CS>(
        &self,
        mut cs: CS,
        bit_length: usize,
    ) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        assert!(bit_length <= E::Fr::NUM_BITS as usize);
        let bits = boolean::field_into_allocated_bits_le_fixed(&mut cs, self.value, bit_length)?;

        let mut packed_lc = LinearCombination::zero();
        let mut coeff = E::Fr::one();

        for bit in bits.iter() {
            packed_lc = packed_lc + (coeff, bit.get_variable());

            coeff.double();
        }

        cs.enforce(
            || "unpacking constraint",
            |_| packed_lc,
            |zero| zero + CS::one(),
            |zero| zero + self.get_variable(),
        );

        Ok(bits.into_iter().map(|b| Boolean::from(b)).collect())
    }

    /// Return allocated number given its bit representation
    pub fn pack_bits_to_element<CS: ConstraintSystem<E>>(
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        assert!(bits.len() <= E::Fr::NUM_BITS as usize);

        let mut data_from_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in bits {
            data_from_lc = data_from_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        let data_packed = AllocatedNum::alloc(cs.namespace(|| "allocate packed number"), || {
            Ok(*data_from_lc.get_value().get()?)
        })?;

        cs.enforce(
            || "pack bits to number",
            |zero| zero + data_packed.get_variable(),
            |zero| zero + CS::one(),
            |_| data_from_lc.lc(E::Fr::one()),
        );

        Ok(data_packed)
    }

    pub fn add<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "add num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.add_assign(other.value.get()?);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        cs.enforce(
            || "addition constraint",
            |zero| zero + self.variable + other.variable,
            |zero| zero + CS::one(),
            |zero| zero + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn add_constant<CS>(&self, mut cs: CS, constant: E::Fr) -> Result<AllocatedNum<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "add constant to num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.add_assign(&constant);

                value = Some(tmp);

                Ok(tmp)
            }
        )?;

        cs.enforce(
            || "addition constraint",
            |zero| zero + self.variable + (constant, CS::one()),
            |zero| zero + CS::one(),
            |zero| zero + var
        );

        Ok(AllocatedNum {
            value,
            variable: var
        })
    }

    pub fn sub<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "sub num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.sub_assign(other.value.get()?);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        cs.enforce(
            || "addition constraint",
            |zero| zero + self.variable - other.variable,
            |zero| zero + CS::one(),
            |zero| zero + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn mul<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "product num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.mul_assign(other.value.get()?);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        // Constrain: a * b = ab
        cs.enforce(
            || "multiplication constraint",
            |zero| zero + self.variable,
            |zero| zero + other.variable,
            |zero| zero + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn mul_constant<CS>(&self, mut cs: CS, constant: E::Fr) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "product num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.mul_assign(&constant);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        cs.enforce(
            || "multiplication constraint",
            |zero| zero + self.variable,
            |zero| zero + (constant, CS::one()),
            |zero| zero + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn div<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value_inv = None;

        let var_inv = cs.alloc(
            || "div num",
            || {
                let tmp = *other.value.get()?;

                if tmp.is_zero() {
                    Err(SynthesisError::DivisionByZero)
                } else {
                    let tmp_inv = tmp.inverse().unwrap();
                    value_inv = Some(tmp_inv);
                    Ok(tmp_inv)
                }
            },
        )?;

        cs.enforce(
            || "inv multiplication constraint",
            |zero| zero + var_inv,
            |zero| zero + other.variable,
            |zero| zero + CS::one(),
        );

        Ok(self.mul(
            cs,
            &AllocatedNum {
                value: value_inv,
                variable: var_inv,
            },
        )?)
    }

    pub fn square<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "squared num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.square();

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        cs.enforce(
            || "squaring constraint",
            |zero| zero + self.variable,
            |zero| zero + self.variable,
            |zero| zero + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn pow_constant<CS>(&self, mut cs: CS, power: &E::Fr) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let power_bits: Vec<bool> = BitIterator::new(power.into_repr()).collect();
        let mut temp = AllocatedNum::alloc(cs.namespace(|| "one"), || Ok(E::Fr::one()))?;
        temp.assert_number(cs.namespace(|| "assert_one"), &E::Fr::one())?;

        for (i, bit) in power_bits.iter().enumerate() {
            temp = temp.square(cs.namespace(|| format!("square on step: {}", i)))?;
            if *bit {
                temp = temp.mul(cs.namespace(|| format!("mul step: {}", i)), &self)?;
            }
        }

        Ok(temp)
    }

    pub fn pow<CS>(&self, mut cs: CS, power_bits: &[Boolean]) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut temp = self.clone();
        let mut result = AllocatedNum::one::<CS>();
        for (i, bit) in power_bits.iter().enumerate() {
            let base = AllocatedNum::conditionally_select(
                cs.namespace(|| format!("according to {}th bit,select correct base", i)),
                &temp,
                &AllocatedNum::one::<CS>(),
                bit,
            )?;
            result = result.mul(cs.namespace(|| format!("n * base{}", i)), &base)?;
            temp = temp.square(cs.namespace(|| format!("square on step: {}", i)))?;
        }

        Ok(result)
    }

    pub fn assert_nonzero<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let inv = cs.alloc(
            || "ephemeral inverse",
            || {
                let tmp = *self.value.get()?;

                if tmp.is_zero() {
                    Err(SynthesisError::DivisionByZero)
                } else {
                    Ok(tmp.inverse().unwrap())
                }
            },
        )?;

        // Constrain a * inv = 1, which is only valid
        // iff a has a multiplicative inverse, untrue
        // for zero.
        cs.enforce(
            || "nonzero assertion constraint",
            |zero| zero + self.variable,
            |zero| zero + inv,
            |zero| zero + CS::one(),
        );

        Ok(())
    }

    pub fn assert_zero<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        cs.enforce(
            || "zero assertion constraint",
            |zero| zero + self.variable,
            |zero| zero + CS::one(),
            |zero| zero,
        );

        Ok(())
    }

    pub fn assert_number<CS>(&self, mut cs: CS, number: &E::Fr) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        cs.enforce(
            || "number assertion constraint",
            |zero| zero + self.variable - (number.clone(), CS::one()),
            |zero| zero + CS::one(),
            |zero| zero,
        );

        Ok(())
    }
    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        match condition {
            Boolean::Constant(true) => Ok((b.clone(), a.clone())),
            Boolean::Constant(false) => Ok((a.clone(), b.clone())),
            _ => {
                let c = Self::alloc(cs.namespace(|| "conditional reversal result 1"), || {
                    if *condition.get_value().get()? {
                        Ok(*b.value.get()?)
                    } else {
                        Ok(*a.value.get()?)
                    }
                })?;

                cs.enforce(
                    || "first conditional reversal",
                    |zero| zero + a.variable - b.variable,
                    |_| condition.lc(CS::one(), E::Fr::one()),
                    |zero| zero + a.variable - c.variable,
                );

                let d = Self::alloc(cs.namespace(|| "conditional reversal result 2"), || {
                    if *condition.get_value().get()? {
                        Ok(*a.value.get()?)
                    } else {
                        Ok(*b.value.get()?)
                    }
                })?;

                cs.enforce(
                    || "second conditional reversal",
                    |zero| zero + b.variable - a.variable,
                    |_| condition.lc(CS::one(), E::Fr::one()),
                    |zero| zero + b.variable - d.variable,
                );

                Ok((c, d))
            }
        }
    }

    /// Takes two allocated numbers (a, b) and returns
    /// a if the condition is true, and b
    /// otherwise.
    /// Most often to be used with b = 0
    pub fn conditionally_select<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let c = Self::alloc(cs.namespace(|| "conditional select result"), || {
            if *condition.get_value().get()? {
                Ok(*a.value.get()?)
            } else {
                Ok(*b.value.get()?)
            }
        })?;

        // a * condition + b*(1-condition) = c ->
        // a * condition - b*condition = c - b

        cs.enforce(
            || "conditional select constraint",
            |zero| zero + a.variable - b.variable,
            |_| condition.lc(CS::one(), E::Fr::one()),
            |zero| zero + c.variable - b.variable,
        );

        Ok(c)
    }

    /// Enforces that self == other if `should_enforce is true`.
    ///
    /// This requires one constraint.
    pub fn conditional_enforce_equal<CS: ConstraintSystem<E>, EX: Into<Expression<E>>>(
        &self,
        mut cs: CS,
        other: EX,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let other: Expression<E> = other.into();
        cs.enforce(
            || "conditional enforce equal",
            |zero| zero + &other.lc() - self.variable,
            |_| should_enforce.lc(CS::one(), E::Fr::one()),
            |zero| zero,
        );
        Ok(())
    }

    /// Enforces that self != other if `should_enforce is true`.
    ///
    /// This requires one constraint.
    pub fn conditional_enforce_not_equal<CS: ConstraintSystem<E>, EX: Into<Expression<E>>>(
        &self,
        mut cs: CS,
        other: EX,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let other: Expression<E> = other.into();
        let multiplier = Self::alloc(
            cs.namespace(|| "conditional select result"),
            || if *should_enforce.get_value().get()? {
                let mut value = *other.get_value().get()?;
                value.sub_assign(self.value.get()?);
                Ok(value.inverse().unwrap_or(E::Fr::zero()))
            } else {
                Ok(E::Fr::zero())
            }
        )?;

        cs.enforce(
            || "conditional enforce not equal",
            |zero| zero + &other.lc() - self.variable,
            |zero| zero + multiplier.variable,
            |_| should_enforce.lc(CS::one(), E::Fr::one()),
        );
        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// allocated boolean variable with value `true`
    /// if the `a` and `b` are equal, `false` otherwise.
    pub fn equals<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
    ) -> Result<AllocatedBit, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        // Allocate and constrain `r`: result boolean bit.
        // It equals `true` if `a` equals `b`, `false` otherwise

        let r_value = match (a.value, b.value) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        };

        let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

        // Let `delta = a - b`

        let delta_value = match (a.value, b.value) {
            (Some(a), Some(b)) => {
                // return (a - b)
                let mut a = a;
                a.sub_assign(&b);
                Some(a)
            }
            _ => None,
        };

        let x_value = match (delta_value, r_value) {
            (Some(delta), Some(r)) => {
                if delta.is_zero() {
                    Some(E::Fr::one())
                } else {
                    let mut mult: E::Fr;
                    if r {
                        mult = E::Fr::one();
                    } else {
                        mult = E::Fr::zero();
                    }
                    mult.sub_assign(&E::Fr::one());
                    let mut temp = delta.inverse().unwrap();
                    temp.mul_assign(&mult);
                    Some(temp)
                }
            }
            _ => None,
        };

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || x_value.grab())?;

        // Constrain allocation:
        // 0 = (a - b) * r
        // thus if (a-b) != 0 then r == 0
        cs.enforce(
            || "0 = (a - b) * r",
            |zero| zero + a.get_variable() - b.get_variable(),
            |zero| zero + r.get_variable(),
            |zero| zero,
        );

        // Constrain:
        // (a-b) * x == r - 1
        // and thus `r` is 1 if `(a - b)` is zero (a != b )
        cs.enforce(
            || "(a - b) * x == r - 1",
            |zero| zero + a.get_variable() - b.get_variable(),
            |zero| zero + x.get_variable(),
            |zero| zero + r.get_variable() - CS::one(),
        );

        Ok(r)
    }

    /// Returns `a == b ? x : y`
    pub fn select_ifeq<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        x: &Self,
        y: &Self,
    ) -> Result<Self, SynthesisError>
    where
        E: Engine,
        CS: ConstraintSystem<E>,
    {
        let eq = Self::equals(cs.namespace(|| "eq"), a, b)?;
        Self::conditionally_select(cs.namespace(|| "select"), x, y, &Boolean::from(eq))
    }

    /// Limits number of bits. The easiest example when required
    /// is to add or subtract two "small" (with bit length smaller
    /// than one of the field) numbers and check for overflow
    pub fn limit_number_of_bits<CS>(
        &self,
        mut cs: CS,
        number_of_bits: usize,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // do the bit decomposition and check that higher bits are all zeros

        let mut bits = self.into_bits_le(cs.namespace(|| "unpack to limit number of bits"))?;

        bits.drain(0..number_of_bits);

        // repack

        let mut top_bits_lc = Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in bits.into_iter() {
            top_bits_lc = top_bits_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        // enforce packing and zeroness
        cs.enforce(
            || "repack top bits",
            |zero| zero,
            |zero| zero + CS::one(),
            |_| top_bits_lc.lc(E::Fr::one()),
        );

        Ok(())
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }
}

pub struct Num<E: Engine> {
    value: Option<E::Fr>,
    lc: LinearCombination<E>,
}

impl<E: Engine> From<AllocatedNum<E>> for Num<E> {
    fn from(num: AllocatedNum<E>) -> Num<E> {
        Num {
            value: num.value,
            lc: LinearCombination::<E>::zero() + num.variable,
        }
    }
}

impl<E: Engine> Clone for Num<E> {
    fn clone(&self) -> Self {
        Num {
            value: self.value.clone(),
            lc: self.lc.clone(),
        }
    }
}

impl<E: Engine> Num<E> {
    pub fn zero() -> Self {
        Num {
            value: Some(E::Fr::zero()),
            lc: LinearCombination::zero(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.lc.as_ref().len() == 0
    }

    pub fn len(&self) -> usize {
        self.lc.as_ref().len()
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn lc(&self, coeff: E::Fr) -> LinearCombination<E> {
        LinearCombination::zero() + (coeff, &self.lc)
    }

    pub fn add_number_with_coeff(self, variable: &AllocatedNum<E>, coeff: E::Fr) -> Self {
        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + (coeff, variable.get_variable()),
        }
    }

    pub fn add_assign_number_with_coeff(&mut self, variable: &AllocatedNum<E>, coeff: E::Fr) {
        let newval = match (self.value, variable.get_value()) {
            (Some(mut curval), Some(val)) => {
                let mut tmp = val;
                tmp.mul_assign(&coeff);

                curval.add_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        self.value = newval;
        self.lc.as_mut().push((variable.get_variable(), coeff));
    }

    pub fn add_bool_with_coeff(self, one: Variable, bit: &Boolean, coeff: E::Fr) -> Self {
        let newval = match (self.value, bit.get_value()) {
            (Some(mut curval), Some(bval)) => {
                if bval {
                    curval.add_assign(&coeff);
                }

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + &bit.lc(one, coeff),
        }
    }

    pub fn add_constant(self, one: Variable, coeff: E::Fr) -> Self {
        let newval = match self.value {
            Some(mut curval) => {
                curval.add_assign(&coeff);

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + (coeff, one),
        }
    }

    pub fn into_allocated_num<CS: ConstraintSystem<E>>(
        self,
        mut cs: CS,
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        if self.lc.as_ref().len() == 1 {
            return Ok(self.unwrap_as_allocated_num());
        }
        let var = AllocatedNum::alloc(cs.namespace(|| "allocate a collapse result"), || {
            let val = *self.get_value().get()?;

            Ok(val)
        })?;

        cs.enforce(
            || "enforce collapse constraint",
            |_| self.lc - var.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(var)
    }

    pub fn unwrap_as_allocated_num(&self) -> AllocatedNum<E> {
        assert!(self.lc.as_ref().len() == 1);
        let (var, c) = self.lc.as_ref().last().unwrap().clone();
        assert!(c == E::Fr::one());

        let var = AllocatedNum {
            value: self.value,
            variable: var,
        };

        var
    }
}

impl<E: Engine> Add<&Num<E>> for Num<E> {
    type Output = Num<E>;

    fn add(self, other: &Num<E>) -> Num<E> {
        let newval = match (self.value, other.value) {
            (Some(mut curval), Some(val)) => {
                let tmp = val;
                curval.add_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + &other.lc,
        }
    }
}

impl<E: Engine> Sub<&Num<E>> for Num<E> {
    type Output = Num<E>;

    fn sub(self, other: &Num<E>) -> Num<E> {
        let newval = match (self.value, other.value) {
            (Some(mut curval), Some(val)) => {
                let tmp = val;
                curval.sub_assign(&tmp);

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc - &other.lc,
        }
    }
}

#[cfg(test)]
mod test {
    use super::{AllocatedNum, Boolean, Num};
    use bellman::pairing::bls12_381::{Bls12, Fr};
    use bellman::pairing::ff::{BitIterator, Field, PrimeField};
    use bellman::ConstraintSystem;
    use circuit::test::*;
    use rand::{Rand, Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_allocated_num() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        AllocatedNum::alloc(&mut cs, || Ok(Fr::one())).unwrap();

        assert!(cs.get("num") == Fr::one());
    }

    #[test]
    fn test_num_squaring() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();
        let n2 = n.square(&mut cs).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("squared num") == Fr::from_str("9").unwrap());
        assert!(n2.value.unwrap() == Fr::from_str("9").unwrap());
        cs.set("squared num", Fr::from_str("10").unwrap());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_limit_number_of_bits() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();

        n.limit_number_of_bits(&mut cs, 2).unwrap();

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_limit_number_of_bits_error() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();

        n.limit_number_of_bits(&mut cs, 1).unwrap();
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_multiplication() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n =
            AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let n2 =
            AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let n3 = n.mul(&mut cs, &n2).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("product num") == Fr::from_str("120").unwrap());
        assert!(n3.value.unwrap() == Fr::from_str("120").unwrap());
        cs.set("product num", Fr::from_str("121").unwrap());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_conditional_reversal() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(false);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }

        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();
            let condition = Boolean::constant(true);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), d.value.unwrap());
            assert_eq!(b.value.unwrap(), c.value.unwrap());
        }
    }

    #[test]
    fn test_num_conditional_select() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(rng.gen())).unwrap();
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(rng.gen())).unwrap();

            let condition_true = Boolean::constant(true);
            let c =
                AllocatedNum::conditionally_select(cs.namespace(|| "c"), &a, &b, &condition_true)
                    .unwrap();

            let condition_false = Boolean::constant(false);
            let d =
                AllocatedNum::conditionally_select(cs.namespace(|| "d"), &a, &b, &condition_false)
                    .unwrap();

            assert!(cs.is_satisfied());
            assert!(cs.num_constraints() == 2);

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }
    }

    #[test]
    fn test_num_equals() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let a =
            AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let b =
            AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let c =
            AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("10").unwrap())).unwrap();

        let not_eq = AllocatedNum::equals(cs.namespace(|| "not_eq"), &a, &b).unwrap();
        let eq = AllocatedNum::equals(cs.namespace(|| "eq"), &a, &c).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2 * 3);

        assert_eq!(not_eq.get_value().unwrap(), false);
        assert_eq!(eq.get_value().unwrap(), true);
    }

    #[test]
    fn test_num_enforce_equals_or_not() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let a =
            AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("10").unwrap())).unwrap();
        let b =
            AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("12").unwrap())).unwrap();
        let c =
            AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("10").unwrap())).unwrap();

        a.conditional_enforce_equal(
            cs.namespace(|| "enforce eq: a == c"),
            &c,
            &Boolean::constant(true)
        ).unwrap();
        a.conditional_enforce_equal(
            cs.namespace(|| "not enforce eq"),
            &b,
            &Boolean::constant(false)
        ).unwrap();
        a.conditional_enforce_not_equal(
            cs.namespace(|| "enforce not_eq: a != b"),
            &b,
            &Boolean::constant(true)
        ).unwrap();
        a.conditional_enforce_not_equal(
            cs.namespace(|| "not enforce not_eq"),
            &c,
            &Boolean::constant(false)
        ).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 4);
    }

    #[test]
    fn test_not_satisfied_num_enforce_equals() {
        let a_and_b = [
            (10u32, 10),
            (10, 12)
        ];
        for (a, b) in a_and_b {
            let eq = a == b;
            let mut cs = TestConstraintSystem::<Bls12>::new();
            let a =
                AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str(&a.to_string()).unwrap())).unwrap();
            let b =
                AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str(&b.to_string()).unwrap())).unwrap();

            if eq {
                a.conditional_enforce_not_equal(
                    cs.namespace(|| "enforce not eq: a != b"),
                    &b,
                    &Boolean::constant(true),
                ).unwrap();
            } else {
                a.conditional_enforce_equal(
                    cs.namespace(|| "enforce eq: a == b"),
                    &b,
                    &Boolean::constant(true),
                ).unwrap();
            }

            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn select_if_equals() {
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let a =
            AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::from_str("0").unwrap())).unwrap();
        let b =
            AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::from_str("1").unwrap())).unwrap();
        let c =
            AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(Fr::from_str("0").unwrap())).unwrap();

        let x =
            AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(Fr::from_str("100").unwrap())).unwrap();
        let y =
            AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(Fr::from_str("200").unwrap())).unwrap();

        let n_eq = AllocatedNum::select_ifeq(cs.namespace(|| "ifeq"), &a, &c, &x, &y).unwrap();
        let n_not_eq = AllocatedNum::select_ifeq(cs.namespace(|| "ifneq"), &a, &b, &x, &y).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(n_eq.get_value().unwrap(), Fr::from_str("100").unwrap());
        assert_eq!(n_not_eq.get_value().unwrap(), Fr::from_str("200").unwrap());
    }

    #[test]
    fn test_num_nonzero() {
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::from_str("3").unwrap())).unwrap();
            n.assert_nonzero(&mut cs).unwrap();

            assert!(cs.is_satisfied());
            cs.set("ephemeral inverse", Fr::from_str("3").unwrap());
            assert!(cs.which_is_unsatisfied() == Some("nonzero assertion constraint"));
        }
        {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Fr::zero())).unwrap();
            assert!(n.assert_nonzero(&mut cs).is_err());
        }
    }

    #[test]
    fn test_into_bits_strict() {
        let mut negone = Fr::one();
        negone.negate();

        let mut cs = TestConstraintSystem::<Bls12>::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(negone)).unwrap();
        n.into_bits_le_strict(&mut cs).unwrap();

        assert!(cs.is_satisfied());

        // make the bit representation the characteristic
        cs.set("bit 254/boolean", Fr::one());

        // this makes the conditional boolean constraint fail
        assert_eq!(
            cs.which_is_unsatisfied().unwrap(),
            "bit 254/boolean constraint"
        );
    }

    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for i in 0..200 {
            let r = Fr::rand(&mut rng);
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();

            let bits = if i % 2 == 0 {
                n.into_bits_le(&mut cs).unwrap()
            } else {
                n.into_bits_le_strict(&mut cs).unwrap()
            };

            assert!(cs.is_satisfied());

            for (b, a) in BitIterator::new(r.into_repr())
                .skip(1)
                .zip(bits.iter().rev())
            {
                if let &Boolean::Is(ref a) = a {
                    assert_eq!(b, a.get_value().unwrap());
                } else {
                    unreachable!()
                }
            }

            cs.set("num", Fr::rand(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());

            for i in 0..Fr::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fr::one();
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }
}

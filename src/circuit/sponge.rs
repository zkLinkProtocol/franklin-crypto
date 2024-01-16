use crate::{
    poseidon::common::domain_strategy::DomainStrategy,
    poseidon::traits::{HashFamily, HashParams},
};
use crate::bellman::Field;
use crate::{bellman::{Engine, SynthesisError}};
use std::convert::TryInto;
use std::fmt::format;
use bellman::{ConstraintSystem, LinearCombination};
use circuit::boolean::Boolean;
use circuit::expression::Expression;
use circuit::num::{AllocatedNum, Num};

pub fn circuit_generic_hash<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
    const LENGTH: usize,
>(
    cs: &mut CS,
    input: &[AllocatedNum<E>; LENGTH],
    params: &P,
    domain_strategy: Option<DomainStrategy>,
) -> Result<[Num<E>; RATE], SynthesisError> {
    CircuitGenericSponge::hash(cs, input, params, domain_strategy)
}

pub fn circuit_generic_hash_num<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
    const LENGTH: usize,
>(
    cs: &mut CS,
    input: &[AllocatedNum<E>; LENGTH],
    params: &P,
    domain_strategy: Option<DomainStrategy>,
) -> Result<[AllocatedNum<E>; RATE], SynthesisError> {
    CircuitGenericSponge::hash_num(cs, input, params, domain_strategy)
}

#[derive(Clone)]
enum SpongeMode<E: Engine, const RATE: usize> {
    Absorb([Option<AllocatedNum<E>>; RATE]),
    Squeeze([Option<Num<E>>; RATE]),
}

#[derive(Clone)]
pub struct CircuitGenericSponge<E: Engine, const RATE: usize, const WIDTH: usize> {
    state: [Num<E>; WIDTH],
    mode: SpongeMode<E, RATE>,
    domain_strategy: DomainStrategy,
}

impl<'a, E: Engine, const RATE: usize, const WIDTH: usize> CircuitGenericSponge<E, RATE, WIDTH> {
    pub fn new() -> Self {
        Self::new_from_domain_strategy(DomainStrategy::CustomVariableLength)
    }

    pub fn new_from_domain_strategy(domain_strategy: DomainStrategy) -> Self {
        match domain_strategy {
            DomainStrategy::CustomVariableLength | DomainStrategy::VariableLength => (),
            _ => panic!("only variable length domain strategies allowed"),
        }
        let state = (0..WIDTH)
            .map(|_| Num::zero())
            .collect::<Vec<_>>()
            .try_into()
            .expect("constant array");
        Self {
            state,
            mode: SpongeMode::Absorb(vec![None; RATE].try_into().unwrap()),
            domain_strategy,
        }
    }

    pub fn hash<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        mut cs: CS,
        input: &[AllocatedNum<E>],
        params: &P,
        domain_strategy: Option<DomainStrategy>,
    ) -> Result<[Num<E>; RATE], SynthesisError> {
        let domain_strategy = domain_strategy.unwrap_or(DomainStrategy::CustomFixedLength);
        match domain_strategy {
            DomainStrategy::CustomFixedLength | DomainStrategy::FixedLength => (),
            _ => panic!("only fixed length domain strategies allowed"),
        }
        // init state
        let mut state: [Num<E>; WIDTH] = (0..WIDTH)
            .map(|_| Num::zero())
            .collect::<Vec<Num<E>>>()
            .try_into()
            .expect("constant array of LCs");

        let domain_strategy = DomainStrategy::CustomFixedLength;
        // specialize capacity
        let capacity_value = domain_strategy
            .compute_capacity::<E>(input.len(), RATE)
            .unwrap_or(E::Fr::zero());
        state
            .last_mut()
            .expect("last element")
            .add_assign_constant(CS::one(), capacity_value);

        // compute padding values
        let padding_values = domain_strategy
            .generate_padding_values::<E>(input.len(), RATE)
            .iter()
            .enumerate()
            .map(|(i, el)| AllocatedNum::alloc_constant(cs.namespace(|| format!("padding {}th constant", i)), || Ok(*el)))
            .collect::<Result<Vec<AllocatedNum<E>>, SynthesisError>>()?;

        // chain all values
        let mut padded_input = smallvec::SmallVec::<[_; 9]>::new();
        padded_input.extend(input.to_owned());
        padded_input.extend(padding_values);

        assert_eq!(padded_input.len() % RATE, 0);

        // process each chunk of input
        for (i, values) in padded_input.chunks_exact(RATE).enumerate() {
            absorb(
                cs.namespace(|| format!("absorb {}th input", i)),
                &mut state,
                values.try_into().expect("constant array"),
                params,
            )?;
        }

        // prepare output
        let mut output = arrayvec::ArrayVec::<_, RATE>::new();
        for s in state[..RATE].iter() {
            output.push(s.clone());
        }

        Ok(output.into_inner().expect("array"))
    }

    pub fn hash_num<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        mut cs: CS,
        input: &[AllocatedNum<E>],
        params: &P,
        domain_strategy: Option<DomainStrategy>
    ) -> Result<[AllocatedNum<E>; RATE], SynthesisError> {
        let result = Self::hash(cs.namespace(|| "calc hash"), input, params, domain_strategy)?;
        // prepare output
        let output = result.iter()
            .enumerate()
            .map(|(i, res)| res.clone().into_allocated_num(cs.namespace(|| format!("convert {}th result to AllocatedNum", i))))
            .collect::<Result<Vec<_>, SynthesisError>>()?
            .try_into()
            .unwrap();

        Ok(output)
    }

    pub fn absorb_multiple<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        &mut self,
        cs: &mut CS,
        input: &[AllocatedNum<E>],
        params: &P,
    ) -> Result<(), SynthesisError> {
        for inp in input.into_iter() {
            self.absorb(cs, inp.clone(), params)?
        }

        Ok(())
    }

    pub fn absorb<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        &mut self,
        cs: &mut CS,
        input: AllocatedNum<E>,
        params: &P,
    ) -> Result<(), SynthesisError> {
        match self.mode {
            SpongeMode::Absorb(ref mut buf) => {
                // push value into buffer
                for el in buf.iter_mut() {
                    if el.is_none() {
                        // we still have empty room for values
                        *el = Some(input);
                        return Ok(());
                    }
                }

                // buffer is filled so unwrap them
                let zero = AllocatedNum::zero(cs.namespace(|| "zero"))?;
                let mut unwrapped_buffer: [AllocatedNum<E>; RATE] = vec![zero.clone(); RATE].try_into().unwrap();
                for (a, b) in unwrapped_buffer.iter_mut().zip(buf.iter_mut()) {
                    if let Some(val) = b {
                        *a = val.clone();
                        *b = None; // kind of resetting buffer
                    }
                }

                // here we can absorb values. run round function implicitly there
                absorb::<_, _, P, RATE, WIDTH>(cs, &mut self.state, &mut unwrapped_buffer, params)?;

                // absorb value
                buf[0] = Some(input);
            }
            SpongeMode::Squeeze(_) => {
                // we don't need squeezed values so switching to absorbing mode is fine
                let mut buf = vec![None; RATE];
                buf[0] = Some(input);
                self.mode = SpongeMode::Absorb(buf.try_into().unwrap())
            }
        }

        Ok(())
    }

    /// Apply padding manually especially when single absorb called single/many times
    pub fn pad_if_necessary<CS: ConstraintSystem<E>>(&mut self, mut cs: CS) -> Result<(), SynthesisError>{
        match self.mode {
            SpongeMode::Absorb(ref mut buf) => {
                let unwrapped_buffer_len = buf.iter().filter(|el| el.is_some()).count();
                // compute padding values
                let padding_strategy = DomainStrategy::CustomVariableLength;
                let padding_values =
                    padding_strategy.generate_padding_values::<E>(unwrapped_buffer_len, RATE);
                let mut padding_values_it = padding_values.into_iter();

                for b in buf {
                    if b.is_none() {
                        *b = Some(AllocatedNum::alloc_constant(
                            cs.namespace(|| "alloc padding value"),
                            || Ok(padding_values_it.next().expect("next elm"))
                        )?);
                    }
                }
                assert!(padding_values_it.next().is_none());
                Ok(())
            }
            SpongeMode::Squeeze(_) => Ok(()),
        }
    }

    pub fn squeeze<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        &mut self,
        cs: &mut CS,
        params: &P,
    ) -> Result<Option<Num<E>>, SynthesisError> {
        let zero = AllocatedNum::zero(cs.namespace(|| "zero "))?;
        let mut i = 0;
        loop {
            match self.mode {
                SpongeMode::Absorb(ref mut buf) => {
                    // buffer may not be filled fully so we may need padding.
                    let mut unwrapped_buffer = arrayvec::ArrayVec::<_, RATE>::new();
                    for el in buf {
                        if let Some(value) = el {
                            unwrapped_buffer.push(value.clone());
                        }
                    }

                    if unwrapped_buffer.len() != RATE {
                        // processing buffer was done and we need padding
                        return Ok(None);
                    }

                    // make input array
                    let mut all_inputs:[AllocatedNum<E>; RATE] = vec![zero.clone(); RATE].try_into().unwrap();
                    for (a, b) in all_inputs.iter_mut().zip(unwrapped_buffer) {
                        *a = b;
                    }

                    // permute state
                    absorb(cs.namespace(|| format!("{}th permute state", i)), &mut self.state, &all_inputs, params)?;

                    // we are switching squeezing mode so we can ignore to reset absorbing buffer
                    let mut squeezed_buffer = arrayvec::ArrayVec::<_, RATE>::new();
                    for s in self.state[..RATE].iter() {
                        squeezed_buffer.push(Some(s.clone()));
                    }
                    self.mode = SpongeMode::Squeeze(squeezed_buffer.into_inner().expect("length must match"));
                }
                SpongeMode::Squeeze(ref mut buf) => {
                    for el in buf {
                        if let Some(value) = el.take() {
                            return Ok(Some(value));
                        }
                    }
                    return Ok(None);
                }
            };
            i += 1;
        }
    }

    pub fn squeeze_num<CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
        &mut self,
        cs: &mut CS,
        params: &P,
    ) -> Result<Option<AllocatedNum<E>>, SynthesisError> {
        if let Some(value) = self.squeeze(cs, params)? {
            Ok(Some(value.into_allocated_num(cs.namespace(|| "convert squeeze num"))?))
        } else {
            Ok(None)
        }
    }
}

fn absorb<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    mut cs: CS,
    state: &mut [Num<E>; WIDTH],
    input: &[AllocatedNum<E>; RATE],
    params: &P,
) -> Result<(), SynthesisError> {
    for (v, s) in input.iter().zip(state.iter_mut()) {
        s.add_assign_number_with_coeff(v, E::Fr::one());
    }
    circuit_generic_round_function(cs, state, params)
}

pub fn circuit_generic_round_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    mut cs: CS,
    state: &mut [Num<E>; WIDTH],
    params: &P,
) -> Result<(), SynthesisError> {
    match params.hash_family() {
        // HashFamily::Rescue => super::rescue::circuit_rescue_round_function(cs, params, state),
        HashFamily::Poseidon => super::poseidon::circuit_poseidon_round_function(cs.namespace(|| "circuit_poseidon_round_function"), params, state),
        // HashFamily::RescuePrime => {
        //     super::rescue_prime::gadget_rescue_prime_round_function(cs, params, state)
        // }
    }
}

pub fn circuit_generic_round_function_conditional<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    cs: &mut CS,
    state: &mut [Num<E>; WIDTH],
    execute: &Boolean,
    params: &P,
) -> Result<(), SynthesisError> {
    let zero = AllocatedNum::zero(cs.namespace(|| "alloc zero"))?;
    let mut old_state_nums = vec![zero.clone(); WIDTH];
    for (i, (lc, s)) in state.iter().zip(old_state_nums.iter_mut()).enumerate() {
        *s = lc.clone().into_allocated_num(cs.namespace(|| format!("convert to {}th state", i)))?;
    }
    let tmp = match params.hash_family() {
        // HashFamily::Rescue => super::rescue::circuit_rescue_round_function(cs, params, state),
        HashFamily::Poseidon => super::poseidon::circuit_poseidon_round_function(cs.namespace(|| "circuit_poseidon_round_function"), params, state),
        // HashFamily::RescuePrime => {
        //     super::rescue_prime::gadget_rescue_prime_round_function(cs, params, state)
        // }
    };

    let _ = tmp?;

    let mut new_state_nums = vec![zero.clone(); WIDTH];
    for (i, (lc, s)) in state.iter().zip(new_state_nums.iter_mut()).enumerate() {
        let mut cs = cs.namespace(|| format!("update {}th state", i));
        *s = lc.clone().into_allocated_num(cs.namespace(|| "lc into num"))?;
    }

    for (i, ((old, new), lc)) in old_state_nums
        .iter()
        .zip(new_state_nums.iter()).zip(state.iter_mut())
        .enumerate()
    {
        let selected = AllocatedNum::conditionally_select(
            cs.namespace(|| format!("select {}th old or new state", i)),
            &new,
            &old,
            execute,
        )?;
        *lc = Num::from(selected);
    }

    Ok(())
}

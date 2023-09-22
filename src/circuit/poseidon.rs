use super::sbox::sbox;
use super::sponge::circuit_generic_hash_num;
use super::matrix::{matrix_vector_product, mul_by_sparse_matrix};
use crate::{poseidon::common::domain_strategy::DomainStrategy, poseidon::params::PoseidonParams};
use crate::poseidon::traits::{HashFamily, HashParams};
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::bellman::{Field, SynthesisError};
use crate::{
    bellman::Engine,
    plonk::circuit::{allocated_num::Num, linear_combination::LinearCombination},
};

/// Receives inputs whose length `known` prior(fixed-length).
/// Also uses custom domain strategy which basically sets value of capacity element to
/// length of input and applies a padding rule which makes input size equals to multiple of
/// rate parameter.
/// Uses pre-defined state-width=3 and rate=2.
pub fn circuit_poseidon_hash<E: Engine, CS: ConstraintSystem<E>, const L: usize>(
    cs: &mut CS,
    input: &[Num<E>; L],
    domain_strategy: Option<DomainStrategy>,
) -> Result<[Num<E>; 2], SynthesisError> {
    const WIDTH: usize = 3;
    const RATE: usize = 2;
    let params = PoseidonParams::<E, RATE, WIDTH>::default();
    circuit_generic_hash_num(cs, input, &params, domain_strategy)
}

pub(crate) fn circuit_poseidon_round_function<
    E: Engine,
    CS: ConstraintSystem<E>,
    P: HashParams<E, RATE, WIDTH>,
    const RATE: usize,
    const WIDTH: usize,
>(
    cs: &mut CS,
    params: &P,
    state: &mut [LinearCombination<E>; WIDTH],
) -> Result<(), SynthesisError> {
    assert_eq!(
        params.hash_family(),
        HashFamily::Poseidon,
        "Incorrect hash family!"
    );
    assert!(params.number_of_full_rounds() % 2 == 0);

    let half_of_full_rounds = params.number_of_full_rounds() / 2;

    let (m_prime, sparse_matrixes) = &params.optimized_mds_matrixes();
    let optimized_round_constants = &params.optimized_round_constants();

    // first full rounds
    for round in 0..half_of_full_rounds {
        let round_constants = &optimized_round_constants[round];

        // add round constatnts
        for (s, c) in state.iter_mut().zip(round_constants.iter()) {
            s.add_assign_constant(*c);
        }
        // non linear sbox
        sbox(
            cs,
            params.alpha(),
            state,
            Some(0..WIDTH),
            params.custom_gate(),
        )?;

        // mul state by mds
        matrix_vector_product(&params.mds_matrix(), state)?;
    }

    state
        .iter_mut()
        .zip(optimized_round_constants[half_of_full_rounds].iter())
        .for_each(|(a, b)| a.add_assign_constant(*b));

    matrix_vector_product(&m_prime, state)?;

    let mut constants_for_partial_rounds = optimized_round_constants
        [half_of_full_rounds + 1..half_of_full_rounds + params.number_of_partial_rounds()]
        .to_vec();
    constants_for_partial_rounds.push([E::Fr::zero(); WIDTH]);
    // in order to reduce gate number we merge two consecutive iteration
    // which costs 2 gates per each

    for (round_constant, sparse_matrix) in constants_for_partial_rounds
        [..constants_for_partial_rounds.len() - 1]
        .chunks(2)
        .zip(sparse_matrixes[..sparse_matrixes.len() - 1].chunks(2))
    {
        // first
        sbox(cs, params.alpha(), state, Some(0..1), params.custom_gate())?;
        state[0].add_assign_constant(round_constant[0][0]);
        mul_by_sparse_matrix(&sparse_matrix[0], state);

        // second
        if round_constant.len() == 2 {
            sbox(cs, params.alpha(), state, Some(0..1), params.custom_gate())?;
            state[0].add_assign_constant(round_constant[1][0]);
            mul_by_sparse_matrix(&sparse_matrix[1], state);
            // reduce gate cost: LC -> Num -> LC
            for state in state.iter_mut() {
                let num = state.clone().into_num(cs).expect("a num");
                *state = LinearCombination::from(num.get_variable());
            }
        }
    }

    sbox(cs, params.alpha(), state, Some(0..1), params.custom_gate())?;
    state[0].add_assign_constant(constants_for_partial_rounds.last().unwrap()[0]);
    mul_by_sparse_matrix(&sparse_matrixes.last().unwrap(), state);

    // second full round
    for round in (params.number_of_partial_rounds() + half_of_full_rounds)
        ..(params.number_of_partial_rounds() + params.number_of_full_rounds())
    {
        let round_constants = &optimized_round_constants[round];

        // add round constatnts
        for (s, c) in state.iter_mut().zip(round_constants.iter()) {
            s.add_assign_constant(*c);
        }

        sbox(
            cs,
            params.alpha(),
            state,
            Some(0..WIDTH),
            params.custom_gate(),
        )?;

        // mul state by mds
        matrix_vector_product(&params.mds_matrix(), state)?;
    }

    Ok(())
}

#[test]
fn test_poseidon_hash_gadget() {
    use rand::{Rand, SeedableRng, XorShiftRng};
    use crate::bellman::{pairing::bn256::{Bn256, Fr}, Field, Engine};
    use circuit::sponge::CircuitGenericSponge;
    use crate::bellman::plonk::better_better_cs::cs::{TrivialAssembly, ConstraintSystem, Width4MainGateWithDNext};
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::poseidon::sponge::generic_hash;

    fn init_cs<E: Engine>() -> TrivialAssembly<E, Width4WithCustomGates, Width4MainGateWithDNext> {
        TrivialAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new()
    }

    fn init_rng() -> XorShiftRng {
        const TEST_SEED: [u32; 4] = [0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654];
        XorShiftRng::from_seed(TEST_SEED)
    }

    fn test_input<E: Engine>() -> ([E::Fr; 2], [Num<E>; 2]) {
        let rng = &mut init_rng();
        let mut input = [E::Fr::zero(); 2];
        let mut input_as_nums = [Num::Constant(E::Fr::zero()); 2];
        for (inp, as_num) in input.iter_mut().zip(input_as_nums.iter_mut()) {
            *inp = E::Fr::rand(rng);
            *as_num = Num::Constant(*inp);
        }
    
        (input, input_as_nums)
    }
    
    fn test_input_circuit<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS) -> ([E::Fr; 2], [Num<E>; 2]) {
        let rng = &mut init_rng();
        let mut input = [E::Fr::zero(); 2];
        let mut input_as_nums = [Num::Constant(E::Fr::zero()); 2];
        for (inp, as_num) in input.iter_mut().zip(input_as_nums.iter_mut()) {
            *inp = E::Fr::rand(rng);
            *as_num = Num::alloc(cs,Some(*inp)).unwrap();
        }
    
        (input, input_as_nums)
    }

    let params = PoseidonParams::<Bn256, 2, 3>::default();
    let (input, _) = test_input::<Bn256>();
    let expected = generic_hash(&params, &input, None);
    println!("Poseidon hash partial round 56 result: {:?}", expected);

    let cs = &mut init_cs();
    let (_, input) = test_input_circuit(cs);
    let hash = CircuitGenericSponge::hash(cs, &input, &params, None).unwrap();
    println!("Poseidon hash partial round 56 circuit result: {:?}", [hash[0].get_value().unwrap(), hash[1].get_value().unwrap()]);
    println!("cs.num_input_gates | cs.num_aux_gates: {} | {}", cs.num_input_gates, cs.num_aux_gates);

    assert!(cs.is_satisfied());
    assert_eq!(hash[0].get_value().unwrap(), expected[0]);
    assert_eq!(hash[1].get_value().unwrap(), expected[1]);
}

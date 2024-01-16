// new test paradigm: using better_cs for witness generation and better_better_cs for actual constraint system
use crate::bellman::pairing::{CurveAffine, CurveProjective, Engine};

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, ScalarEngine};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{ConstraintSystem, Variable};

use crate::bellman::plonk::better_better_cs::cs::PlonkCsWidth4WithNextStepParams as ActualParams;
use crate::bellman::plonk::better_cs::cs::Circuit as OldCircuit;
use crate::bellman::plonk::better_cs::cs::ConstraintSystem as OldConstraintSystem;
use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use crate::bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams as OldActualParams;
use crate::bellman::plonk::better_cs::keys::{
    Proof, SetupPolynomials, SetupPolynomialsPrecomputations, VerificationKey,
};

use crate::bellman::kate_commitment::*;
use crate::bellman::plonk::better_better_cs::cs::{
    Circuit, PlonkCsWidth4WithNextStepParams, TrivialAssembly, Width4MainGateWithDNext,
};
use crate::bellman::plonk::better_cs::generator::GeneratorAssembly as OldAssembly;
use crate::bellman::plonk::better_cs::generator::GeneratorAssembly4WithNextStep as OldActualAssembly;
use crate::bellman::plonk::better_cs::prover::ProverAssembly as OldProver;
use crate::bellman::plonk::better_cs::prover::ProverAssembly4WithNextStep as OldActualProver;
use crate::bellman::plonk::better_cs::verifier::verify;
use crate::bellman::plonk::commitments::transcript::*;
use crate::bellman::plonk::fft::cooley_tukey_ntt::*;
use crate::bellman::worker::*;
use bellman::plonk::better_better_cs::cs::{
    ensure_in_map_or_create, get_from_map_unchecked, ArithmeticTerm, Gate, GateInternal, MainGate,
    MainGateTerm, PolyIdentifier,
};
use bellman::plonk::better_better_cs::data_structures::{
    AssembledPolynomialStorage, AssembledPolynomialStorageForMonomialForms, PolynomialInConstraint,
};
use bellman::plonk::better_better_cs::lookup_tables::LookupTableApplication;
use bellman::plonk::polynomials::{Coefficients, Polynomial, Values};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct TestCircuit4<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: Engine> Circuit<E> for TestCircuit4<E> {
    type MainGate = Width4MainGateWithDNext;

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| Ok(E::Fr::from_str("10").unwrap()))?;

        println!("A = {:?}", a);

        let b = cs.alloc(|| Ok(E::Fr::from_str("20").unwrap()))?;

        println!("B = {:?}", b);

        let c = cs.alloc(|| Ok(E::Fr::from_str("200").unwrap()))?;

        println!("C = {:?}", c);

        let d = cs.alloc(|| Ok(E::Fr::from_str("100").unwrap()))?;

        println!("D = {:?}", d);

        let one = E::Fr::one();

        let mut two = one;
        two.double();

        let mut negative_one = one;
        negative_one.negate();

        // 2a - b = 0
        let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
        let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
        let mut term = MainGateTerm::new();
        term.add_assign(two_a);
        term.add_assign(minus_b);

        cs.allocate_main_gate(term)?;

        // c - a*b == 0
        let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
        ab_term.scale(&negative_one);
        let c_term = ArithmeticTerm::from_variable(c);
        let mut term = MainGateTerm::new();
        term.add_assign(c_term);
        term.add_assign(ab_term);

        cs.allocate_main_gate(term)?;

        // d - 100 == 0
        let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
        let d_term = ArithmeticTerm::from_variable(d);
        let mut term = MainGateTerm::new();
        term.add_assign(d_term);
        term.sub_assign(hundred);

        cs.allocate_main_gate(term)?;

        let gamma = cs.alloc(|| Ok(E::Fr::from_str("20").unwrap()))?;

        // gamma - b == 0
        let gamma_term = ArithmeticTerm::from_variable(gamma);
        let b_term = ArithmeticTerm::from_variable(b);
        let mut term = MainGateTerm::new();
        term.add_assign(gamma_term);
        term.sub_assign(b_term);

        cs.allocate_main_gate(term)?;

        // 2a
        let mut term = MainGateTerm::<E>::new();
        term.add_assign(ArithmeticTerm::from_variable_and_coeff(a, two));

        let dummy = CS::get_dummy_variable();

        // 2a - d_next = 0

        let (vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
        *coeffs.last_mut().unwrap() = negative_one;

        // here d is equal = 2a, so we need to place b there
        // and compensate it with -b somewhere before

        cs.new_single_gate_for_trace_step(&CS::MainGate::default(), &coeffs, &vars, &[])?;

        let mut term = MainGateTerm::<E>::new();
        term.add_assign(ArithmeticTerm::from_variable(b));

        // b + 0 + 0 - b = 0
        let (mut vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
        coeffs[3] = negative_one;
        vars[3] = b;

        cs.new_single_gate_for_trace_step(&CS::MainGate::default(), &coeffs, &vars, &[])?;

        Ok(())
    }
}

mod test {
    use super::*;

    use crate::bellman::pairing::{CurveAffine, CurveProjective, Engine};

    use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, ScalarEngine};

    use crate::bellman::SynthesisError;

    use crate::bellman::plonk::better_better_cs::cs::Variable;

    use crate::bellman::plonk::better_better_cs::cs::Circuit;
    use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
    use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams;
    use crate::bellman::plonk::better_better_cs::cs::PlonkCsWidth4WithNextStepParams;
    use crate::bellman::plonk::better_better_cs::cs::{
        ProvingAssembly, SetupAssembly, TrivialAssembly, Width4MainGateWithDNext,
    };
    use crate::bellman::plonk::better_better_cs::verifier::verify;
    use crate::bellman::plonk::better_better_cs::{proof::Proof, setup::VerificationKey};

    use crate::bellman::kate_commitment::*;
    use crate::bellman::plonk::commitments::transcript::*;
    use crate::bellman::plonk::fft::cooley_tukey_ntt::*;
    use crate::bellman::worker::*;

    use super::super::affine_point_wrapper::aux_data::*;
    use super::super::affine_point_wrapper::*;
    use super::super::channel::*;
    use super::super::new_data_structs::*;
    use super::super::new_verifying_circuit::*;
    use crate::bellman::pairing::bn256::{Bn256, Fr};
    use crate::bellman::plonk::commitments::transcript::Transcript;
    use crate::plonk::circuit::bigint::field::*;
    use crate::plonk::circuit::curve::sw_affine::*;
    use crate::plonk::circuit::rescue::*;
    use crate::rescue::bn256::Bn256RescueParams;
    use crate::rescue::rescue_transcript::RescueTranscriptForRNS;
    use crate::rescue::RescueEngine;

    // use plonk::circuit::verifier_circuit::poseidon_constant::PoseidonHashParams;
    // use super::super::poseidon::PoseidonTranscript;
    // use super::super::poseidon_channel::PoseidonChannelGadget;
    use crate::plonk::circuit::verifier_circuit::affine_point_wrapper::without_flag_unchecked::WrapperUnchecked;
    use bellman::plonk::domains::Domain;
    use plonk::circuit::generate_vk::{generate_vk_solidity, print_proof, print_verification_key};
    use std::fs::File;
    use std::marker::PhantomData;

    pub fn recursion_test<'a, E, T, CG, AD, WP>(
        a: E::Fr,
        b: E::Fr,
        num_steps: usize,
        channel_params: &'a CG::Params,
        rns_params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        transcript_params: <T as Prng<E::Fr>>::InitializationParameters,
    ) where
        E: Engine,
        T: Transcript<E::Fr>,
        CG: ChannelGadget<E>,
        AD: AuxData<E>,
        WP: WrappedAffinePoint<'a, E>,
    {
        use crate::plonk::circuit::*;

        let mut assembly =
            SetupAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = TestCircuit4::<E> {
            _marker: PhantomData,
        };

        circuit.synthesize(&mut assembly).expect("must work");

        println!("Assembly contains {} gates", assembly.n());
        assert!(assembly.is_satisfied());

        assembly.finalize();

        println!("Finalized assembly contains {} gates", assembly.n());

        let worker = Worker::new();

        let setup = assembly.create_setup::<TestCircuit4<E>>(&worker).unwrap();

        let mut assembly =
            ProvingAssembly::<E, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();
        circuit.synthesize(&mut assembly).expect("must work");
        assembly.finalize();

        let size = assembly.n().next_power_of_two();

        let crs_mons = Crs::<E, CrsForMonomialForm>::crs_42(size, &worker);

        let proof = assembly
            .create_proof::<TestCircuit4<E>, T>(
                &worker,
                &setup,
                &crs_mons,
                Some(transcript_params.clone()),
            )
            .unwrap();

        let verification_key = VerificationKey::from_setup(&setup, &worker, &crs_mons).unwrap();

        let valid = verify::<E, TestCircuit4<E>, T>(
            &verification_key,
            &proof,
            Some(transcript_params.clone()),
        )
        .unwrap();

        dbg!(valid);
        println!("PROOF IS VALID");

        let buffer = File::open("./new_proof.proof").unwrap();
        let proof = Proof::<E, TestCircuit4<E>>::read(&buffer).unwrap();
        let buffer = File::open("./verify_key.key").unwrap();
        let verification_key = VerificationKey::<E, TestCircuit4<E>>::read(&buffer).unwrap();

        let mut g2_bases = [E::G2Affine::zero(); 2];
        g2_bases.copy_from_slice(&crs_mons.g2_monomial_bases.as_ref()[..]);

        //RecursiveCircuit setup , prove , verify
        let mut assembly =
            SetupAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();

        let recursive_circuit =
            PlonkVerifierCircuit::<E, CG, Width4WithCustomGates, TestCircuit4<E>, AD, WP>::new(
                channel_params,
                vec![],
                vec![],
                proof.clone(),
                verification_key.clone(),
                AD::new(),
                rns_params,
                g2_bases,
            );

        recursive_circuit
            .synthesize(&mut assembly)
            .expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        assert!(assembly.is_satisfied());
        assembly.finalize();
        println!("Finalized assembly contains {} gates", assembly.n());

        let circuit =
            PlonkVerifierCircuit::<E, CG, Width4WithCustomGates, TestCircuit4<E>, AD, WP>::new(
                channel_params,
                vec![],
                vec![],
                proof,
                verification_key,
                AD::new(),
                rns_params,
                g2_bases,
            );

        let worker = Worker::new();
        let setup = assembly.create_setup::<PlonkVerifierCircuit<E,CG, Width4WithCustomGates,TestCircuit4<E>, AD, WP>>(&worker).unwrap();

        let mut assembly =
            ProvingAssembly::<E, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        circuit.synthesize(&mut assembly).expect("must work");
        assembly.finalize();

        let size = assembly.n().next_power_of_two();

        let crs_mons = Crs::<E, CrsForMonomialForm>::crs_42(size, &worker);

        let proof = assembly.create_proof::<PlonkVerifierCircuit<E,CG, Width4WithCustomGates,TestCircuit4<E>, AD, WP>, T>(
            &worker,
            &setup,
            &crs_mons,
            Some(transcript_params.clone())
        ).unwrap();

        let vk = VerificationKey::from_setup(&setup, &worker, &crs_mons).unwrap();

        let domain = Domain::<E::Fr>::new_for_size(vk.n as u64).unwrap();
        println!("new_vk.omega:{}", domain.generator);

        print_verification_key(&vk);
        print_proof(&proof);
        generate_vk_solidity(&vk, "bbc_recursive_vk");

        let valid = verify::<
            E,
            PlonkVerifierCircuit<E, CG, Width4WithCustomGates, TestCircuit4<E>, AD, WP>,
            T,
        >(&vk, &proof, Some(transcript_params))
        .unwrap();

        assert!(valid);

        let mut buffer = File::create("./new_proof.proof").unwrap();
        proof.write(&mut buffer).unwrap();
        let mut buffer = File::create("./verify_key.key").unwrap();
        vk.write(&mut buffer).unwrap();
    }

    #[test]
    fn bn256_recursion_test() {
        let a = <Bn256 as ScalarEngine>::Fr::one();
        let b = <Bn256 as ScalarEngine>::Fr::one();
        let num_steps = 100;

        let rns_params = RnsParameters::<Bn256, <Bn256 as Engine>::Fq>::new_for_field(68, 110, 4);
        let rescue_params = Bn256RescueParams::new_checked_2_into_1();
        // let poseidon_params = super::super::poseidon_constant::Bn256PoseidonParams::new();

        let transcript_params = (&rescue_params, &rns_params);

        recursion_test::<
            Bn256,
            RescueTranscriptForRNS<Bn256>,
            RescueChannelGadget<Bn256>,
            BN256AuxData,
            WrapperUnchecked<Bn256>,
        >(
            a,
            b,
            num_steps,
            &rescue_params,
            &rns_params,
            transcript_params,
        );
    }
}

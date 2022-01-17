#[cfg(test)]
mod test {
    use std::sync::Arc;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::pairing::ff::*;
    use crate::bellman::SynthesisError;
    use crate::bellman::Engine;
    use crate::plonk::circuit::allocated_num::{
        AllocatedNum,
        Num,
    };
    use crate::plonk::circuit::byte::{
        Byte,
    };
    use crate::bellman::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use super::super::utils::*;
    use super::super::hasher::*;
    use crate::plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
    use rand::{Rng, SeedableRng, StdRng};
    use std::convert::TryInto;


    struct TestReinforcementConcreteCircuit<E:Engine>{
        input: [E::Fr; RC_STATE_WIDTH],
        output: [E::Fr; RC_STATE_WIDTH],
        elems_to_absorb: [E::Fr; RC_RATE],
        params: Arc<ReinforcedConcreteParams<E::Fr>>,
        is_const_test: bool,
    }

    impl<E: Engine> Circuit<E> for TestReinforcementConcreteCircuit<E>
    {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> { 
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                    Rescue5CustomGate::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {

            let mut actual_output_vars = Vec::with_capacity(RC_STATE_WIDTH);
            for value in self.output.iter() {
                if !self.is_const_test {
                    let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                    actual_output_vars.push(Num::Variable(new_var));
                }
                else {
                    actual_output_vars.push(Num::Constant(value.clone()));
                }
            }

            let alphas : [E::Fr; 2] = {
                self.params.alphas.iter().map(|x| from_u64::<E::Fr>(*x as u64))
                .collect::<Vec<_>>().try_into().unwrap()
            };
            let betas = self.params.betas.clone();
            let s_arr = self.params.si.clone();
            let p_prime = self.params.sbox.len() as u16;
            let perm_f = |x: u16| -> u16 {
                self.params.sbox[x as usize]
            };

            let rc_gadget = ReinforcementConcreteGadget::new(
                cs, alphas, betas, p_prime, s_arr, perm_f, false
            )?;

            let supposed_output_vars = {    
                let mut input_vars = Vec::with_capacity(self.input.len());
                for value in self.input.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        input_vars.push(Num::Variable(new_var));
                    }
                    else {
                        input_vars.push(Num::Constant(value.clone()));
                    }
                }

                let mut values_to_absorb = Vec::with_capacity(self.elems_to_absorb.len());
                for value in self.elems_to_absorb.iter() {
                    if !self.is_const_test {
                        let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                        values_to_absorb.push(Num::Variable(new_var));
                    }
                    else {
                        values_to_absorb.push(Num::Constant(value.clone()));
                    }
                }

                rc_gadget.reset(Some(&input_vars[..]));
                rc_gadget.absorb(cs, &values_to_absorb[..])?;
                rc_gadget.get_cur_state()
            };
           
            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                a.enforce_equal(cs, &b)?;
            }

            Ok(())
        }
    }

    fn rc_gadget_test_template<E: Engine>() 
    {
        let seed: &[_] = &[1, 2, 3, 4, 5];
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let mut input = [E::Fr::zero(); RC_STATE_WIDTH];
        for i in 0..RC_STATE_WIDTH {
            input[i] = rng.gen();
        }

        let params = E::get_default_rc_params();
        let mut hasher = ReinforcedConcrete::<E::Fr>::new(&params);
        // write input message
        hasher.update(&input[0..55]);
        // read hash digest and consume hasher
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: false,
            is_byte_test: false,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }

    #[test]
    fn rc_gadget_const_propagation_test() 
    {
        const NUM_OF_BLOCKS: usize = 3;
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 64 * NUM_OF_BLOCKS];
        for i in 0..(64 * (NUM_OF_BLOCKS-1) + 55) {
            input[i] = rng.gen();
        }
        input[64 * (NUM_OF_BLOCKS-1) + 55] = 0b10000000;
        
        let total_number_of_bits = (64 * (NUM_OF_BLOCKS-1) + 55) * 8;
        input[64 * (NUM_OF_BLOCKS-1) + 60] = (total_number_of_bits >> 24) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 61] = (total_number_of_bits >> 16) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 62] = (total_number_of_bits >> 8) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 63] = total_number_of_bits as u8;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.update(&input[0..(64 * (NUM_OF_BLOCKS-1) + 55)]);
        // read hash digest and consume hasher
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16 * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); 8];

        for block in input.chunks(4) {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            ch_base_num_of_chunks: None,
            maj_sheduler_base_num_of_chunks: None,
            is_const_test: true,
            is_byte_test: false,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}
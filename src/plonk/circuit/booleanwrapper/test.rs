#[cfg(test)]
mod test{
    use crate::plonk::circuit::boolean::{AllocatedBit, Boolean};
    use crate::bellman::pairing::Engine;
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::SynthesisError;
    use crate::bellman::plonk::better_better_cs::cs::{TrivialAssembly, Width4MainGateWithDNext};
    use crate::bellman::pairing::{bn256::Bn256};
    use super::super::base::*;
    #[test]
    fn test_1(){
        //with the usual call of the same methods with the same variables, two constraints are formed
        struct TestCircuit{
            value_1: Option<bool>,
            value_2: Option<bool>,
            value_3: Option<bool>,
            value_4: Option<bool>,
        }
        impl<E: Engine> Circuit<E> for TestCircuit{
            type MainGate = Width4MainGateWithDNext;
    
            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
                Ok(
                    vec![
                        Width4MainGateWithDNext::default().into_internal(),
                    ]
                )
            }
    
            fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let value_1 = AllocatedBit::alloc(cs, self.value_1).unwrap();
                let value_2 = AllocatedBit::alloc(cs, self.value_2).unwrap();
                let value_3 = AllocatedBit::alloc(cs, self.value_3).unwrap();
                let value_4 = AllocatedBit::alloc(cs, self.value_4).unwrap();
    
                let _experiment_1 = Boolean::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));
                let _experiment_2 = Boolean::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));

                let _experiment_3 = Boolean::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));
                let _experiment_4 = Boolean::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));

                let _experiment_5 = Boolean::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));
                let _experiment_6 = Boolean::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));

                let _experiment_7 = Boolean::conditionally_select(cs, &Boolean::Is(value_1), &Boolean::Is(value_2), &Boolean::Is(value_4));
                let _experiment_8 = Boolean::conditionally_select(cs, &Boolean::Is(value_1), &Boolean::Is(value_2), &Boolean::Is(value_4));
    
                Ok(())
            }
        } 
        
        let circuit = TestCircuit{
            value_1: Some(true),
            value_2: Some(true),
            value_3: Some(false),
            value_4: Some(false),
    
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            circuit.synthesize(&mut assembly).expect("must work");
            println!("Number of constraints without optimization");
            println!("Assembly contains {} gates", assembly.n());
            println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
            assert!(assembly.is_satisfied());
    }


    #[test]
    fn test_2(){
        //The test shows the number of constants with optimization
        struct TestCircuit{
            value_1: Option<bool>,
            value_2: Option<bool>,
            value_3: Option<bool>,
            value_4: Option<bool>,
        }
        impl<E: Engine> Circuit<E> for TestCircuit{
            type MainGate = Width4MainGateWithDNext;
    
            fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
                Ok(
                    vec![
                        Width4MainGateWithDNext::default().into_internal(),
                    ]
                )
            }
    
            fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
                let value_1 = AllocatedBit::alloc(cs, self.value_1).unwrap();
                let value_2 = AllocatedBit::alloc(cs, self.value_2).unwrap();
                let value_3 = AllocatedBit::alloc(cs, self.value_3).unwrap();
                let value_4 = AllocatedBit::alloc(cs, self.value_4).unwrap();
    
                let _experiment_1 = BooleanWrapper::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));
                let _experiment_2 = BooleanWrapper::xor(cs, &Boolean::Is(value_1), &Boolean::Is(value_2));

                let _experiment_3 = BooleanWrapper::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));
                let _experiment_4 = BooleanWrapper::or(cs, &Boolean::Is(value_3), &Boolean::Is(value_4));

                let _experiment_5 = BooleanWrapper::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));
                let _experiment_6 = BooleanWrapper::and(cs, &Boolean::Not(value_2), &Boolean::Is(value_4));

                let _experiment_7 = BooleanWrapper::conditionally_select(cs, &Boolean::Is(value_1), &Boolean::Is(value_2), &Boolean::Is(value_4));
                let _experiment_8 = BooleanWrapper::conditionally_select(cs, &Boolean::Is(value_1), &Boolean::Is(value_2), &Boolean::Is(value_4));
    
                Ok(())
            }
        } 
        
        let circuit = TestCircuit{
            value_1: Some(true),
            value_2: Some(true),
            value_3: Some(false),
            value_4: Some(false),
    
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

            circuit.synthesize(&mut assembly).expect("must work");
            println!("Number of constraints with optimization");
            println!("Assembly contains {} gates", assembly.n());
            println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
            assert!(assembly.is_satisfied());
    }
}

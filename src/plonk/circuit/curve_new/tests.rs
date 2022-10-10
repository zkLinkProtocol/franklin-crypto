#[cfg(test)]
mod test {
    use crate::bellman::pairing::bn256;
    use crate::bellman::{Field, PrimeField, GenericCurveAffine, GenericCurveProjective};
    use plonk::circuit::Width4WithCustomGates;
    use bellman::plonk::better_better_cs::gates::{
        selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self
    };
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;
    use crate::plonk::circuit::bigint_new::*;
    use crate::plonk::circuit::curve_new::*;

    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;
    use crate::bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
    use crate::bellman::plonk::better_better_cs::setup::VerificationKey;
    use crate::bellman::plonk::better_better_cs::verifier::verify;

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    #[test]
    fn test_generic_projective_double_add_for_bn256() {
        let mut cs = TrivialAssembly::<
            bn256::Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = generate_optimal_circuit_params_for_bn256::<bn256::Bn256, _>(&mut cs, 80usize, 80usize);
        let mut rng = rand::thread_rng();

        let mut a = bn256::G1::zero();
        let mut b = bn256::G1::zero();
        for out in std::iter::once(&mut a).chain(std::iter::once(&mut b)) { 
            let affine_point: bn256::G1Affine = rng.gen();
            let (mut x, mut y) = GenericCurveAffine::into_xy_unchecked(affine_point);
            let z : bn256::Fq = rng.gen();
            x.mul_assign(&z);
            y.mul_assign(&z);
            
            let proj_point = bn256::G1::from_xyz_unchecked(x, y, z);
            *out = proj_point;
        }
        let mut result = a.clone();
        result.double(); 
        //result.add_assign(&b);
        println!("a: {}", a);
        println!("a doubled: {}", result);

        println!("AAA");
        let a = ProjectivePoint::alloc(&mut cs, Some(a), &params).unwrap();
        println!("AAAB");
        // let mut b = ProjectivePoint::alloc(&mut cs, Some(b), &params).unwrap();
        let mut actual_result = ProjectivePoint::alloc(&mut cs, Some(result), &params).unwrap();
        println!("AAAC");
        
        let counter_start = cs.get_current_step_number();
        let mut result = ProjectivePoint::double(&a, &mut cs).unwrap(); 
        println!("real x: {}", result.get_x().get_field_value().unwrap());
        println!("real y: {}", result.get_y().get_field_value().unwrap());
        println!("real z: {}", result.get_z().get_field_value().unwrap());

        println!("real x: {}", actual_result.get_x().get_field_value().unwrap());
        println!("real y: {}", actual_result.get_y().get_field_value().unwrap());
        println!("real z: {}", actual_result.get_z().get_field_value().unwrap());
        //let mut result = a.clone();
        // result = result.add(&mut cs, &mut b).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);

        ProjectivePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
        assert!(cs.is_satisfied()); 
    }

    #[test]
    fn test_generic_affine_extended_double_add_for_bn256() {
        use self::bn256::{Bn256, G1, G1Affine, Fq};

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
        let rns_params = &params.base_field_rns_params;

        let a_x_c0 = "11947046220310406338075336430452637192462772637241719407011734688739628070508";
        let a_x_c1 = "10557742219851096102260847081504953836102098067687282141689259525204118168143";
        let a_y_c0 = "15601064320065192494908094207408122343972055839928949425916220757362334086123";
        let a_y_c1 = "8529668414453473015102015524644323833697434755595850489456056849073813231365";
        let a_coefs = [&a_x_c0, &a_x_c1, &a_y_c0, &a_y_c1];

        let b_x_c0 = "220307984863270321646848220250400852276700881024772566232775081293241238563";
        let b_x_c1 = "1268657104210478535811095545301172618324930929631779260627009638542643809713";
        let b_y_c0 = "14716094244763148080513574234943212664563830050269302711516770265264441206811";
        let b_y_c1 = "1767762926323305702692527140415867669545860126912362251081259289072812848508";
        let b_coefs = [&b_x_c0, &b_x_c1, &b_y_c0, &b_y_c1];

        let c_x_c0 = "14502852985533014211323301556586986708073645991817525233238442508152308472745";
        let c_x_c1 = "3731688454144978548314047313025143811107288207224347116507836166136690390974";
        let c_y_c0 = "3341290380766155696716470666946884673121015452733721707932930112416013276659";
        let c_y_c1 = "5650743550923202600541315224154807569595826295523387795464783550769874508672";
        let c_coefs = [&c_x_c0, &c_x_c1, &c_y_c0, &c_y_c1];

        let mut a = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
        let mut b = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
        let mut c = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(rns_params);
                
        let iter = std::iter::once(&mut a).chain(std::iter::once(&mut b)).chain(std::iter::once(&mut c)).zip(
            std::iter::once(&a_coefs).chain(std::iter::once(&b_coefs)).chain(std::iter::once(&c_coefs))
        );

        for (out, coeffs) in iter  { 
            let x_c0 = Fq::from_str(coeffs[0]);
            let x_c1 = Fq::from_str(coeffs[1]);
            let y_c0 = Fq::from_str(coeffs[2]);
            let y_c1 = Fq::from_str(coeffs[3]);
            let point = AffinePointExt::alloc(&mut cs, x_c0, x_c1, y_c0, y_c1, rns_params).unwrap();
            *out = point;
        }

        let counter_start = cs.get_current_step_number();
        let mut result = a.double_and_add_unchecked(&mut cs, &mut b).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);

        AffinePointExt::enforce_equal(&mut cs, &mut result, &mut c).unwrap();
        assert!(cs.is_satisfied()); 
    }
}

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // test correctness of basic arithmetic operations of a curve: add, sub, double, double_add
//     struct AffinePointTester<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
//     where <G as GenericCurveAffine>::Base: PrimeField
//     {
//         circuit_params: CurveCircuitParameters<E, G, T>,
//     }

//     impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for AffinePointTester<E, G, T> 
//     where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
//     {
//         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
//             )
//         }
    
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let mut rng = rand::thread_rng();

//             let a: G1Affine = rng.gen();
//             let b: G1Affine = rng.gen();
            
//             let mut tmp = bellman::CurveAffine::into_projective(&a);
//             tmp.add_assign_mixed(&b);
//             let a_plus_b_actual = tmp.into_affine();

//             let mut tmp = bellman::CurveAffine::into_projective(&a);
//             tmp.sub_assign_mixed(&b);
//             let a_sub_b_actual = tmp.into_affine();

//             let mut a_doubled_actual = a.clone();
//             a_doubled_actual.double();
            
        
//         let a = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
//         let mut b = AffinePoint::alloc(&mut cs, Some(b), &params).unwrap();
//         let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
//         let naive_mul_start = cs.get_current_step_number();
//         let mut result = a.add_unequal_unchecked(&mut cs, &mut b).unwrap();
//         let naive_mul_end = cs.get_current_step_number();
//         println!("num of gates: {}", naive_mul_end - naive_mul_start);

//         // println!("actual result: x: {}, y: {}", actual_result.x.get_field_value().unwrap(), actual_result.y.get_field_value().unwrap());
//         // println!("computed result: x: {}, y: {}", result.x.get_field_value().unwrap(), result.y.get_field_value().unwrap());

//         AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
//         assert!(cs.is_satisfied()); 
//         println!("SCALAR MULTIPLICATION final");
//     }



//     struct AffineExt_vs_Projective<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
//     where <G as GenericCurveAffine>::Base: PrimeField
//     {
//         circuit_params: CurveCircuitParameters<E, G, T>,
//     }
    
//     impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for AffineExt_vs_Projective<E, G, T> 
//     where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
//     {
//         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
//             )
//         }
    
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let mut rng = rand::thread_rng();

//             let a: G = rng.gen();
//             let b: G = rng.gen();
//             let mut b_negated = b;
//             b_megated.negate();
    
//             let mut tmp = a.into_projective();
//         b.negate();
//         tmp.add_assign_mixed(&b);
//         let result = tmp.into_affine();
//         b.negate();

//         // testing a + b, 2 * a, a - b, mixed_add
        
//         let a_affine = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
//         let a_proj = ProjectivePoint::from(a_affine);
//         let b_affine = AffinePoint::alloc(&mut cs, Some(b), &params).unwrap();
//         let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
//         let naive_mul_start = cs.get_current_step_number();
//         let result = a_proj.sub_mixed(&mut cs, &b_affine).unwrap();
//         let naive_mul_end = cs.get_current_step_number();
//         println!("num of gates: {}", naive_mul_end - naive_mul_start);

//         let mut result = unsafe { result.convert_to_affine(&mut cs).unwrap() };
//         AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
//         assert!(cs.is_satisfied()); 
            

//             let mut result_wit_proj = G::Projective::zero();
//             for _ in 0..self.num_of_points {
//                 let scalar_wit : G::Scalar = rng.gen();
//                 let point_wit : G = rng.gen();

//                 let mut tmp = point_wit.into_projective();
//                 tmp.mul_assign(scalar_wit);
//                 result_wit_proj.add_assign(&tmp);

//                 let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
//                 let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;

//                 points.push(point);
//                 scalars.push(scalar);
//             }

//             let result_wit = result_wit_proj.into_affine();
//             println!("ACTUAL VALUE: {}", result_wit);
//             let mut actual_result = AffinePoint::alloc(cs, Some(result_wit), &self.circuit_params)?;
           

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = AffinePoint::safe_multiexp_affine(cs, &scalars, &points)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for affine multiexp var1: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             // let naive_mul_start = cs.get_current_step_number();
//             // let mut result = AffinePoint::safe_multiexp_affine2(cs, &scalars, &points)?;
//             // let naive_mul_end = cs.get_current_step_number();
//             // println!("num of gates for affine multiexp var2: {}", naive_mul_end - naive_mul_start);
//             // AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = AffinePoint::safe_multiexp_affine3(cs, &scalars, &points)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for affine multiexp var3: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             // let naive_mul_start = cs.get_current_step_number();
//             // let mut result = AffinePoint::safe_multiexp_affine4(cs, &scalars, &points)?;
//             // let naive_mul_end = cs.get_current_step_number();
//             // println!("num of gates for affine multiexp var4: {}", naive_mul_end - naive_mul_start);
//             // AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;


//             let naive_mul_start = cs.get_current_step_number();
//             let result = AffinePoint::safe_multiexp_projective(cs, &scalars, &points)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for proj multiexp: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             Ok(())
//         }
//     }

//     #[test]
//     fn test_arithmetic_for_projective_bn256_curve() {
//         let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
//         inscribe_default_bitop_range_table(&mut cs).unwrap();
//         let params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, 80usize, 80usize);
//         let mut rng = rand::thread_rng();

//         let a: G1Affine = rng.gen();
//         let mut b: G1Affine = rng.gen();
//         let mut tmp = a.into_projective();
//         b.negate();
//         tmp.add_assign_mixed(&b);
//         let result = tmp.into_affine();
//         b.negate();
        
//         let a_affine = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
//         let a_proj = ProjectivePoint::from(a_affine);
//         let b_affine = AffinePoint::alloc(&mut cs, Some(b), &params).unwrap();
//         let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
//         let naive_mul_start = cs.get_current_step_number();
//         let result = a_proj.sub_mixed(&mut cs, &b_affine).unwrap();
//         let naive_mul_end = cs.get_current_step_number();
//         println!("num of gates: {}", naive_mul_end - naive_mul_start);

//         let mut result = unsafe { result.convert_to_affine(&mut cs).unwrap() };
//         AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
//         assert!(cs.is_satisfied()); 
//     }

//     struct TestCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
//     where <G as GenericCurveAffine>::Base: PrimeField
//     {
//         circuit_params: CurveCircuitParameters<E, G, T>
//     }
    
//     impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestCircuit<E, G, T> 
//     where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
//     {
//         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
//             )
//         }
    
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let mut rng = rand::thread_rng();
//             let a: G = rng.gen();
//             let scalar : G::Scalar = rng.gen();
//             let mut tmp = a.into_projective();
//             tmp.mul_assign(scalar);
//             let result = tmp.into_affine();
            
//             let mut a = AffinePoint::alloc(cs, Some(a), &self.circuit_params)?;
//             let mut scalar = FieldElement::alloc(cs, Some(scalar), &self.circuit_params.scalar_field_rns_params)?;
//             let mut actual_result = AffinePoint::alloc(cs, Some(result), &self.circuit_params)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.mul_by_scalar_descending_ladder(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending ladder: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.mul_by_scalar_descending_skew_ladder(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending skew ladder: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.mul_by_scalar_descending_skew_ladder_with_endo(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending skew ladder with_endo: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.mul_by_scalar_descending_skew_ladder_with_base_ext(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending skew ladder with base ext: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.mul_by_scalar_descending_skew_ladder_with_endo_and_base_ext(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!(
//                 "num of gates for descending skew ladder with endo and base ext: {}", naive_mul_end - naive_mul_start
//             );
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = a.test_selector_tree(cs, &mut scalar)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!(
//                 "num of gates for descending skew ladder with endo and base ext (via tree selector): {}", naive_mul_end - naive_mul_start
//             );
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            
//             let naive_mul_start = cs.get_current_step_number();
//             let result = a.mul_by_scalar_ascending_ladder_proj(cs, &mut scalar)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for ascending ladder proj: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let result = a.mul_by_scalar_ascending_skew_ladder_proj(cs, &mut scalar)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for ascending skew ladder proj: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let result = a.mul_by_scalar_descending_skew_ladder_proj(cs, &mut scalar)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending skew ladder proj: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let result = a.mul_by_scalar_descending_skew_ladder_with_endo_proj(cs, &mut scalar)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for descending skew ladder with endo proj: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             Ok(())
//         }
//     }

//     #[test]
//     fn test_scalar_multiplication_for_bn256() {
//         const LIMB_SIZE: usize = 80;

//         let mut cs = TrivialAssembly::<
//             Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
//         >::new();
//         inscribe_default_bitop_range_table(&mut cs).unwrap();
//         let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

//         let circuit = TestCircuit { circuit_params };
//         circuit.synthesize(&mut cs).expect("must work");
//         cs.finalize();
//         assert!(cs.is_satisfied()); 
//     }

//     struct TestMultiexpCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
//     where <G as GenericCurveAffine>::Base: PrimeField
//     {
//         circuit_params: CurveCircuitParameters<E, G, T>,
//         num_of_points: usize
//     }
    
//     impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestMultiexpCircuit<E, G, T> 
//     where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
//     {
//         type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
//         fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
//             Ok(
//                 vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
//             )
//         }
    
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let mut rng = rand::thread_rng();
//             let mut points = Vec::with_capacity(self.num_of_points);
//             let mut scalars = Vec::with_capacity(self.num_of_points);

//             let mut result_wit_proj = G::Projective::zero();
//             for _ in 0..self.num_of_points {
//                 let scalar_wit : G::Scalar = rng.gen();
//                 let point_wit : G = rng.gen();

//                 let mut tmp = point_wit.into_projective();
//                 tmp.mul_assign(scalar_wit);
//                 result_wit_proj.add_assign(&tmp);

//                 let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
//                 let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;

//                 points.push(point);
//                 scalars.push(scalar);
//             }

//             let result_wit = result_wit_proj.into_affine();
//             println!("ACTUAL VALUE: {}", result_wit);
//             let mut actual_result = AffinePoint::alloc(cs, Some(result_wit), &self.circuit_params)?;
           

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = AffinePoint::safe_multiexp_affine(cs, &scalars, &points)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for affine multiexp var1: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             // let naive_mul_start = cs.get_current_step_number();
//             // let mut result = AffinePoint::safe_multiexp_affine2(cs, &scalars, &points)?;
//             // let naive_mul_end = cs.get_current_step_number();
//             // println!("num of gates for affine multiexp var2: {}", naive_mul_end - naive_mul_start);
//             // AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             let naive_mul_start = cs.get_current_step_number();
//             let mut result = AffinePoint::safe_multiexp_affine3(cs, &scalars, &points)?;
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for affine multiexp var3: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             // let naive_mul_start = cs.get_current_step_number();
//             // let mut result = AffinePoint::safe_multiexp_affine4(cs, &scalars, &points)?;
//             // let naive_mul_end = cs.get_current_step_number();
//             // println!("num of gates for affine multiexp var4: {}", naive_mul_end - naive_mul_start);
//             // AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;


//             let naive_mul_start = cs.get_current_step_number();
//             let result = AffinePoint::safe_multiexp_projective(cs, &scalars, &points)?;
//             let mut result = unsafe { result.convert_to_affine(cs)? };
//             let naive_mul_end = cs.get_current_step_number();
//             println!("num of gates for proj multiexp: {}", naive_mul_end - naive_mul_start);
//             AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

//             Ok(())
//         }
//     }

//     #[test]
//     fn test_multiexp_scalar_multiplication_for_bn256() {
//         const LIMB_SIZE: usize = 80;
//         const NUM_OF_POINTS: usize = 3;

//         let mut cs = TrivialAssembly::<
//             Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
//         >::new();
//         inscribe_default_bitop_range_table(&mut cs).unwrap();
//         let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

//         let circuit = TestMultiexpCircuit { circuit_params, num_of_points: NUM_OF_POINTS };
//         circuit.synthesize(&mut cs).expect("must work");
//         cs.finalize();
//         assert!(cs.is_satisfied()); 
//     }
// }
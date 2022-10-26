#[cfg(test)]
mod test {
    use crate::bellman::pairing::bn256;
    use crate::bellman::{Field, PrimeField, GenericCurveAffine, GenericCurveProjective};
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::plonk::circuit::Engine;
    use crate::plonk::circuit::SynthesisError;
    use bellman::plonk::better_better_cs::gates::{
        selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self
    };
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;
    use crate::plonk::circuit::bigint::*;
    use crate::plonk::circuit::curve::*;

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
        let rns_params = &params.base_field_rns_params;
        let mut rng = rand::thread_rng();

        let a_affine: bn256::G1Affine = rng.gen();
        let b_affine: bn256::G1Affine = rng.gen();
        let mut result = a_affine.into_projective();
        result.double(); 
        result.add_assign_mixed(&b_affine);
        let mut actual_result = ProjectivePoint::from(
            AffinePoint::alloc(&mut cs, Some(result.into_affine()), &params).unwrap()
        );

        let mut a = ProjectivePoint::zero(&params);
        let mut b = ProjectivePoint::zero(&params);

        let iter = std::iter::once((&a_affine, &mut a)).chain(std::iter::once((&b_affine, &mut b))); 
        for (affine_point, out) in iter { 
            let (mut x_wit, mut y_wit) = affine_point.into_xy_unchecked();
            let z_wit : bn256::Fq = rng.gen();
            x_wit.mul_assign(&z_wit);
            y_wit.mul_assign(&z_wit);

            let x = FieldElement::alloc(&mut cs, Some(x_wit), &rns_params).unwrap();
            let y = FieldElement::alloc(&mut cs, Some(y_wit), &rns_params).unwrap();
            let z = FieldElement::alloc(&mut cs, Some(z_wit), &rns_params).unwrap();

            *out = ProjectivePoint {
                x, y, z,
                circuit_params: &params,
                value: Some(affine_point.clone()),
            };
        }
      
        let counter_start = cs.get_current_step_number();
        let mut result = ProjectivePoint::double(&a, &mut cs).unwrap(); 
        result = result.add(&mut cs, &mut b).unwrap();
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

        let mut a = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(&params);
        let mut b = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(&params);
        let mut c = AffinePointExt::<Bn256, G1Affine, Bn256Extension2Params>::uninitialized(&params);
                
        let iter = std::iter::once(&mut a).chain(std::iter::once(&mut b)).chain(std::iter::once(&mut c)).zip(
            std::iter::once(&a_coefs).chain(std::iter::once(&b_coefs)).chain(std::iter::once(&c_coefs))
        );

        for (out, coeffs) in iter  { 
            let x_c0 = Fq::from_str(coeffs[0]);
            let x_c1 = Fq::from_str(coeffs[1]);
            let y_c0 = Fq::from_str(coeffs[2]);
            let y_c1 = Fq::from_str(coeffs[3]);
            let point = AffinePointExt::alloc(&mut cs, x_c0, x_c1, y_c0, y_c1, &params).unwrap();
            *out = point;
        }

        let counter_start = cs.get_current_step_number();
        let mut result = a.double_and_add_unequal_unchecked(&mut cs, &mut b).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);

        AffinePointExt::enforce_equal(&mut cs, &mut result, &mut c).unwrap();
        assert!(cs.is_satisfied()); 
    }

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // test correctness of basic arithmetic operations of a curve: add, sub, double, double_add
    fn affine_arithmetic_tester_impl<E, CS, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>>(
        cs: &mut CS, params: &CurveCircuitParameters<E, G, T>
    ) 
    where <G as GenericCurveAffine>::Base: PrimeField, E: Engine, CS: ConstraintSystem<E>
    {
        let mut rng = rand::thread_rng();
        let a_wit: G = rng.gen();
        let b_wit: G = rng.gen();
        let mut b_negated_wit = b_wit.clone();
        b_negated_wit.negate();
        
        let mut tmp = a_wit.into_projective();
        tmp.add_assign_mixed(&b_wit);
        let a_plus_b_wit = tmp.into_affine();

        let mut tmp = a_wit.into_projective();
        tmp.add_assign_mixed(&b_negated_wit);
        let a_minus_b_wit = tmp.into_affine();

        let mut tmp = a_wit.into_projective();
        tmp.double();
        let a_doubled_wit = tmp.into_affine();

        let mut tmp = a_wit.into_projective();
        tmp.double();
        tmp.add_assign_mixed(&b_wit);
        let a_doubled_plus_b_wit = tmp.into_affine();
        
        let mut a = AffinePoint::alloc(cs, Some(a_wit), params).unwrap();
        let mut b = AffinePoint::alloc(cs, Some(b_wit), params).unwrap();
        let mut a_plus_b_actual = AffinePoint::alloc(cs, Some(a_plus_b_wit), params).unwrap();
        let mut a_minus_b_actual = AffinePoint::alloc(cs, Some(a_minus_b_wit), params).unwrap();
        let mut a_doubled_actual = AffinePoint::alloc(cs, Some(a_doubled_wit), params).unwrap();
        let mut a_doubled_plus_b_actual = AffinePoint::alloc(cs, Some(a_doubled_plus_b_wit), params).unwrap();

        let mut a_plus_b_computed = a.add_unequal(cs, &mut b).unwrap();
        let mut a_minus_b_computed = a.sub_unequal(cs, &mut b).unwrap();
        let mut a_doubled_computed = a.double(cs).unwrap();
        let mut a_doubled_plus_b_computed = a.double_and_add_unequal_unchecked(cs, &mut b).unwrap();

        AffinePoint::enforce_equal(cs, &mut a_plus_b_actual, &mut a_plus_b_computed).unwrap();
        AffinePoint::enforce_equal(cs, &mut a_minus_b_actual, &mut a_minus_b_computed).unwrap();
        AffinePoint::enforce_equal(cs, &mut a_doubled_actual, &mut a_doubled_computed).unwrap();
        AffinePoint::enforce_equal(cs, &mut a_doubled_plus_b_actual, &mut a_doubled_plus_b_computed).unwrap();
    }

    #[test]
    fn affine_arithmetic_tester_for_bn256() {
        let mut cs = TrivialAssembly::<
            bn256::Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = generate_optimal_circuit_params_for_bn256::<bn256::Bn256, _>(&mut cs, 80usize, 80usize);
        affine_arithmetic_tester_impl(&mut cs, &params);
        assert!(cs.is_satisfied()); 
    }

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // benchmark projective add, add_mixed, double, double_add_mixed againt their affine_ext counterparts
    fn affine_ext_vs_projective_impl<E, CS, G: GenericCurveAffine + rand::Rand, T: Extension2Params<G::Base>>(
        cs: &mut CS, params: &CurveCircuitParameters<E, G, T>
    ) 
    where <G as GenericCurveAffine>::Base: PrimeField, E: Engine, CS: ConstraintSystem<E>
    {
        let rns_params = &params.base_field_rns_params;
        let mut rng = rand::thread_rng();
        let a_wit: G = rng.gen();
        let b_wit: G = rng.gen();

        let mut tmp = a_wit.into_projective();
        tmp.add_assign_mixed(&b_wit);
        let a_plus_b_wit = tmp.into_affine();

        let mut tmp = a_wit.into_projective();
        tmp.double();
        let a_doubled_wit = tmp.into_affine();

        let mut tmp = a_wit.into_projective();
        tmp.double();
        tmp.add_assign_mixed(&b_wit);
        let a_doubled_plus_b_wit = tmp.into_affine();

        let mut a_proj = ProjectivePoint::zero(&params);
        let mut b_proj = ProjectivePoint::zero(&params);

        let iter = std::iter::once((&a_wit, &mut a_proj)).chain(std::iter::once((&b_wit, &mut b_proj))); 
        for (affine_point, out) in iter { 
            let (mut x_wit, mut y_wit) = affine_point.into_xy_unchecked();
            let z_wit : G::Base = rng.gen();
            x_wit.mul_assign(&z_wit);
            y_wit.mul_assign(&z_wit);

            let x = FieldElement::alloc(cs, Some(x_wit), &rns_params).unwrap();
            let y = FieldElement::alloc(cs, Some(y_wit), &rns_params).unwrap();
            let z = FieldElement::alloc(cs, Some(z_wit), &rns_params).unwrap();

            *out = ProjectivePoint {
                x, y, z,
                circuit_params: &params,
                value: Some(affine_point.clone()),
            };
        };

        let a = AffinePoint::alloc(cs, Some(a_wit), params).unwrap();
        let b = AffinePoint::alloc(cs, Some(b_wit), params).unwrap();
        let mut a_plus_b = AffinePoint::alloc(cs, Some(a_plus_b_wit), params).unwrap();
        let mut a_doubled = AffinePoint::alloc(cs, Some(a_doubled_wit), params).unwrap();
        let mut a_doubled_plus_b = AffinePoint::alloc(cs, Some(a_doubled_plus_b_wit), params).unwrap();

        let counter_start = cs.get_current_step_number();
        let mut result_proj = a_proj.add(cs, &b_proj).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for projective add: {}", counter_end - counter_start);
        ProjectivePoint::enforce_equal(
            cs, &mut result_proj, &mut ProjectivePoint::from(a_plus_b.clone())
        ).unwrap();

        let offset_generator = AffinePointExt::constant(
            params.fp2_pt_ord3_x_c0, params.fp2_pt_ord3_x_c1, 
            params.fp2_pt_ord3_y_c0, params.fp2_pt_ord3_y_c1,
            &params
        );
        let a_ext = offset_generator.add_unequal_unchecked(cs, &AffinePointExt::from(a.clone())).unwrap();
        let b_ext = offset_generator.add_unequal_unchecked(cs, &AffinePointExt::from(b.clone())).unwrap();

        let counter_start = cs.get_current_step_number();
        let result_ext = a_ext.add_unequal_unchecked(cs, &b_ext).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for affine_ext add: {}", counter_end - counter_start);
        let tmp = result_ext.add_unequal_unchecked(cs, &offset_generator).unwrap();
        let point = tmp.get_x().c0.get_field_value().zip(tmp.get_y().c0.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        });
        let mut result_base = AffinePoint {
            x: tmp.get_x().c0,
            y: tmp.get_y().c0,
            value: point,
            circuit_params: params
        }; 
        AffinePoint::enforce_equal(cs, &mut result_base, &mut a_plus_b).unwrap();


        let counter_start = cs.get_current_step_number();
        let mut result_proj = a_proj.add_mixed(cs, &b).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for projective add mixed: {}", counter_end - counter_start);
        ProjectivePoint::enforce_equal(
            cs, &mut result_proj, &mut ProjectivePoint::from(a_plus_b.clone())
        ).unwrap();

        let counter_start = cs.get_current_step_number();
        let result_ext = a_ext.add_unequal_unchecked(cs, &AffinePointExt::from(b.clone())).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for affine_ext add mixed: {}", counter_end - counter_start);
        let tmp = result_ext.sub_unequal_unchecked(cs, &offset_generator).unwrap();
        let point = tmp.get_x().c0.get_field_value().zip(tmp.get_y().c0.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        });
        let mut result_base = AffinePoint {
            x: tmp.get_x().c0,
            y: tmp.get_y().c0,
            value: point,
            circuit_params: params
        }; 
        AffinePoint::enforce_equal(cs, &mut result_base, &mut a_plus_b).unwrap();


        let counter_start = cs.get_current_step_number();
        let mut result_proj = a_proj.double(cs).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for projective double: {}", counter_end - counter_start);
        ProjectivePoint::enforce_equal(
            cs, &mut result_proj, &mut ProjectivePoint::from(a_doubled.clone())
        ).unwrap();

        let counter_start = cs.get_current_step_number();
        let result_ext = a_ext.double(cs).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for affine_ext double: {}", counter_end - counter_start);
        let tmp = result_ext.add_unequal_unchecked(cs, &offset_generator).unwrap();
        let point = tmp.get_x().c0.get_field_value().zip(tmp.get_y().c0.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        });
        let mut result_base = AffinePoint {
            x: tmp.get_x().c0,
            y: tmp.get_y().c0,
            value: point,
            circuit_params: params
        }; 
        AffinePoint::enforce_equal(cs, &mut result_base, &mut a_doubled).unwrap();

        let counter_start = cs.get_current_step_number();
        let mut result_proj = a_proj.double(cs).unwrap(); 
        result_proj = result_proj.add_mixed(cs, &b).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates for projective double and add mixed: {}", counter_end - counter_start);
        ProjectivePoint::enforce_equal(
            cs, &mut result_proj, &mut ProjectivePoint::from(a_doubled_plus_b.clone())
        ).unwrap();

        let counter_start = cs.get_current_step_number();
        let result_ext = a_ext.double_and_add_unequal_unchecked(cs, &AffinePointExt::from(b)).unwrap(); 
        let counter_end = cs.get_current_step_number();
        println!("num of gates for affine_ext double and add mixed: {}", counter_end - counter_start);
        let tmp = result_ext.add_unequal_unchecked(cs, &offset_generator).unwrap();
        let point = tmp.get_x().c0.get_field_value().zip(tmp.get_y().c0.get_field_value()).map(|(x, y)| {
            G::from_xy_checked(x, y).expect("should be on the curve")
        });
        let mut result_base = AffinePoint {
            x: tmp.get_x().c0,
            y: tmp.get_y().c0,
            value: point,
            circuit_params: params
        }; 
        AffinePoint::enforce_equal(cs, &mut result_base, &mut a_doubled_plus_b).unwrap();
    }

    #[test]
    fn affine_ext_vs_projective_tester_for_bn256() {
        let mut cs = TrivialAssembly::<
            bn256::Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = generate_optimal_circuit_params_for_bn256::<bn256::Bn256, _>(&mut cs, 80usize, 80usize);
        affine_ext_vs_projective_impl(&mut cs, &params);
        assert!(cs.is_satisfied()); 
    }

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // benchmarking different implementations of point by scalar multiplicaton
    struct TestMulByScalarCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestMulByScalarCircuit<E, G, T> 
    where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
    {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }
    
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut rng = rand::thread_rng();
            let a: G = rng.gen();
            let scalar : G::Scalar = rng.gen();
            let mut tmp = a.into_projective();
            tmp.mul_assign(scalar);
            let result = tmp.into_affine();
            
            let mut a = AffinePoint::alloc(cs, Some(a), &self.circuit_params)?;
            let mut scalar = FieldElement::alloc(cs, Some(scalar), &self.circuit_params.scalar_field_rns_params)?;
            let mut actual_result = AffinePoint::alloc(cs, Some(result), &self.circuit_params)?;

            let counter_start = cs.get_current_step_number();
            let (mut result, _) = a.mul_by_scalar_complete(cs, &mut scalar)?;
            let counter_end = cs.get_current_step_number();
            println!("num of gates for complete scalar multiplication: {}", counter_end - counter_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let counter_start = cs.get_current_step_number();
            let mut result = a.mul_by_scalar_non_complete(cs, &mut scalar)?;
            let counter_end = cs.get_current_step_number();
            println!("num of gates for non-complete scalar multiplication: {}", counter_end - counter_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            Ok(())
        }
    }

    #[test]
    fn test_scalar_multiplication_for_bn256() {
        use self::bn256::Bn256;
        const LIMB_SIZE: usize = 80;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestMulByScalarCircuit { circuit_params };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }

    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------
    // benchmarking different implementations of multiexp
    struct TestMultiexpCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>,
        num_of_points: usize
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestMultiexpCircuit<E, G, T> 
    where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
    {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }
    
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut rng = rand::thread_rng();
            let mut points = Vec::with_capacity(self.num_of_points);
            let mut scalars = Vec::with_capacity(self.num_of_points);

            let mut result_wit_proj = G::Projective::zero();
            for _ in 0..self.num_of_points {
                let scalar_wit : G::Scalar = rng.gen();
                let point_wit : G = rng.gen();

                let mut tmp = point_wit.into_projective();
                tmp.mul_assign(scalar_wit);
                result_wit_proj.add_assign(&tmp);

                let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
                let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;

                points.push(point);
                scalars.push(scalar);
            }

            let result_wit = result_wit_proj.into_affine();
            let mut actual_result = AffinePoint::alloc(cs, Some(result_wit), &self.circuit_params)?;
           
            let counter_start = cs.get_current_step_number();
            let (mut result, _) = AffinePoint::multiexp_complete(cs, &mut scalars, &mut points)?;
            let counter_end = cs.get_current_step_number();
            println!("num of gates for complete multiexp: {}", counter_end - counter_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            let counter_start = cs.get_current_step_number();
            let mut result = AffinePoint::multiexp_non_complete(cs, &mut scalars, &mut points)?;
            let counter_end = cs.get_current_step_number();
            println!("num of gates for non-complete multiexp: {}", counter_end - counter_start);
            AffinePoint::enforce_equal(cs, &mut result, &mut actual_result)?;

            Ok(())
        }
    }

    #[test]
    fn test_multiexp_for_bn256() {
        use self::bn256::Bn256;
        const LIMB_SIZE: usize = 80;
        const NUM_OF_POINTS: usize = 3;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestMultiexpCircuit { circuit_params, num_of_points: NUM_OF_POINTS };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }
}
use crate::bellman::pairing::{CurveAffine, Engine};

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{ConstraintSystem, Variable};

use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams as CSParams;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::{proof::Proof, setup::VerificationKey};
use crate::bellman::plonk::domains::*;

use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::curve::*;
use crate::plonk::circuit::simple_term::*;

use super::affine_point_wrapper::aux_data::AuxData;
use super::affine_point_wrapper::WrappedAffinePoint;
use super::channel::*;
use super::helper_functions::*;
use super::new_data_structs::*;

use circuit::Assignment;
use plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
use std::cell::Cell;

#[track_caller]
pub fn verify_and_aggregate<'a, E, CS, T, P, AD, WP>(
    cs: &mut CS,
    channel_params: &'a T::Params,
    public_inputs: &[AllocatedNum<E>],
    vk: &mut VerificationKeyGagdet<'a, E, WP>,
    proof: &mut ProofGadget<'a, E, WP>,
    aux_data: &AD,
    params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    g2_elements: &[E::G2Affine; 2],
) -> Result<[WP; 2], SynthesisError>
where
    E: Engine,
    CS: ConstraintSystem<E>,
    T: ChannelGadget<E>,
    AD: AuxData<E>,
    P: PlonkConstraintSystemParams<E>,
    WP: WrappedAffinePoint<'a, E>,
{
    println!("recursive start!");

    assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

    let mut channel = T::new(channel_params);

    if proof.inputs.len() != vk.num_inputs {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let required_domain_size = if let Some(n) = vk.n {
        assert!(vk.domain_size_as_allocated_num.is_none());
        let required_domain_size = n + 1;
        if required_domain_size.is_power_of_two() == false {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        Some(required_domain_size)
    } else {
        assert!(vk.domain_size_as_allocated_num.is_some());

        None
    };

    let (omega_const, omega_inv_const) = if let Some(required_domain_size) = required_domain_size {
        let domain = Domain::<E::Fr>::new_for_size(required_domain_size as u64)?;
        let omega = domain.generator;
        let omega_inv = domain.generator.inverse().expect("should exist");

        (Some(omega), Some(omega_inv))
    } else {
        (None, None)
    };

    println!("omega: {:?}", omega_const);
    println!("omega_inv_const: {:?}", omega_inv_const);

    let domain_size_decomposed = if let Some(domain_size) = vk.domain_size_as_allocated_num.as_ref()
    {
        assert!(vk.n.is_none());
        let absolute_limit = (E::Fr::S + 1) as usize;
        let decomposed = domain_size.into_bits_le(cs, Some(absolute_limit))?;

        Some(decomposed)
    } else {
        assert!(vk.n.is_some());

        None
    };

    let selector_q_const_index = P::STATE_WIDTH + 1;
    let selector_q_m_index = P::STATE_WIDTH;

    // Commit public inputs
    for inp in proof.inputs.iter() {
        println!("proof.inputs : {:?}", inp);
        channel.consume(inp.clone(), cs)?;
    }

    for (inp, inp_from_proof) in public_inputs.iter().zip(proof.inputs.iter()) {
        inp.enforce_equal(cs, inp_from_proof)?;
    }

    // Commit wire values
    for w in proof.state_polys_commitments.iter() {
        channel.consume_point(cs, w.clone())?;
        println!("{:?}", w.get_point().value);
    }

    let beta = channel.produce_challenge(cs)?;
    let gamma = channel.produce_challenge(cs)?;
    println!("beta: {:?}", beta.get_value());
    println!("gamma: {:?}", gamma.get_value());

    // commit grand product
    channel.consume_point(cs, proof.copy_permutation_grand_product_commitment.clone())?;

    let alpha = channel.produce_challenge(cs)?;
    println!("alpha: {:?}", alpha.get_value());

    // Commit parts of the quotient polynomial
    for w in proof.quotient_poly_parts_commitments.iter() {
        channel.consume_point(cs, w.clone())?;
    }

    let z = channel.produce_challenge(cs)?;
    println!("z: {:?}", z.get_value());

    // commit every claimed value

    channel.consume(proof.quotient_poly_opening_at_z.clone(), cs)?;
    for el in proof.state_polys_openings_at_z.iter() {
        channel.consume(el.clone(), cs)?;
    }

    for el in proof.state_polys_openings_at_dilations.iter() {
        channel.consume(el.clone(), cs)?;
    }

    channel.consume(proof.gate_selectors_openings_at_z[0].clone(), cs)?;
    for el in proof.copy_permutation_polys_openings_at_z.iter() {
        channel.consume(el.clone(), cs)?;
    }

    channel.consume(
        proof
            .copy_permutation_grand_product_opening_at_z_omega
            .clone(),
        cs,
    )?;
    channel.consume(proof.linearization_poly_opening_at_z.clone(), cs)?;

    let z_in_pow_domain_size = if let Some(required_domain_size) = required_domain_size {
        assert!(required_domain_size.is_power_of_two());
        let mut z_in_pow_domain_size = z.clone();
        for _ in 0..required_domain_size.trailing_zeros() {
            z_in_pow_domain_size = z_in_pow_domain_size.square(cs)?;
        }

        z_in_pow_domain_size
    } else {
        let pow_decomposition = domain_size_decomposed.as_ref().unwrap();

        let mut pow_decomposition = pow_decomposition.to_vec();
        pow_decomposition.reverse();

        let z_in_pow_domain_size = AllocatedNum::<E>::pow(cs, &z, &pow_decomposition)?;

        z_in_pow_domain_size
    };

    let omega_inv_variable = if let Some(omega) = vk.omega_as_allocated_num.as_ref() {
        let inv = omega.inverse(cs).expect(&format!(
            "Inverse of the domain generator must exist! Omega = {:?}",
            omega.get_value()
        ));

        Some(inv)
    } else {
        None
    };

    let mut l_0_at_z = if let Some(required_domain_size) = required_domain_size {
        let omega_inv = omega_inv_const.unwrap();
        let l_0_at_z = evaluate_lagrange_poly(
            cs,
            required_domain_size,
            0,
            &omega_inv,
            z.clone(),
            z_in_pow_domain_size.clone(),
        )?;

        l_0_at_z
    } else {
        let l_0_at_z = evaluate_lagrange_poly_for_variable_domain_size(
            cs,
            0,
            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
            omega_inv_variable.as_ref().unwrap(),
            z.clone(),
            z_in_pow_domain_size.clone(),
        )?;

        l_0_at_z
    };

    // do the actual check for relationship at z
    {
        let mut lhs = proof.quotient_poly_opening_at_z.clone();
        let vanishing_at_z = evaluate_vanishing_poly(cs, z_in_pow_domain_size.clone())?;
        lhs = lhs.mul(cs, &vanishing_at_z)?;

        let mut rhs = proof.linearization_poly_opening_at_z.clone();

        // add public inputs
        {
            let mut input_term = AllocatedNum::zero(cs);
            for (idx, input) in proof.inputs.iter().enumerate() {
                let mut tmp = if idx == 0 {
                    l_0_at_z.mul(cs, &input)?
                } else {
                    let mut tmp = if let Some(required_domain_size) = required_domain_size {
                        let omega_inv = omega_inv_const.unwrap();
                        let tmp = evaluate_lagrange_poly(
                            cs,
                            required_domain_size,
                            idx,
                            &omega_inv,
                            z.clone(),
                            z_in_pow_domain_size.clone(),
                        )?;

                        tmp
                    } else {
                        let tmp = evaluate_lagrange_poly_for_variable_domain_size(
                            cs,
                            idx,
                            vk.domain_size_as_allocated_num.as_ref().unwrap().clone(),
                            omega_inv_variable.as_ref().unwrap(),
                            z.clone(),
                            z_in_pow_domain_size.clone(),
                        )?;

                        tmp
                    };
                    tmp.mul(cs, &input)?
                };
                input_term = input_term.add(cs, &mut tmp)?;
            }
            input_term = input_term.mul(cs, &mut proof.gate_selectors_openings_at_z[0])?;
            rhs = rhs.add(cs, &input_term)?;
        }

        // - \alpha (a + perm(z) * beta + gamma)*()*(d + gamma) & z(z*omega)

        let mut z_part = proof
            .copy_permutation_grand_product_opening_at_z_omega
            .clone();

        for (w, p) in proof
            .state_polys_openings_at_z
            .iter()
            .zip(proof.copy_permutation_polys_openings_at_z.iter())
        {
            let mut tmp = p.clone();
            tmp = tmp.mul(cs, &beta)?;
            tmp = tmp.add(cs, &gamma)?;
            tmp = tmp.add(cs, &w)?;

            z_part = z_part.mul(cs, &tmp)?;
        }

        let mut quotient_linearization_challenge = alpha.mul(cs, &alpha)?;
        quotient_linearization_challenge =
            quotient_linearization_challenge.mul(cs, &quotient_linearization_challenge)?;
        quotient_linearization_challenge =
            quotient_linearization_challenge.mul(cs, &quotient_linearization_challenge)?;
        // quotient_linearization_challenge = quotient_linearization_challenge.mul(cs, &alpha)?;
        // last poly value and gamma
        let mut tmp = gamma.clone();
        tmp = tmp.add(
            cs,
            &proof.state_polys_openings_at_z.iter().rev().next().unwrap(),
        )?;

        z_part = z_part.mul(cs, &tmp)?;
        z_part = z_part.mul(cs, &quotient_linearization_challenge)?;
        rhs = rhs.sub(cs, &z_part)?;

        //  let quotient_linearization_challenge = alpha.mul(cs, &alpha)?;
        quotient_linearization_challenge = quotient_linearization_challenge.mul(cs, &alpha)?;
        // - L_0(z) * \alpha^2
        let tmp = l_0_at_z.mul(cs, &quotient_linearization_challenge)?;
        rhs = rhs.sub(cs, &tmp)?;

        lhs.enforce_equal(cs, &rhs)?;
        println!("lhs enforce_equal rhs");
    }

    let v = channel.produce_challenge(cs)?;

    println!("v: {:?}", v.get_value());
    channel.consume_point(cs, proof.opening_proof_at_z.clone())?;
    channel.consume_point(cs, proof.opening_proof_at_z_omega.clone())?;

    let u = channel.produce_challenge(cs)?;
    println!("u: {:?}", u.get_value());

    // verify_initial end

    // first let's reconstruct the linearization polynomial from
    // honomorphic commitments, and simultaneously add (through the separation scalar "u")
    // part for opening of z(X) at z*omega

    // calculate the power to add z(X) commitment that is opened at x*omega
    // it's r(X) + witness + all permutations + 1

    // let v_power_for_standalone_z_x_opening = 1 + 1 + P::STATE_WIDTH + (P::STATE_WIDTH-1);

    let mut virtual_commitment_for_linearization_poly = {
        let mut res = vk.gate_setup_commitments[STATE_WIDTH + 1].clone();
        let mut tmp_g1 = WP::alloc(cs, Some(E::G1Affine::one()), params, aux_data)?; // G1(1,2)
        let mut tmp_fr = AllocatedNum::zero(cs); // 0

        for i in 0..P::STATE_WIDTH {
            tmp_g1 = vk.gate_setup_commitments[i].mul(
                cs,
                &proof.state_polys_openings_at_z[i],
                None,
                params,
                aux_data,
            )?;
            res = res.add(cs, &mut tmp_g1, params)?;
        }

        tmp_fr = proof.state_polys_openings_at_z[0].mul(cs, &proof.state_polys_openings_at_z[1])?;
        tmp_g1 = vk.gate_setup_commitments[STATE_WIDTH].mul(cs, &tmp_fr, None, params, aux_data)?;
        res = res.add(cs, &mut tmp_g1, params)?;

        // d_next
        tmp_g1 = vk.gate_setup_commitments[STATE_WIDTH + 2].mul(
            cs,
            &proof.state_polys_openings_at_dilations[0],
            None,
            params,
            aux_data,
        )?; // index of q_d_next(x)
        res = res.add(cs, &mut tmp_g1, params)?;

        // multiply by main gate selector(z)
        res = res.mul(
            cs,
            &proof.gate_selectors_openings_at_z[0],
            None,
            params,
            aux_data,
        )?; // these is only one explicitly opened selector

        let mut current_alpha = AllocatedNum::one(cs);
        // calculate scalar contribution from the range check gate
        {
            tmp_fr = {
                let mut one_fr = AllocatedNum::one(cs);
                let mut two_fr = one_fr.add(cs, &one_fr)?;
                let mut three_fr = two_fr.add(cs, &one_fr)?;
                let mut four_fr = three_fr.add(cs, &one_fr)?;

                let mut res = AllocatedNum::zero(cs);
                let mut t0 = AllocatedNum::zero(cs);
                let mut t1 = AllocatedNum::zero(cs);
                let mut t2 = AllocatedNum::zero(cs);

                for i in 0..3 {
                    current_alpha = current_alpha.mul(cs, &alpha)?;

                    // high - 4*low

                    // this is 4*low
                    t0 = proof.state_polys_openings_at_z[3 - i].mul(cs, &four_fr)?;

                    // high
                    t1 = proof.state_polys_openings_at_z[2 - i].sub(cs, &t0)?;

                    // t0 is now t1 - {0,1,2,3}

                    // first unroll manually for -0;
                    t2 = t1.clone();

                    // -1
                    t0 = t1.sub(cs, &one_fr)?;
                    t2 = t2.mul(cs, &t0)?;

                    // -2
                    t0 = t1.sub(cs, &two_fr)?;
                    t2 = t2.mul(cs, &t0)?;

                    // -3
                    t0 = t1.sub(cs, &three_fr)?;
                    t2 = t2.mul(cs, &t0)?;

                    t2 = t2.mul(cs, &current_alpha)?;

                    res = res.add(cs, &t2)?;
                }

                // now also d_next - 4a

                current_alpha = current_alpha.mul(cs, &alpha)?;

                // high - 4*low

                // this is 4*low
                t0 = proof.state_polys_openings_at_z[0].mul(cs, &four_fr)?;

                // high
                t1 = proof.state_polys_openings_at_dilations[0].sub(cs, &t0)?;

                // t0 is now t1 - {0,1,2,3}

                // first unroll manually for -0;
                t2 = t1.clone();

                // -1
                t0 = t1.sub(cs, &one_fr)?;
                t2 = t2.mul(cs, &t0)?;

                // -2
                t0 = t1.sub(cs, &two_fr)?;
                t2 = t2.mul(cs, &t0)?;

                // -3
                t0 = t1.sub(cs, &three_fr)?;
                t2 = t2.mul(cs, &t0)?;

                t2 = t2.mul(cs, &current_alpha)?;

                res = res.add(cs, &t2)?;

                res
            }
        }

        tmp_g1 = vk.gate_selectors_commitments[1].mul(cs, &tmp_fr, None, params, aux_data)?; // selector commitment for range constraint gate * scalar
        res = res.add(cs, &mut tmp_g1, params)?;

        //add_contribution_from_rescue_custom_gates
        tmp_fr = {
            let a_value = proof.state_polys_openings_at_z[0];
            let b_value = proof.state_polys_openings_at_z[1];
            let c_value = proof.state_polys_openings_at_z[2];
            let d_value = proof.state_polys_openings_at_z[3];

            current_alpha = current_alpha.mul(cs, &alpha)?;

            //a^2 - b = 0
            let mut res = a_value;
            res = res.mul(cs, &a_value)?;
            res = res.sub(cs, &b_value)?;
            res = res.mul(cs, &current_alpha)?;

            current_alpha = current_alpha.mul(cs, &alpha)?;

            // b^2 - c = 0
            let mut tmp = b_value;
            tmp = tmp.mul(cs, &b_value)?;
            tmp = tmp.sub(cs, &c_value)?;
            tmp = tmp.mul(cs, &current_alpha)?;

            res = res.add(cs, &tmp)?;

            current_alpha = current_alpha.mul(cs, &alpha)?;

            // c*a - d = 0;
            let mut tmp = c_value;
            tmp = tmp.mul(cs, &a_value)?;
            tmp = tmp.sub(cs, &d_value)?;
            tmp = tmp.mul(cs, &current_alpha)?;

            res.add(cs, &tmp)?
        };

        tmp_g1 = vk.gate_selectors_commitments[2].mul(cs, &tmp_fr, None, params, aux_data)?; // selector commitment for range constraint gate * scalar
        res = res.add(cs, &mut tmp_g1, params)?;

        println!(
            "add_contribution_from_rescue_custom_gates end res: {:?}",
            res.get_point().value
        );

        current_alpha = current_alpha.mul(cs, &alpha)?;

        let mut alpha_for_grand_product = current_alpha.clone();

        let mut grand_product_part_at_z = AllocatedNum::alloc(cs, || {
            // non_res * z * beta + wire

            let mut result = *z.get_value().get()?;
            result.mul_assign(beta.get_value().get()?);
            result.add_assign(&*proof.state_polys_openings_at_z[0].get_value().get()?);
            result.add_assign(gamma.get_value().get()?);

            Ok(result)
        })?;

        for i in 0..vk.non_residues.len() {
            let mut tmp_fr = AllocatedNum::alloc(cs, || {
                let mut tmp_fr = *z.get_value().get()?;
                tmp_fr.mul_assign(&vk.non_residues[i]);
                tmp_fr.mul_assign(beta.get_value().get()?);
                tmp_fr.add_assign(gamma.get_value().get()?);
                tmp_fr.add_assign(proof.state_polys_openings_at_z[i + 1].get_value().get()?);

                Ok(tmp_fr)
            })?;
            grand_product_part_at_z = grand_product_part_at_z.mul(cs, &mut tmp_fr)?;
        }

        grand_product_part_at_z = grand_product_part_at_z.mul(cs, &alpha_for_grand_product)?;

        current_alpha = current_alpha.mul(cs, &alpha)?;

        // tmp_fr.assign(state.cached_lagrange_evals[0]);
        // tmp_fr.mul_assign(current_alpha);
        // tmp_fr = l_0_at_z.mul(cs, &current_alpha)?;
        // grand_product_part_at_z = grand_product_part_at_z.add(cs, &tmp_fr)?;

        let mut last_permutation_part_at_z = AllocatedNum::one(cs); // 0
        for i in 0..proof.copy_permutation_polys_openings_at_z.len() {
            let mut tmp_fr = AllocatedNum::alloc(cs, || {
                let mut tmp_fr = *beta.get_value().get()?;
                tmp_fr.mul_assign(
                    &*proof.copy_permutation_polys_openings_at_z[i]
                        .get_value()
                        .get()?,
                );
                tmp_fr.add_assign(gamma.get_value().get()?);
                tmp_fr.add_assign(proof.state_polys_openings_at_z[i].get_value().get()?);

                Ok(tmp_fr)
            })?;

            last_permutation_part_at_z = last_permutation_part_at_z.mul(cs, &tmp_fr)?;
        }

        last_permutation_part_at_z = last_permutation_part_at_z.mul(cs, &beta)?;
        last_permutation_part_at_z = last_permutation_part_at_z
            .mul(cs, &proof.copy_permutation_grand_product_opening_at_z_omega)?;
        last_permutation_part_at_z =
            last_permutation_part_at_z.mul(cs, &alpha_for_grand_product)?;

        // actually multiply prefactors by z(x) and perm_d(x) and combine them
        let mut tmp_g1 = proof.copy_permutation_grand_product_commitment.mul(
            cs,
            &grand_product_part_at_z,
            None,
            params,
            aux_data,
        )?;
        let mut tmp_g2 = vk.permutation_commitments[STATE_WIDTH - 1].mul(
            cs,
            &last_permutation_part_at_z,
            None,
            params,
            aux_data,
        )?;
        tmp_g1 = tmp_g1.sub(cs, &mut tmp_g2, params)?;

        res = res.add(cs, &mut tmp_g1, params)?;

        println!(
            "current-alpha before evaluate_l0_at_point : {:?}",
            current_alpha
        );
        println!(
            "evaluate_l0_at_point before res : {:?}",
            res.get_point().value
        );
        //TODO change start evaluate_l0_at_point
        tmp_fr = {
            let mut den = z;
            let one = AllocatedNum::one(cs);
            let domain_size = AllocatedNum::alloc(cs, || {
                E::Fr::from_str(&*format!("{}", vk.n.unwrap() + 1))
                    .ok_or(SynthesisError::MalformedVerifyingKey)
            })?;
            den = den.sub(cs, &one)?;
            den = den.mul(cs, &domain_size)?;

            den = den.inverse(cs)?;
            println!("den in evaluate_l0_at_point : {:?}", den);

            let absolute_limit = (E::Fr::S + 1) as usize;

            let mut power = domain_size.into_bits_le(cs, Some(absolute_limit))?;
            power.reverse();

            let mut res = AllocatedNum::<E>::pow(cs, &z, &power)?;
            res = res.sub(cs, &one)?;
            res.mul(cs, &den)?
        };
        println!("tmp_fr after evaluate_l0_at_point : {:?}", tmp_fr);
        tmp_fr = tmp_fr.mul(cs, &current_alpha)?;
        tmp_g1 = proof
            .copy_permutation_grand_product_commitment
            .mul(cs, &tmp_fr, None, params, aux_data)?;
        res = res.add(cs, &mut tmp_g1, params)?;
        //change end

        println!("evaluate_l0_at_point end res : {:?}", res.get_point().value);

        // multiply them by v immedately as linearization has a factor of v^1
        res = res.mul(cs, &v, None, params, aux_data)?;
        // res now contains contribution from the gates linearization and
        // copy permutation part

        // now we need to add a part that is the rest
        // for z(x*omega):
        // - (a(z) + beta*perm_a + gamma)*()*()*(d(z) + gamma) * z(x*omega)

        res
    };

    // println!("virtual_commitment_for_linearization_poly: {:?}", virtual_commitment_for_linearization_poly.get_value());
    // now check the openings
    // aggregate t(X) from parts

    let mut tmp_g1 = WP::alloc(cs, Some(E::G1Affine::one()), params, aux_data)?; // G1(1,2)
    let mut aggregation_challenge = AllocatedNum::one(cs);
    let mut commitment_aggregation = proof.quotient_poly_parts_commitments[0].clone();
    let mut tmp_fr = AllocatedNum::one(cs);

    for i in 1..proof.quotient_poly_parts_commitments.len() {
        tmp_fr = tmp_fr.mul(cs, &z_in_pow_domain_size)?;
        tmp_g1 =
            proof.quotient_poly_parts_commitments[i].mul(cs, &tmp_fr, None, params, aux_data)?;
        commitment_aggregation = commitment_aggregation.add(cs, &mut tmp_g1, params)?;
    }
    // pass
    println!(
        "commitment_aggregation,after quotient_poly_parts_commitments:\n{:?}",
        commitment_aggregation.get_point().value
    );

    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
    println!(
        "virtual_commitment_for_linearization_poly:\n{:?}",
        virtual_commitment_for_linearization_poly.get_point().value
    );
    commitment_aggregation =
        commitment_aggregation.add(cs, &mut virtual_commitment_for_linearization_poly, params)?;
    //pass
    println!(
        "commitment_aggregation,after add commitment_for_linearization_poly:\n{:?}",
        commitment_aggregation.get_point().value
    );

    // do the same for wires
    for com in proof.state_polys_commitments.iter_mut() {
        // add to second multiexp as well
        aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
        tmp_g1 = com.mul(cs, &aggregation_challenge, None, params, aux_data)?;
        commitment_aggregation = commitment_aggregation.add(cs, &mut tmp_g1, params)?;
    }

    println!(
        "commitment_aggregation,after state_polys_commitments:\n{:?}",
        commitment_aggregation.get_point().value
    );

    //START for NUM_GATE_SELECTORS_OPENED_EXPLICITLY == 1
    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
    tmp_g1 =
        vk.gate_selectors_commitments[0].mul(cs, &aggregation_challenge, None, params, aux_data)?;
    commitment_aggregation = commitment_aggregation.add(cs, &mut tmp_g1, params)?;
    //END

    // and for all permutation polynomials except the last one
    assert_eq!(
        vk.permutation_commitments.len(),
        proof.copy_permutation_polys_openings_at_z.len() + 1
    );

    let arr_len = vk.permutation_commitments.len();
    for com in vk.permutation_commitments[0..(arr_len - 1)].iter_mut() {
        aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
        tmp_g1 = com.mul(cs, &aggregation_challenge, None, params, aux_data)?;
        commitment_aggregation = commitment_aggregation.add(cs, &mut tmp_g1, params)?;
    }
    println!(
        "commitment_aggregation,after state_polys_commitments:\n{:?}",
        commitment_aggregation.get_point().value
    );

    // we skip z(X) at z
    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;

    // aggregate last wire commitment (that is opened at z*omega)
    // using multiopening challenge and u
    let mut tmp_fr = aggregation_challenge.mul(cs, &u)?;
    let mut tmp = proof
        .copy_permutation_grand_product_commitment
        .mul(cs, &tmp_fr, None, params, aux_data)?;
    commitment_aggregation = commitment_aggregation.add(cs, &mut tmp, params)?;

    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
    // add to second multiexp
    tmp_fr = aggregation_challenge.mul(cs, &u)?;
    tmp_g1 =
        proof.state_polys_commitments[STATE_WIDTH - 1].mul(cs, &tmp_fr, None, params, aux_data)?;
    commitment_aggregation = commitment_aggregation.add(cs, &mut tmp_g1, params)?;

    // diff
    println!(
        "commitment_aggregation : {:?}",
        commitment_aggregation.get_point().value
    );
    // subtract the opening value using one multiplication

    let mut aggregation_challenge = v.clone();
    let mut aggregated_value = proof.quotient_poly_opening_at_z.clone();

    tmp_fr = proof.linearization_poly_opening_at_z;
    tmp_fr = tmp_fr.mul(cs, &aggregation_challenge)?;
    aggregated_value = aggregated_value.add(cs, &tmp_fr)?;

    for i in 0..proof.state_polys_openings_at_z.len() {
        aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
        let tmp_fr = proof.state_polys_openings_at_z[i].mul(cs, &aggregation_challenge)?;
        aggregated_value = aggregated_value.add(cs, &tmp_fr)?;
    }

    for i in 0..proof.gate_selectors_openings_at_z.len() {
        aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
        let tmp = proof.gate_selectors_openings_at_z[i].mul(cs, &aggregation_challenge)?;
        aggregated_value = aggregated_value.add(cs, &tmp)?;
    }

    for i in 0..proof.copy_permutation_polys_openings_at_z.len() {
        aggregation_challenge = aggregation_challenge.mul(cs, &v)?;
        let tmp = proof.copy_permutation_polys_openings_at_z[i].mul(cs, &aggregation_challenge)?;
        aggregated_value = aggregated_value.add(cs, &tmp)?;
    }

    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;

    tmp_fr = proof
        .copy_permutation_grand_product_opening_at_z_omega
        .mul(cs, &aggregation_challenge)?;
    tmp_fr = tmp_fr.mul(cs, &u)?;
    aggregated_value = aggregated_value.add(cs, &tmp_fr)?;

    aggregation_challenge = aggregation_challenge.mul(cs, &v)?;

    tmp_fr = proof.state_polys_openings_at_dilations[0].mul(cs, &aggregation_challenge)?;
    tmp_fr = tmp_fr.mul(cs, &u)?;
    aggregated_value = aggregated_value.add(cs, &tmp_fr)?;

    let mut tmp_g1 = WP::alloc(cs, Some(E::G1Affine::one()), params, aux_data)?; // G1(1,2)
    tmp_g1 = tmp_g1.mul(cs, &aggregated_value, None, params, aux_data)?;
    commitment_aggregation = commitment_aggregation.sub(cs, &mut tmp_g1, params)?;

    // add parts that are opened at z*omega using `u`
    let mut pair_with_generator = commitment_aggregation.clone();
    let mut tmp = proof
        .opening_proof_at_z
        .mul(cs, &z, None, params, aux_data)?;
    pair_with_generator = pair_with_generator.add(cs, &mut tmp, params)?;

    let mut tmp_fr = z.mul(cs, &vk.omega_as_allocated_num.unwrap())?;
    tmp_fr = tmp_fr.mul(cs, &u)?;
    tmp_g1 = proof
        .opening_proof_at_z_omega
        .mul(cs, &tmp_fr, None, params, aux_data)?;
    pair_with_generator = pair_with_generator.add(cs, &mut tmp_g1, params)?;

    let mut pair_with_x = proof
        .opening_proof_at_z_omega
        .mul(cs, &u, None, params, aux_data)?;
    pair_with_x = pair_with_x.add(cs, &mut proof.opening_proof_at_z, params)?;
    pair_with_x = pair_with_x.negate(cs, params)?;

    let mut scalars = vec![];
    scalars.push(aggregation_challenge);

    // let mut current = aggregation_challenge;
    // for _ in 1..2 {
    //     let new = current.mul(cs, &aggregation_challenge)?;
    //     scalars.push(new);
    //
    //     current = new;
    // }

    let pair_with_generator =
        WP::multiexp(cs, &scalars, &[pair_with_generator], None, params, aux_data)?;
    let pair_with_x = WP::multiexp(cs, &scalars, &[pair_with_x], None, params, aux_data)?;

    if let (Some(with_gen), Some(with_x)) = (
        pair_with_generator.get_point().get_value(),
        pair_with_x.get_point().get_value(),
    ) {
        let valid = E::final_exponentiation(&E::miller_loop(&[
            (&with_gen.prepare(), &g2_elements[0].prepare()),
            (&with_x.prepare(), &g2_elements[1].prepare()),
        ]))
        .unwrap()
            == E::Fqk::one();

        assert!(valid);
    } else {
        panic!("pair_with_generator and pair_with_x get_point no value.")
    }

    println!("recursive circuit final!");
    Ok([pair_with_generator, pair_with_x])
}

pub struct PlonkVerifierCircuit<'a, E, T, P, C, AD, WP>
where
    E: Engine,
    T: ChannelGadget<E>,
    AD: AuxData<E>,
    C: Circuit<E>,
    P: PlonkConstraintSystemParams<E>,
    WP: WrappedAffinePoint<'a, E>,
{
    _engine_marker: std::marker::PhantomData<E>,
    _channel_marker: std::marker::PhantomData<T>,
    _cs_params_marker: std::marker::PhantomData<P>,
    _circuit_params_marker: std::marker::PhantomData<C>,
    _point_wrapper_marker: std::marker::PhantomData<WP>,

    channel_params: &'a T::Params,
    public_inputs: Vec<E::Fr>,

    supposed_outputs: Vec<E::G1Affine>,
    proof: Cell<Option<Proof<E, C>>>,
    vk: Cell<Option<VerificationKey<E, C>>>,
    aux_data: AD,
    params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,

    g2_elements: [E::G2Affine; 2],
}

impl<'a, E, T, P, C, AD, WP> PlonkVerifierCircuit<'a, E, T, P, C, AD, WP>
where
    E: Engine,
    T: ChannelGadget<E>,
    AD: AuxData<E>,
    P: PlonkConstraintSystemParams<E>,
    C: Circuit<E>,
    WP: WrappedAffinePoint<'a, E>,
{
    pub fn new(
        channel_params: &'a T::Params,
        public_inputs: Vec<E::Fr>,
        supposed_outputs: Vec<E::G1Affine>,
        proof: Proof<E, C>,
        vk: VerificationKey<E, C>,
        aux_data: AD,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        g2_bases: [E::G2Affine; 2],
    ) -> Self {
        PlonkVerifierCircuit {
            _engine_marker: std::marker::PhantomData::<E>,
            _channel_marker: std::marker::PhantomData::<T>,
            _cs_params_marker: std::marker::PhantomData::<P>,
            _circuit_params_marker: std::marker::PhantomData::<C>,
            _point_wrapper_marker: std::marker::PhantomData::<WP>,

            channel_params,
            public_inputs,
            supposed_outputs,

            proof: Cell::new(Some(proof)),
            vk: Cell::new(Some(vk)),
            aux_data,
            params,

            g2_elements: g2_bases,
        }
    }
}

impl<'a, E, T, P, C, AD, WP> Circuit<E> for PlonkVerifierCircuit<'a, E, T, P, C, AD, WP>
where
    E: Engine,
    T: ChannelGadget<E>,
    AD: AuxData<E>,
    P: PlonkConstraintSystemParams<E>,
    C: Circuit<E>,
    WP: WrappedAffinePoint<'a, E>,
{
    type MainGate = Width4MainGateWithDNext;

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);

        let mut actual_proof = self.proof.replace(None).unwrap();
        let mut actual_vk = self.vk.replace(None).unwrap();

        let mut proof = ProofGadget::<E, WP>::alloc(cs, actual_proof, self.params, &self.aux_data)?;
        let mut vk =
            VerificationKeyGagdet::<E, WP>::alloc(cs, actual_vk, self.params, &self.aux_data)?;

        let inputs = proof.inputs.clone();
        let _ = verify_and_aggregate::<E, _, T, P, AD, WP>(
            cs,
            self.channel_params,
            &inputs,
            &mut vk,
            &mut proof,
            &self.aux_data,
            &self.params,
            &self.g2_elements,
        )?;

        Ok(())
    }

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        use crate::plonk::circuit::bigint::range_constraint_gate::TwoBitDecompositionRangecheckCustomGate;

        Ok(vec![
            Self::MainGate::default().into_internal(),
            TwoBitDecompositionRangecheckCustomGate::default().into_internal(),
            Rescue5CustomGate::default().into_internal(),
        ])
    }
}

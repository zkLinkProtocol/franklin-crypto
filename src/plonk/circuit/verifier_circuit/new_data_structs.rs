use super::affine_point_wrapper::aux_data::AuxData;
use super::affine_point_wrapper::WrappedAffinePoint;
use crate::plonk::circuit::allocated_num::*;
use crate::plonk::circuit::bigint::bigint::*;
use crate::plonk::circuit::bigint::field::*;
use crate::plonk::circuit::boolean::*;
use crate::plonk::circuit::curve::sw_affine::*;

use crate::bellman::pairing::{CurveAffine, CurveProjective, Engine};

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ConstraintSystem, PlonkConstraintSystemParams as NewCsParams, Variable,
};

use crate::bellman::plonk::better_better_cs::cs::PlonkConstraintSystemParams as CSParams;
use crate::bellman::plonk::better_better_cs::{proof::Proof, setup::VerificationKey};
use bellman::plonk::better_better_cs::cs::{
    Circuit, PlonkCsWidth4WithNextStepParams as PlonkCsParams,
};
use bellman::plonk::domains::Domain;
use plonk::circuit::verifier_circuit::data_structs::{
    add_points, add_scalar_field_elements, IntoLimbedCircuitWitness, IntoLimbedWitness,
};

pub struct ProofGadget<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub n: Option<usize>,
    pub inputs: Vec<AllocatedNum<E>>,
    pub state_polys_commitments: Vec<WP>,
    pub witness_polys_commitments: Vec<WP>,
    pub copy_permutation_grand_product_commitment: WP,

    pub quotient_poly_parts_commitments: Vec<WP>,

    pub state_polys_openings_at_z: Vec<AllocatedNum<E>>,
    pub state_polys_openings_at_dilations: Vec<AllocatedNum<E>>,
    pub witness_polys_openings_at_z: Vec<AllocatedNum<E>>,
    pub witness_polys_openings_at_dilations: Vec<AllocatedNum<E>>,

    pub gate_setup_openings_at_z: Vec<AllocatedNum<E>>,
    pub gate_selectors_openings_at_z: Vec<AllocatedNum<E>>,

    pub copy_permutation_polys_openings_at_z: Vec<AllocatedNum<E>>,
    pub copy_permutation_grand_product_opening_at_z_omega: AllocatedNum<E>,

    pub quotient_poly_opening_at_z: AllocatedNum<E>,

    pub linearization_poly_opening_at_z: AllocatedNum<E>,

    pub opening_proof_at_z: WP,
    pub opening_proof_at_z_omega: WP,

    _marker: &'a std::marker::PhantomData<()>,
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> ProofGadget<'a, E, WP> {
    pub fn alloc<CS: ConstraintSystem<E>, P: Circuit<E>, AD: AuxData<E>>(
        cs: &mut CS,
        proof: Proof<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {
        let inputs = proof
            .inputs
            .iter()
            .map(|x| AllocatedNum::alloc_input(cs, || Ok(*x)))
            .collect::<Result<Vec<_>, _>>()?;

        let state_polys_commitments = proof
            .state_polys_commitments
            .iter()
            .map(|x| WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data))
            .collect::<Result<Vec<_>, _>>()?;

        let copy_permutation_grand_product_commitment = WrappedAffinePoint::alloc(
            cs,
            Some(proof.copy_permutation_grand_product_commitment),
            params,
            aux_data,
        )?;

        let quotient_poly_parts_commitments = proof
            .quotient_poly_parts_commitments
            .iter()
            .map(|x| WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data))
            .collect::<Result<Vec<_>, _>>()?;

        let state_polys_openings_at_z = proof
            .state_polys_openings_at_z
            .iter()
            .map(|x| AllocatedNum::alloc(cs, || Ok(*x)))
            .collect::<Result<Vec<_>, _>>()?;

        let state_polys_openings_at_dilations = proof
            .state_polys_openings_at_dilations
            .iter()
            .map(|(_, _, x)| AllocatedNum::alloc(cs, || Ok(*x)))
            .collect::<Result<Vec<_>, _>>()?;

        let copy_permutation_grand_product_opening_at_z_omega = AllocatedNum::alloc(cs, || {
            Ok(proof.copy_permutation_grand_product_opening_at_z_omega)
        })?;
        let quotient_poly_opening_at_z =
            AllocatedNum::alloc(cs, || Ok(proof.quotient_poly_opening_at_z))?;
        let linearization_poly_opening_at_z =
            AllocatedNum::alloc(cs, || Ok(proof.linearization_poly_opening_at_z))?;

        let gate_selectors_openings_at_z = proof
            .gate_selectors_openings_at_z
            .iter()
            .map(|x| AllocatedNum::alloc(cs, || Ok(x.1)))
            .collect::<Result<Vec<_>, _>>()?;
        let copy_permutation_polys_openings_at_z = proof
            .copy_permutation_polys_openings_at_z
            .iter()
            .map(|x| AllocatedNum::alloc(cs, || Ok(*x)))
            .collect::<Result<Vec<_>, _>>()?;

        let opening_proof_at_z =
            WrappedAffinePoint::alloc(cs, Some(proof.opening_proof_at_z), params, aux_data)?;
        let opening_proof_at_z_omega =
            WrappedAffinePoint::alloc(cs, Some(proof.opening_proof_at_z_omega), params, aux_data)?;

        Ok(ProofGadget {
            n: Some(proof.n),
            inputs,
            state_polys_commitments,
            witness_polys_commitments: vec![],
            copy_permutation_grand_product_commitment,
            quotient_poly_parts_commitments,
            state_polys_openings_at_z,
            state_polys_openings_at_dilations,
            witness_polys_openings_at_z: vec![],
            witness_polys_openings_at_dilations: vec![],
            gate_setup_openings_at_z: vec![],
            gate_selectors_openings_at_z,
            copy_permutation_polys_openings_at_z,
            copy_permutation_grand_product_opening_at_z_omega,
            quotient_poly_opening_at_z,
            linearization_poly_opening_at_z,
            opening_proof_at_z,
            opening_proof_at_z_omega,
            _marker: &std::marker::PhantomData::<()>,
        })
    }

    pub fn alloc_from_witness<
        CS: ConstraintSystem<E>,
        C: Circuit<E>,
        P: CSParams<E>,
        AD: AuxData<E>,
    >(
        cs: &mut CS,
        num_inputs: usize,
        proof: &Option<Proof<E, C>>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {
        use crate::circuit::Assignment;

        let state_width = P::STATE_WIDTH;
        let num_quotient_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!P::HAS_CUSTOM_GATES);

        let mut inputs = vec![];
        for idx in 0..num_inputs {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.inputs))
                .and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            inputs.push(allocated);
        }

        let mut state_polys_commitments = vec![];
        for idx in 0..state_width {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.state_polys_commitments))
                .and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            state_polys_commitments.push(allocated);
        }

        let wit = proof
            .as_ref()
            .and_then(|el| Some(el.copy_permutation_grand_product_commitment));
        let copy_permutation_grand_product_commitment =
            WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let mut quotient_poly_parts_commitments = vec![];
        for idx in 0..num_quotient_commitments {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.quotient_poly_parts_commitments))
                .and_then(|el| Some(el[idx]));
            let allocated = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

            quotient_poly_parts_commitments.push(allocated);
        }

        let mut state_polys_openings_at_z = vec![];
        for idx in 0..state_width {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.state_polys_openings_at_z))
                .and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            state_polys_openings_at_z.push(allocated);
        }

        let mut state_polys_openings_at_dilations = vec![];
        for idx in 0..1 {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.state_polys_openings_at_dilations))
                .and_then(|el| Some(el[idx].2));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            state_polys_openings_at_dilations.push(allocated);
        }

        let mut gate_selectors_openings_at_z = vec![];
        for idx in 0..1 {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.gate_selectors_openings_at_z))
                .and_then(|el| Some(el[idx].1));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            gate_selectors_openings_at_z.push(allocated);
        }

        let wit = proof
            .as_ref()
            .and_then(|el| Some(el.copy_permutation_grand_product_opening_at_z_omega));
        let copy_permutation_grand_product_opening_at_z_omega =
            AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

        let wit = proof
            .as_ref()
            .and_then(|el| Some(el.quotient_poly_opening_at_z));
        let quotient_poly_opening_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

        let wit = proof
            .as_ref()
            .and_then(|el| Some(el.linearization_poly_opening_at_z));
        let linearization_poly_opening_at_z = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

        let mut copy_permutation_polys_openings_at_z = vec![];
        for idx in 0..(state_width - 1) {
            let wit = proof
                .as_ref()
                .and_then(|el| Some(&el.copy_permutation_polys_openings_at_z))
                .and_then(|el| Some(el[idx]));
            let allocated = AllocatedNum::alloc(cs, || Ok(*wit.get()?))?;

            copy_permutation_polys_openings_at_z.push(allocated);
        }

        let wit = proof.as_ref().and_then(|el| Some(el.opening_proof_at_z));
        let opening_proof_at_z = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        let wit = proof
            .as_ref()
            .and_then(|el| Some(el.opening_proof_at_z_omega));
        let opening_proof_at_z_omega = WrappedAffinePoint::alloc(cs, wit, params, aux_data)?;

        Ok(ProofGadget {
            n: None,
            inputs,
            state_polys_commitments,
            witness_polys_commitments: vec![],
            copy_permutation_grand_product_commitment,
            quotient_poly_parts_commitments,
            state_polys_openings_at_z,
            state_polys_openings_at_dilations,
            witness_polys_openings_at_z: vec![],
            witness_polys_openings_at_dilations: vec![],
            gate_setup_openings_at_z: vec![],
            gate_selectors_openings_at_z,
            copy_permutation_polys_openings_at_z,
            copy_permutation_grand_product_opening_at_z_omega,
            quotient_poly_opening_at_z,
            linearization_poly_opening_at_z,
            opening_proof_at_z,
            opening_proof_at_z_omega,
            _marker: &std::marker::PhantomData::<()>,
        })
    }
}

#[derive(Clone)]
pub struct VerificationKeyGagdet<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> {
    pub n: Option<usize>,
    pub domain_size_as_allocated_num: Option<AllocatedNum<E>>,
    pub omega_as_allocated_num: Option<AllocatedNum<E>>,
    pub num_inputs: usize,
    pub state_width: usize,

    pub gate_setup_commitments: Vec<WP>,
    pub gate_selectors_commitments: Vec<WP>,
    pub permutation_commitments: Vec<WP>,

    pub non_residues: Vec<E::Fr>,

    _m: &'a std::marker::PhantomData<()>,
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> VerificationKeyGagdet<'a, E, WP> {
    pub fn alloc<CS: ConstraintSystem<E>, P: Circuit<E>, AD: AuxData<E>>(
        cs: &mut CS,
        vk: VerificationKey<E, P>,
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {
        let gate_setup_commitments = vk
            .gate_setup_commitments
            .iter()
            .map(|x| WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data))
            .collect::<Result<Vec<_>, _>>()?;

        let gate_selectors_commitments = vk
            .gate_selectors_commitments
            .iter()
            .map(|x| WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data))
            .collect::<Result<Vec<_>, _>>()?;

        let permutation_commitments = vk
            .permutation_commitments
            .iter()
            .map(|x| WrappedAffinePoint::alloc(cs, Some(*x), params, aux_data))
            .collect::<Result<Vec<_>, _>>()?;

        let domain = Domain::<E::Fr>::new_for_size(vk.n as u64).unwrap();
        let omega_as_allocated_num = AllocatedNum::alloc(cs, || Ok(domain.generator))?;

        Ok(VerificationKeyGagdet {
            n: Some(vk.n),
            domain_size_as_allocated_num: None,
            omega_as_allocated_num: Some(omega_as_allocated_num),
            num_inputs: vk.num_inputs,
            state_width: vk.state_width,
            gate_setup_commitments,
            gate_selectors_commitments,
            permutation_commitments,
            non_residues: vk.non_residues,

            _m: &std::marker::PhantomData::<()>,
        })
    }

    pub fn alloc_from_limbs_witness<CS: ConstraintSystem<E>, P: CSParams<E>, AD: AuxData<E>>(
        cs: &mut CS,
        num_inputs: usize,
        domain_size: &AllocatedNum<E>,
        omega: &AllocatedNum<E>,
        witness: &[AllocatedNum<E>],
        params: &'a RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
        non_residues: Vec<E::Fr>,
        aux_data: &AD,
    ) -> Result<Self, SynthesisError> {
        let num_selector_commitments = P::STATE_WIDTH + 2;
        let num_next_step_selector_commitments = 1;

        let num_permutation_commitments = P::STATE_WIDTH;

        assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!P::HAS_CUSTOM_GATES);

        let mut w = witness;

        let mut gate_setup_commitments = vec![];
        for _ in 0..num_selector_commitments {
            let (point, rest) =
                WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            gate_setup_commitments.push(point);
        }

        let mut gate_selectors_commitments = vec![];
        for _ in 0..num_next_step_selector_commitments {
            let (point, rest) =
                WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            gate_selectors_commitments.push(point);
        }

        let mut permutation_commitments = vec![];
        for _ in 0..num_permutation_commitments {
            let (point, rest) =
                WrappedAffinePoint::from_allocated_limb_witness(cs, w, params, aux_data)?;

            w = rest;

            permutation_commitments.push(point);
        }

        assert_eq!(w.len(), 0, "must consume all the witness");

        Ok(VerificationKeyGagdet {
            n: None,
            domain_size_as_allocated_num: Some(domain_size.clone()),
            omega_as_allocated_num: Some(omega.clone()),
            num_inputs,
            state_width: 4,
            gate_setup_commitments,
            gate_selectors_commitments,
            permutation_commitments,
            non_residues,
            _m: &std::marker::PhantomData::<()>,
        })
    }
}

impl<E: Engine, C: Circuit<E>> IntoLimbedWitness<E> for VerificationKey<E, C> {
    fn witness_size_for_params(
        params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> usize {
        let mut base = 2;

        let per_coord = if params.can_allocate_from_double_limb_witness() {
            let mut num_witness = params.num_limbs_for_in_field_representation / 2;
            if params.num_limbs_for_in_field_representation % 2 != 0 {
                num_witness += 1;
            }
            num_witness
        } else {
            params.num_limbs_for_in_field_representation
        };

        // TODO zklink:deal new verification_key witness size
        let num_selector_commitments = <PlonkCsParams as NewCsParams<E>>::STATE_WIDTH + 3;
        let num_next_step_selector_commitments = 3;

        let num_permutation_commitments = <PlonkCsParams as NewCsParams<E>>::STATE_WIDTH;

        assert!(<PlonkCsParams as NewCsParams<E>>::CAN_ACCESS_NEXT_TRACE_STEP);
        assert!(!<PlonkCsParams as NewCsParams<E>>::HAS_CUSTOM_GATES);

        base += num_selector_commitments * 2 * per_coord;
        base += num_next_step_selector_commitments * 2 * per_coord;
        base += num_permutation_commitments * 2 * per_coord;

        base
    }

    fn into_witness_for_params(
        &self,
        params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Result<Vec<E::Fr>, SynthesisError> {
        use super::utils::new_verification_key_into_allocated_limb_witnesses;

        let as_limbs = new_verification_key_into_allocated_limb_witnesses(&self, params);

        Ok(as_limbs)
    }
}

impl<E: Engine, C: Circuit<E>> IntoLimbedWitness<E> for Proof<E, C> {
    fn witness_size_for_params(
        _params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> usize {
        unimplemented!();
        // let mut base = 2;

        // let per_coord = if params.can_allocate_from_double_limb_witness() {
        //     let mut num_witness = params.num_limbs_for_in_field_representation / 2;
        //     if params.num_limbs_for_in_field_representation % 2 != 0 {
        //         num_witness += 1;
        //     }

        //     num_witness
        // } else {
        //     params.num_limbs_for_in_field_representation
        // };

        // let num_selector_commitments = P::STATE_WIDTH + 2;
        // let num_next_step_selector_commitments = 1;

        // let num_permutation_commitments = P::STATE_WIDTH;

        // assert!(P::CAN_ACCESS_NEXT_TRACE_STEP);
        // assert!(!P::HAS_CUSTOM_GATES);

        // base += num_selector_commitments * 2 * per_coord;
        // base += num_next_step_selector_commitments * 2 * per_coord;
        // base += num_permutation_commitments * 2 * per_coord;

        // base
    }

    fn into_witness_for_params(
        &self,
        params: &RnsParameters<E, <E::G1Affine as CurveAffine>::Base>,
    ) -> Result<Vec<E::Fr>, SynthesisError> {
        use super::utils::new_proof_into_single_limb_witness;

        let as_limbs = new_proof_into_single_limb_witness(&self, params);

        Ok(as_limbs)
    }
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> IntoLimbedCircuitWitness<E>
    for ProofGadget<'a, E, WP>
{
    fn into_witness<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        let mut result = vec![];

        add_scalar_field_elements(&self.inputs, &mut result);
        add_points(&self.state_polys_commitments, &mut result);
        add_points(&self.witness_polys_commitments, &mut result);
        add_points(
            &[self.copy_permutation_grand_product_commitment.clone()],
            &mut result,
        );

        add_points(&self.quotient_poly_parts_commitments, &mut result);

        add_scalar_field_elements(&self.state_polys_openings_at_z, &mut result);
        add_scalar_field_elements(&self.state_polys_openings_at_dilations, &mut result);
        add_scalar_field_elements(&self.witness_polys_openings_at_z, &mut result);
        add_scalar_field_elements(&self.witness_polys_openings_at_dilations, &mut result);

        add_scalar_field_elements(&self.gate_setup_openings_at_z, &mut result);
        add_scalar_field_elements(&self.gate_selectors_openings_at_z, &mut result);

        add_scalar_field_elements(&self.copy_permutation_polys_openings_at_z, &mut result);
        add_scalar_field_elements(
            &[self
                .copy_permutation_grand_product_opening_at_z_omega
                .clone()],
            &mut result,
        );

        add_scalar_field_elements(&[self.quotient_poly_opening_at_z.clone()], &mut result);

        add_scalar_field_elements(&[self.linearization_poly_opening_at_z.clone()], &mut result);

        add_points(
            &[
                self.opening_proof_at_z.clone(),
                self.opening_proof_at_z_omega.clone(),
            ],
            &mut result,
        );

        Ok(result)
    }
}

impl<'a, E: Engine, WP: WrappedAffinePoint<'a, E>> IntoLimbedCircuitWitness<E>
    for VerificationKeyGagdet<'a, E, WP>
{
    fn into_witness<CS: ConstraintSystem<E>>(
        &self,
        _cs: &mut CS,
    ) -> Result<Vec<Num<E>>, SynthesisError> {
        assert!(
            self.domain_size_as_allocated_num.is_some(),
            "can only be called on a gadget with variable parameters"
        );
        assert!(
            self.omega_as_allocated_num.is_some(),
            "can only be called on a gadget with variable parameters"
        );

        let mut result = vec![];

        result.push(Num::Variable(
            self.domain_size_as_allocated_num.as_ref().unwrap().clone(),
        ));
        result.push(Num::Variable(
            self.omega_as_allocated_num.as_ref().unwrap().clone(),
        ));

        add_points(&self.gate_selectors_commitments, &mut result);
        add_points(&self.gate_setup_commitments, &mut result);
        add_points(&self.permutation_commitments, &mut result);

        Ok(result)
    }
}

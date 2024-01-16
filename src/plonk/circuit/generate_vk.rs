#![allow(dead_code)]

use crate::bellman::plonk::better_better_cs::{proof::Proof as BetterProof};
use crate::bellman::plonk::better_better_cs::setup::VerificationKey as BetterVerificationKey;
use crate::bellman::plonk::better_better_cs::cs::Circuit;
use crate::bellman::plonk::domains::Domain;
use crate::bellman::plonk::better_cs::cs::PlonkConstraintSystemParams as OldCSParams;
use crate::bellman::plonk::better_cs::keys::{Proof, VerificationKey};
use crate::bellman::pairing::{
    Engine,
    CurveAffine,
    ff::{PrimeField, PrimeFieldRepr}
};
use regex::Regex;
use std::fs::File;
use std::io::Write;

pub fn generate_vk_solidity<E:Engine,C:Circuit<E>>(vk:&BetterVerificationKey<E, C>,filename:&'static str){
    let mut template = String::from(VERIFICATION_KEY);

    let domain_size = Regex::new(r#"(<%domain_size%>)"#).unwrap();
    let num_inputs = Regex::new(r#"(<%num_inputs%>)"#).unwrap();
    let omega = Regex::new(r#"(<%omega%>)"#).unwrap();
    let gate_setup_commitments = Regex::new(r#"(<%gate_setup_commitments%>)"#).unwrap();
    let gate_selector_commitments = Regex::new(r#"(<%gate_selector_commitments%>)"#).unwrap();
    let non_residues = Regex::new(r#"(<%non_residues%>)"#).unwrap();
    let copy_permutation_commitments = Regex::new(r#"(<%copy_permutation_commitments%>)"#).unwrap();
    let g2_x = Regex::new(r#"(<%g2_x%>)"#).unwrap();

    template = domain_size.replace(template.as_str(), format!("{}",vk.n+1).as_str()).into_owned();
    template = num_inputs.replace(template.as_str(), format!("{}",vk.num_inputs).as_str()).into_owned();
    template = omega.replace(template.as_str(), compute_omega::<E>(vk.n as u64).as_str()).into_owned();

    for gate_setup_commitment in vk.gate_setup_commitments.iter(){
        let [x,y] = render_g1_affine_to_hex::<E>(gate_setup_commitment);
        template = gate_setup_commitments.replace(template.as_str(), x.as_str()).into_owned();
        template = gate_setup_commitments.replace(template.as_str(), y.as_str()).into_owned();
    }

    for permutation_commitment in vk.permutation_commitments.iter(){
        let [x,y] = render_g1_affine_to_hex::<E>(permutation_commitment);
        template = copy_permutation_commitments.replace(template.as_str(), x.as_str()).into_owned();
        template = copy_permutation_commitments.replace(template.as_str(), y.as_str()).into_owned();
    }

    for gate_selector_commitment in vk.gate_selectors_commitments.iter(){
        let [x,y] = render_g1_affine_to_hex::<E>(gate_selector_commitment);
        template = gate_selector_commitments.replace(template.as_str(), x.as_str()).into_owned();
        template = gate_selector_commitments.replace(template.as_str(), y.as_str()).into_owned();
    }

    for non_residue in vk.non_residues.iter(){
        template = non_residues.replace(template.as_str(), render_scalar_to_hex(non_residue).as_str()).into_owned();
    }

    let [x_c0,x_c1,y_c0,y_c1] = render_g2_affine_to_hex::<E>(&vk.g2_elements[1]);
    template = g2_x.replace(template.as_str(), x_c1.as_str()).into_owned();
    template = g2_x.replace(template.as_str(), x_c0.as_str()).into_owned();
    template = g2_x.replace(template.as_str(), y_c1.as_str()).into_owned();
    template = g2_x.replace(template.as_str(), y_c0.as_str()).into_owned();

    let mut fs = File::create(format!("./{}.sol",filename)).unwrap();
    fs.write_all(unsafe { template.as_bytes_mut() }).expect(&*format!("./generate {}.sol fail!", filename));
}

fn compute_omega<E:Engine>(domain_size:u64)-> String{
    let domain = Domain::<E::Fr>::new_for_size(domain_size).unwrap();
    format!("{}",domain.generator.into_repr())
}


fn render_scalar_to_hex<F: PrimeField>(el: &F) -> String {
    let mut buff = vec![];
    let repr = el.into_repr();
    repr.write_be(&mut buff).unwrap();

    format!("0x{}", hex::encode(buff))
}

fn render_g1_affine_to_hex<E: Engine>(point: &E::G1Affine) -> [String; 2] {
    if point.is_zero() {
        return ["0x0".to_owned(), "0x0".to_owned()];
    }

    let (x, y) = point.into_xy_unchecked();
    [render_scalar_to_hex(&x), render_scalar_to_hex(&y)]
}

fn render_g2_affine_to_hex<E:Engine>(point: &E::G2Affine) -> [String; 4] {
    if point.is_zero() {
        return [
            "0x0".to_owned(),
            "0x0".to_owned(),
            "0x0".to_owned(),
            "0x0".to_owned(),
        ];
    }

    let (x, y) = point.into_xy_unchecked();

    [
        // render_scalar_to_hex(&x.c0),
        // render_scalar_to_hex(&x.c1),
        // render_scalar_to_hex(&y.c0),
        // render_scalar_to_hex(&y.c1),
        format!("{}",x),
        format!("{}",x),
        format!("{}",y),
        format!("{}",y),
    ]
}

fn print_g1<E:Engine>(g1:&E::G1Affine) {
    let (x, y) = g1.into_xy_unchecked();
    println!("{}\n{}", render_scalar_to_hex(&x),  render_scalar_to_hex(&y));
}
fn print_g1_vec<E:Engine>(v:&[E::G1Affine]){
    v.iter().for_each(|p| print_g1::<E>(p));
}
fn print_fr<E:Engine>(fr:&E::Fr){
    let mut fr_be = Vec::with_capacity(32);
    let repr = fr.into_repr();
    repr.write_be(&mut fr_be).unwrap();
    println!("0x{}", hex::encode(fr_be));
}
fn print_fr_vec<E:Engine>(v:&[E::Fr]){
    v.iter().for_each(|p| print_fr::<E>(p))
}

pub fn print_old_proof<E: Engine, C: OldCSParams<E>>(proof:&Proof<E,C>){
    println!("\n******************************************************************************************************");
    print_fr_vec::<E>(&proof.input_values);
    print_g1_vec::<E>(&proof.wire_commitments);
    print_g1::<E>(&proof.grand_product_commitment);
    print_g1_vec::<E>(&proof.quotient_poly_commitments);
    print_fr_vec::<E>(&proof.wire_values_at_z);
    proof.wire_values_at_z_omega.iter().for_each(|f| print_fr::<E>(f));
    print_fr::<E>(&proof.grand_product_at_z_omega);
    print_fr::<E>(&proof.quotient_polynomial_at_z);
    print_fr::<E>(&proof.linearization_polynomial_at_z);
    print_fr_vec::<E>(&proof.permutation_polynomials_at_z);
    print_g1::<E>(&proof.opening_at_z_proof);
    print_g1::<E>(&proof.opening_at_z_omega_proof);
}
pub fn print_proof<E: Engine, C: Circuit<E>>(proof: &BetterProof<E, C>){
    // according to solidity deserialized format , print all hex
    println!("\n******************************************************************************************************");
    print_fr_vec::<E>(&proof.inputs);
    print_g1_vec::<E>(&proof.state_polys_commitments);
    print_g1::<E>(&proof.copy_permutation_grand_product_commitment);
    print_g1_vec::<E>(&proof.quotient_poly_parts_commitments);
    print_fr_vec::<E>(&proof.state_polys_openings_at_z);
    proof.state_polys_openings_at_dilations.iter().for_each(|(_,_,f)| print_fr::<E>(f));
    proof.gate_selectors_openings_at_z.iter().for_each(|(_,f)| print_fr::<E>(f));
    print_fr_vec::<E>(&proof.copy_permutation_polys_openings_at_z);
    print_fr::<E>(&proof.copy_permutation_grand_product_opening_at_z_omega);
    print_fr::<E>(&proof.quotient_poly_opening_at_z);
    print_fr::<E>(&proof.linearization_poly_opening_at_z);
    print_g1::<E>(&proof.opening_proof_at_z);
    print_g1::<E>(&proof.opening_proof_at_z_omega);

    //according to solidity deserialized format order
    println!("\n******************************************************************************************************");
    println!("proof.n:{}", proof.n);
    println!("proof.input:{:?}", proof.inputs);
    println!("proof.state_polys_commitments:{:?}", proof.state_polys_commitments);
    println!("proof.copy_permutation_grand_product_commitment:{:?}", proof.copy_permutation_grand_product_commitment);
    println!("proof.quotient_poly_parts_commitments:{:?}", proof.quotient_poly_parts_commitments);
    println!("proof.state_polys_openings_at_z:{:?}", proof.state_polys_openings_at_z);
    println!("proof.state_polys_openings_at_dilations:{:?}", proof.state_polys_openings_at_dilations);
    println!("proof.gate_selectors_openings_at_z:{:?}", proof.gate_selectors_openings_at_z);
    println!("proof.copy_permutation_polys_openings_at_z:{:?}", proof.copy_permutation_polys_openings_at_z);
    println!("proof.copy_permutation_grand_product_opening_at_z_omega:{:?}", proof.copy_permutation_grand_product_opening_at_z_omega);
    println!("proof.quotient_poly_opening_at_z:{:?}", proof.quotient_poly_opening_at_z);
    println!("proof.linearization_poly_opening_at_z:{:?}", proof.linearization_poly_opening_at_z);
    println!("proof.opening_proof_at_z:{:?}", proof.opening_proof_at_z);
    println!("proof.opening_proof_at_z_omega:{:?}", proof.opening_proof_at_z_omega);

    // field about lookup
    println!("\n*****************************************************************************************");
    println!("proof.witness_polys_openings_at_z:{:?}", proof.witness_polys_openings_at_z);
    println!("proof.witness_polys_openings_at_dilations:{:?}", proof.witness_polys_openings_at_dilations);
    println!("proof.lookup_s_poly_commitment:{:?}", proof.lookup_s_poly_commitment);
    println!("proof.lookup_grand_product_commitment:{:?}", proof.lookup_grand_product_commitment);
    println!("proof.lookup_s_poly_opening_at_z_omega:{:?}", proof.lookup_s_poly_opening_at_z_omega);
    println!("proof.lookup_grand_product_opening_at_z_omega:{:?}", proof.lookup_grand_product_opening_at_z_omega);
    println!("proof.lookup_t_poly_opening_at_z:{:?}", proof.lookup_t_poly_opening_at_z);
    println!("proof.lookup_t_poly_opening_at_z_omega:{:?}", proof.lookup_t_poly_opening_at_z_omega);
    println!("proof.lookup_selector_poly_opening_at_z:{:?}", proof.lookup_selector_poly_opening_at_z);
    println!("proof.lookup_table_type_poly_opening_at_z:{:?}", proof.lookup_table_type_poly_opening_at_z);
}
pub fn print_old_verification_key<E: Engine, C: OldCSParams<E>>(vk:&VerificationKey<E, C>){
    println!("\n******************************************************************************************************");
    println!("vk.n:{}", vk.n);
    println!("vk.num_inputs:{}", vk.num_inputs);
    println!("vk.selector_commitments:{:?}", &vk.selector_commitments);
    println!("vk.next_step_selector_commitments:{:?}", &vk.next_step_selector_commitments);
    println!("vk.permutation_commitments:{:?}", &vk.permutation_commitments);
    println!("vk.non_residues:{:?}", &vk.non_residues);
    println!("vk.g2_elements:{:?}", &vk.g2_elements);
}
pub fn print_verification_key<E: Engine, C: Circuit<E>>(vk:&BetterVerificationKey<E, C>){
    println!("\n******************************************************************************************************");
    println!("vk.n:{}", vk.n);
    println!("vk.num_inputs:{}", vk.num_inputs);
    println!("vk.state_width:{}", vk.state_width);
    println!("vk.num_witness_polys:{}", vk.num_witness_polys);
    println!("vk.gate_setup_commitments:{:?}", &vk.gate_setup_commitments);
    println!("vk.gate_selectors_commitments:{:?}", &vk.gate_selectors_commitments);
    println!("vk.permutation_commitments:{:?}", &vk.permutation_commitments);
    println!("vk.non_residues:{:?}", &vk.non_residues);
    println!("vk.g2_elements:{:?}", &vk.g2_elements);

    println!("\n******************************************************************************************************");
    println!("vk.total_lookup_entries_length:{}",vk.total_lookup_entries_length);
    println!("vk.lookup_selector_commitment:{:?}",vk.lookup_selector_commitment);
    println!("vk.lookup_tables_commitments:{:?}",vk.lookup_tables_commitments);
    println!("vk.lookup_table_type_commitment:{:?}",vk.lookup_table_type_commitment);
}

static VERIFICATION_KEY:&str = r#"
function getZkBankVk() internal pure returns(VerificationKey memory vk) {
        vk.domain_size = <%domain_size%>;
        vk.num_inputs = <%num_inputs%>;
        vk.omega = PairingsBn254.new_fr(<%omega%>);
        vk.gate_setup_commitments[0] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[1] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[2] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[3] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[4] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[5] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );
        vk.gate_setup_commitments[6] = PairingsBn254.new_g1(
            <%gate_setup_commitments%>,
            <%gate_setup_commitments%>
        );

        vk.gate_selector_commitments[0] = PairingsBn254.new_g1(
            <%gate_selector_commitments%>,
            <%gate_selector_commitments%>
        );
        vk.gate_selector_commitments[1] = PairingsBn254.new_g1(
            <%gate_selector_commitments%>,
            <%gate_selector_commitments%>
        );

        vk.copy_permutation_commitments[0] = PairingsBn254.new_g1(
            <%copy_permutation_commitments%>,
            <%copy_permutation_commitments%>
        );
        vk.copy_permutation_commitments[1] = PairingsBn254.new_g1(
            <%copy_permutation_commitments%>,
            <%copy_permutation_commitments%>
        );
        vk.copy_permutation_commitments[2] = PairingsBn254.new_g1(
            <%copy_permutation_commitments%>,
            <%copy_permutation_commitments%>
        );
        vk.copy_permutation_commitments[3] = PairingsBn254.new_g1(
            <%copy_permutation_commitments%>,
            <%copy_permutation_commitments%>
        );

        vk.copy_permutation_non_residues[0] = PairingsBn254.new_fr(
            <%non_residues%>
        );
        vk.copy_permutation_non_residues[1] = PairingsBn254.new_fr(
            <%non_residues%>
        );
        vk.copy_permutation_non_residues[2] = PairingsBn254.new_fr(
            <%non_residues%>
        );

        vk.g2_x = PairingsBn254.new_g2(
            [<%g2_x%>,
            <%g2_x%>],
            [<%g2_x%>,
            <%g2_x%>]
        );
    }
"#;
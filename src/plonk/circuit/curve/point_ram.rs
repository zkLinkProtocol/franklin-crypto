use super::super::permutation_network::*;

use std::collections::HashMap;
use num_traits::Zero;
use plonk::circuit::boolean::Boolean;
use num_bigint::BigUint;
use plonk::circuit::curve::AffinePoint;
use plonk::circuit::allocated_num::Num;
use plonk::circuit::bigint::FieldElement;
use plonk::circuit::SynthesisError;
use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};
use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use super::super::allocated_num::{AllocatedNum};
use super::super::linear_combination::LinearCombination;
use plonk::circuit::bigint::RnsParameters;
use std::cell::RefCell;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable,
    Width4MainGateWithDNext,
};
use plonk::circuit::bigint::fe_to_biguint;

pub fn can_not_be_false_if_flagged<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    condition: &Boolean,
    condition_must_be_valid: &Boolean,
) -> Result<(), SynthesisError> {
    // only forbidden combination is condition is false and condition_must_be_valid == true
    match (condition.get_value(), condition_must_be_valid.get_value()) {
        (Some(c), Some(f)) => {
            let valid = if f {
                c
            } else {
                true
            };
            assert!(valid, "condition is broken: condition = {}, while enforcing flag = {}", c, f);
        },
        _ => {}
    }

    // TODO: we can trivially optimize here
    let invalid = Boolean::and(cs, &condition.not(), &condition_must_be_valid)?;
    Boolean::enforce_equal(cs, &invalid, &Boolean::constant(false))?;

    Ok(())
}
#[derive(Clone, Debug)]
pub struct Memory<'a, E: Engine, G: GenericCurveAffine> 
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub block: Vec<(Num<E>, AffinePoint<'a, E, G>)>,

    pub witness_map: HashMap<BigUint , RefCell<AffinePoint<'a, E, G>>>

}

impl<'a, E: Engine, G: GenericCurveAffine> Memory<'a, E, G>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub fn new() -> Self{
        Self {
            block: vec![],
            witness_map: HashMap::new()
        }
    }
    pub fn read_and_alloc<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, addr: Num<E>, params: &'a RnsParameters<E, G::Base>) -> Result<RefCell<AffinePoint<'a, E, G>>, SynthesisError>{

        let addres = fe_to_biguint(&addr.get_value().unwrap());

        let existing = self.witness_map.get(&addres).unwrap().clone();
        let witness_alloc = AffinePoint::alloc(cs, existing.clone().into_inner().value.clone(), params).unwrap();

        self.block.push((addr, witness_alloc));

        Ok(existing)
    }

    pub fn insert_witness(&mut self, addr: Num<E>, point: AffinePoint<'a, E, G>){
        let addres = fe_to_biguint(&addr.get_value().unwrap());
        let value = RefCell::new(point);
        self.witness_map.insert(addres, value);
    }


    pub fn waksman_permutation<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>{

        let size = self.block.len();
        let permutation = Self::calculate_permutation(&self.block);
        let permutation = if let Some(permutation) = permutation {
            permutation
        } else {
            IntegerPermutation::new(size)
        };

        let switches = order_into_switches_set(cs, &permutation)?;

        let mut total_num_switches = 0;
        for layer in switches.iter() {
            total_num_switches += layer.len();
        }

        use plonk::circuit::bigint_new::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut original_values = vec![];
        let mut original_indexes = vec![];
        // let mut original_addres = vec![];

        let mut sorted_values = vec![];
        let mut sorted_indexes = vec![];
        // let mut original_addres = vec![];
        

        let mut packed_original_values = vec![];
        let mut packed_sorted_values = vec![];


        for (addr, value ) in self.block.iter() {

            let value = value.clone();
            let x = FieldElement::into_limbs(value.clone().x.clone());

            let chunk = value.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }
            let (odd_y, y) = value.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;

            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_original_values.push([value_low, value_high]);
            original_values.push(value);
            original_indexes.push(addr);

        }

        for index in permutation.elements.iter() {

            let value = original_values[*index].clone();
            let addr = original_indexes[*index].clone();
            sorted_values.push(value.x.clone());
            sorted_indexes.push(addr.clone());

            let value = value.clone();
            let y = FieldElement::into_limbs(value.clone().y.clone());
            let x = FieldElement::into_limbs(value.clone().x.clone());

            let chunk = value.x.representation_params.binary_limbs_bit_widths[0];
            let iter = value.x.representation_params.binary_limbs_bit_widths.clone().into_iter();
            
            let chunk_x = 253 / chunk;
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..chunk_x{
                lc_low.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();

            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for l in chunk_x..x.len(){
                lc_high.add_assign_number_with_coeff(&x[l].num, shifts[i]);
                i+= iter.clone().next().unwrap();
            }

            let (odd_y, y) = value.clone().point_compression(cs)?;
            lc_high.add_assign_boolean_with_coeff(&odd_y, shifts[i]);  // point compression
            i+= 1;

            lc_high.add_assign_number_with_coeff(&addr, shifts[i]);

            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_sorted_values.push([value_low, value_high]);

        }
        let o0: Vec<_> = packed_original_values.iter().map(|el| el[0]).collect();
        let o1: Vec<_> = packed_original_values.into_iter().map(|el| el[1]).collect();
        let s0: Vec<_> = packed_sorted_values.iter().map(|el| el[0]).collect();
        let s1: Vec<_> = packed_sorted_values.into_iter().map(|el| el[1]).collect();

        prove_permutation_using_switches_witness(
            cs, 
            &s0,
            &o0,
            &switches
        )?;

        prove_permutation_using_switches_witness(
            cs, 
            &s1,
            &o1,
            &switches
        )?;

        let mut value_addr_iter = sorted_values.into_iter().zip(sorted_indexes.into_iter());
        let (value, addr) = value_addr_iter.next().unwrap();
        let (is_zero, _) = value.clone().is_zero(cs)?;
        can_not_be_false_if_flagged(cs, &is_zero, &Boolean::constant(true))?;
        let mut pre_value = value.clone();
        let mut pre_addr = addr.clone();

        for (value, addr) in value_addr_iter{
            
            let (unchanged, _) = FieldElement::equals(cs, value.clone(), pre_value)?;
            let is_zero = value.clone().is_zero(cs)?;

            let borrow = pre_addr.sub(cs, &addr)?;

            let is_zero_addr = borrow.is_zero(cs)?;

            can_not_be_false_if_flagged(cs, &unchanged, &is_zero_addr)?;

            pre_value = value;
            pre_addr = addr;

        }

        Ok(())

    }

    fn calculate_permutation(row: &Vec<(Num<E>, AffinePoint<'a, E, G>)>) -> Option<IntegerPermutation> {
        
        let mut keys = vec![];
        for (addr, _) in row.iter() {
            let addres = fe_to_biguint(&addr.get_value().unwrap());
            let idx = keys.len();
            keys.push((idx, addres));
        }

        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();

        let integer_permutation = IntegerPermutation::new_from_permutation(integer_permutation);

        Some(integer_permutation)
    }





} 

mod test {
    use super::*;

    use crate::bellman::pairing::bn256::{Bn256, Fq, Fr, G1Affine};
    use crate::plonk::circuit::*;
    use plonk::circuit::tables::inscribe_combined_bitwise_ops_and_range_table;

    #[test]
    fn test_ram() {
        
        use rand::{Rng, SeedableRng, XorShiftRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);

        let mut ram = Memory::new();
        let mut vec_verif = vec![];
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, Width4MainGateWithDNext>::new();
        inscribe_combined_bitwise_ops_and_range_table(&mut cs, 8);
        let mut array_addr = vec![];
        for i in 0..100 {

            let a_f: G1Affine = rng.gen();
            let a_fr: Fr = rng.gen();

            let a = AffinePoint::alloc(&mut cs, Some(a_f), &params).unwrap();
            let num_adr =Num::alloc(&mut cs, Some(a_fr)).unwrap();
            array_addr.push(num_adr);


            vec_verif.push(a.clone());

            ram.block.push((num_adr, a.clone()));
            let biguint = fe_to_biguint(&a_fr);
            ram.witness_map.insert(biguint, RefCell::new(a.clone())); 
        }
        for j in 0..100{
            let addres = array_addr[j];
            
            let point = ram.read_and_alloc(&mut cs, addres, &params).unwrap();
            // assert_eq!(vec_verif[j].value.unwrap(), point.value.unwrap());

            
        }

        ram.waksman_permutation(&mut cs);



    }
}
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

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms,
    MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable,
    Width4MainGateWithDNext,
};

pub struct Memory<'a, E: Engine, G: GenericCurveAffine> 
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub block: Vec<(u64, Boolean, u64, AffinePoint<'a, E, G>)>,

    pub witness_map: HashMap<u64 ,AffinePoint<'a, E, G>>

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
    pub fn read_or_write<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, flag: Boolean, count: u64, addr: u64, value: AffinePoint<'a, E, G>){
        match (flag.get_value(), addr, value.clone()) {
            (Some(flag), addr, value) => {
                if flag {
                    self.witness_map.insert(addr, value.clone());
                } else {
                    if let existing = self.witness_map.get(&addr).unwrap().clone() {
                        let (a, _) = AffinePoint::equals(cs, existing, value.clone()).unwrap();
                        assert_eq!(a.get_value().unwrap(), true)
                    }
                }
            },
            _ => {}
        }
        
        self.block.push((count, flag, addr, value ))
    }

    pub fn get_witness(&self, addr: u64) -> AffinePoint<'a, E, G>
    {
        let witness = self.witness_map.get(&addr).unwrap();

        witness.clone()
    }

    pub fn insert_witness(&mut self, addr: u64, point: AffinePoint<'a, E, G>){
        self.witness_map.insert(addr, point);
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

        use plonk::circuit::bigint::compute_shifts;
        let shifts = compute_shifts::<E::Fr>();
        let mut original_values = vec![];
        let mut sorted_values = vec![];

        let mut packed_original_values = vec![];
        let mut packed_sorted_values = vec![];


        for (idx, flag, addr, value ) in self.block.iter() {

            let value = value.clone();
            let y = FieldElement::into_limbs(value.y.clone());
            let step = 256 / y.len();
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..y.len()/2{
                lc_low.add_assign_number_with_coeff(&y[l].num, shifts[i]);
                i+= step;
            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for m in y.len()/2..y.len(){
                lc_high.add_assign_number_with_coeff(&y[m].num, shifts[i]);
                i+= step;
            }
            let value_high = lc_high.into_num(cs)?.get_variable();

            packed_original_values.push([value_low, value_high]);
            original_values.push(value);

        }

        for index in permutation.elements.iter() {

            let value_other = original_values[*index].clone();
            sorted_values.push(value_other.clone());

            let y = FieldElement::into_limbs(value_other.y.clone());
            let step = 256 / y.len();
            let mut i = 0;
            let mut lc_low = LinearCombination::zero(); 
            for l in 0..y.len()/2{
                lc_low.add_assign_number_with_coeff(&y[l].num, shifts[i]);
                i+= step;
            }
            let value_low = lc_low.into_num(cs)?.get_variable();
            i=0;

            let mut lc_high = LinearCombination::zero();
            for m in y.len()/2..y.len(){
                lc_high.add_assign_number_with_coeff(&y[m].num, shifts[i]);
                i+= step;
            }
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


        Ok(())

    }

    fn calculate_permutation(row: &Vec<(u64, Boolean, u64, AffinePoint<'a, E, G>)>) -> Option<IntegerPermutation> {
        
        let mut keys = vec![];
        for (id, _, addr, _) in row.iter() {
            let composite_key = *id as usize + *addr as usize;
            let idx = keys.len();
            keys.push((idx, composite_key));
        }

        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();

        let integer_permutation = IntegerPermutation::new_from_permutation(integer_permutation);

        Some(integer_permutation)
    }





} 
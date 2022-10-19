use super::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;
use crate::bellman::pairing::ff::{
    Field, PrimeField, PrimeFieldRepr, BitIterator, ScalarEngine
};
use crate::bellman::GenericCurveAffine;
use crate::bellman::GenericCurveProjective;
use crate::plonk::circuit::bigint::biguint_to_fe;
use crate::plonk::circuit::bigint::fe_to_biguint;
use crate::plonk::circuit::bigint::split_into_fixed_number_of_limbs;
use crate::plonk::circuit::utils::u64_to_fe;
use plonk::circuit::bigint_new::Extension2Params;

pub(crate) const GEN_SCALAR_MUL_TABLE_NAME: &'static str = "generator by scalar mul table";

// A table for storing a AffinePoint from a generator with using endomorphism.
// Create a table of the view:
// Point: k*P = k0*P + k1*Q where Q = lambda*P
// note that both k1 and k2 be of both signs: both positive and negative
// the raw of the table is of the form:
// prefix || k1 || k0 | limb_0 | limb_1
// where prefix is combination of four flags: select_y_limbs | limb_idx_selector | sign_k1 | sign_k0
// in total the first column is of the form: 
// select_y_limbs | limb_idx_selector | sign_k1 | sign_k0 | k1 | k0
#[derive(Clone)]
pub struct GeneratorScalarMulTable<E: Engine>
{
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    table_len: usize, 
    name: &'static str,
}

impl<E: Engine> GeneratorScalarMulTable<E>
{
    pub fn new<G: GenericCurveAffine, T: Extension2Params<G::Base>>(
        window: usize, name: &'static str, params: &CurveCircuitParameters<E, G, T>
    ) -> Self 
    where <G as GenericCurveAffine>::Base: PrimeField 
    {   
        let binary_limb_width =  params.base_field_rns_params.binary_limb_width;      
        let num_of_limbs = params.base_field_rns_params.num_binary_limbs;
        let num_elems_in_window = (2 as u64).pow(window as u32) as usize;
        assert_eq!(num_of_limbs % 2, 0);
        let num_of_limb_idxs = (num_of_limbs + 1) / 2;
        let btilen_of_limb_sel = crate::log2_floor(num_of_limb_idxs);
        let table_len = num_elems_in_window * num_elems_in_window * 8 * num_of_limb_idxs;
       
        let mut column0 = Vec::with_capacity(table_len);
        let mut column1 = Vec::with_capacity(table_len);
        let mut column2 = Vec::with_capacity(table_len);
        let mut map = std::collections::HashMap::with_capacity(table_len);

        let generator = G::one();
        let generator_endo = {
            let (mut x, y) = generator.clone().into_xy_unchecked();
            x.mul_assign(&params.beta); 
            G::from_xy_checked(x, y).expect("should be a valid point")
        };
        let mut generator_negated = generator.clone();
        generator_negated.negate();
        let mut generator_endo_negated = generator_endo.clone();
        generator_endo_negated.negate(); 
        let aux_prefix_offset = 2 * window + 2;

        let skew_mul = |point: &G, point_negated: &G, scalar: usize| -> G::Projective {
            // treat raw address is skew-represented address:
            // 1 -> G, 0 -> - G
            let mut acc = G::Projective::zero();
            for i in (0..window).rev() {
                acc.double();
                let bit = (scalar >> i) & 1 != 0;
                let tmp = if bit { &point } else { &point_negated }; 
                acc.add_assign_mixed(&tmp);
            }
            acc
        };

        let split_into_limbs = |fr: G::Base| -> Vec<E::Fr> {
            let fr_as_biguint = fe_to_biguint(&fr);
            let mut chunks = split_into_fixed_number_of_limbs(fr_as_biguint, binary_limb_width, num_of_limbs);
            chunks.drain(..).map(|x| biguint_to_fe(x)).collect()
        };

        for (k0, k1, k0_is_neg, k1_is_neg) in itertools::iproduct!(
            0..num_elems_in_window, 0..num_elems_in_window, // k0 and k1
            std::iter::once(false).chain(std::iter::once(true)), // k0 is negative
            std::iter::once(false).chain(std::iter::once(true)) //k1 is negative
        ) {
            let (point, point_negated) = if k0_is_neg { 
                (&generator_negated, &generator) 
            } else {
                (&generator, &generator_negated)
            };
            let gen_mul_k0 = skew_mul(point, point_negated, k0);  
            
            let (point, point_negated) = if k1_is_neg { 
                (&generator_endo_negated, &generator_endo) 
            } else {
                (&generator_endo, &generator_endo_negated)
            };
            let gen_mul_k1 = skew_mul(point, point_negated, k1);
            
            let mut tmp = gen_mul_k0;
            tmp.add_assign(&gen_mul_k1);
            let point = tmp.into_affine();
            let (x, y) = point.into_xy_unchecked();
            let x_limbs = split_into_limbs(x);
            let y_limbs = split_into_limbs(y);

            let base_prefix = (k0_is_neg as usize) + (k1_is_neg as usize) * 2;
            let base = k0 + (k1 << window) + (base_prefix << ( 2 * window));
            
            let iter = x_limbs.chunks(2).zip(std::iter::repeat(0)).enumerate().chain(
                y_limbs.chunks(2).zip(std::iter::repeat(1)).enumerate()
            );
            for (idx, (limbs, x_y_selector)) in iter {
                let aux_prefix = (idx + (x_y_selector << btilen_of_limb_sel)) << aux_prefix_offset;
                let elem0 = u64_to_fe((base + aux_prefix) as u64);
                let elem1 = limbs[0];
                let elem2 = limbs[1];
                
                column0.push(elem0);
                column1.push(elem1); 
                column2.push(elem2); 
                map.insert(elem0, (elem1, elem2));
            }
        }
        assert_eq!(column0.len(), table_len);

        Self { 
            table_entries: [column0, column1, column2],
            table_lookup_map: map, 
            table_len,
            name
        }

    }
}

impl<E: Engine> std::fmt::Debug for GeneratorScalarMulTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GeneratorScalarMulTable").finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for GeneratorScalarMulTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }

    fn table_size(&self) -> usize {
        self.table_len
    }

    fn num_keys(&self) -> usize {
        1
    }

    fn num_values(&self) -> usize {
        2
    }

    fn allows_combining(&self) -> bool {
        true
    }

    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }

    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }

    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }

    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }

    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}




use super::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::SynthesisError;
use crate::bellman::Engine;
use crate::plonk::circuit::bigint_new::fe_to_biguint;
use bellman::GenericCurveAffine;
use plonk::circuit::bigint::RnsParameters;
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
};
use bellman::bn256::Fr;
use bellman::GenericCurveProjective;
use plonk::circuit::bigint::FieldElement;
use plonk::circuit::curve::endomorphism::EndomorphismParameters;
use itertools::Itertools;


// A table for storing a AffinePoint from a generator with using endomorphism.
// Create a table of the view:
// Point: k*P = k1*P + k2*Q where Q = lambda*P
// for each combination of scalar_1, scalar_2 in the window, the table would contain the following block:
// prefix running in the ange 0..7 (assuming that standard decomposition of FieldElement occupies 4 chunks)
// ___________________________________________
// |  000 || scalar_1 | scalar_2 | limb_x_0  |
// |  001 || scalar_1 | scalar_2 | limb_x_1  |
// |  010 || scalar_1 | scalar_2 | limb_x_2  |
// |  011 || scalar_1 | scalar_2 | limb_x_3  |
// |  100 || scalar_1 | scalar_2 | limb_y_0  |
// |  101 || scalar_1 | scalar_2 | limb_y_1  |
// |  110 || scalar_1 | scalar_2 | limb_y_2  |
// |  111 || scalar_1 | scalar_2 | limb_y_3  |
// |    .   .   .   .   .   .   .   .   .   .|
// |_________________________________________|
// #[derive(Clone)]
// pub struct GeneratorScalarMulTable<E: Engine>{
//     pub table_entries: [Vec<E::Fr>; 3],
//     table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
//     table_len: usize, 
//     name: &'static str,
// }

// impl<E: Engine> GeneratorScalarMulTable<E>{
//     pub fn new<'a>(
//         window: usize, name: &'static str,  
//         circuit_params: EndomorphismParameters<E>
//     ) -> Self {
//         // the size of the table will be the number of points 2^w * 2 * num_of_limbs;          
//         let num_of_limbs = params.num_binary_limbs;
//         let num_elems_in_window = (2 as u64).pow(window as u32) as usize;
//         let table_len = num_elems_in_window * num_elems_in_window * num_of_limbs * 2;
       
//         let mut column0 = Vec::with_capacity(table_len);
//         let mut column1 = Vec::with_capacity(table_len);
//         let mut column2 = Vec::with_capacity(table_len);
//         let mut map = std::collections::HashMap::with_capacity(table_len);
 
//         let generator = E::G1Affine::one();
//         let generator_endo = ...;

//         let scalar_mul 

//         for (scalar_1, scalar_2) in (0..num_elems_in_window).zip(0..num_elems_in_window) {
//             // for the key we calculate a constant in the binary representation. 
//             // However, we will count the scalar for the point in the skew representation
//             // Example: 0 1 01 11 100       if  window-3 000, 001, 011  --- bin rep
//             // Example: number3 –– 011 ------ 1  skew 111 -7       

//             // this scalar_num calculate for the constant by which we will multiply the point
//             let (_, scalar_num_1) = vec_of_bit(i, window);
//             // sigh of scalar
//             let a = i64::abs(scalar_num_1);
//             let diff = scalar_num_1 - a;
//             let unsign_nuber = i64::abs(scalar_num_1);
//             // scalar || 000
//             let scalar_x_low_0 = E::Fr::from_str(&format!("{}", (i*8))).unwrap(); 
//             // scalar || 001
//             let scalar_x_low_1= E::Fr::from_str(&format!("{}", (i*8+1))).unwrap(); 
//             // scalar || 010
//             let scalar_x_high_0 = E::Fr::from_str(&format!("{}", (i*8+2))).unwrap();
//             // scalar || 011
//             let scalar_x_high_1 = E::Fr::from_str(&format!("{}", (i*8+3))).unwrap();
//             // scalar || 100 
//             let scalar_y_low_0 = E::Fr::from_str(&format!("{}", (i*8+4))).unwrap(); 
//             // scalar || 101
//             let scalar_y_low_1 = E::Fr::from_str(&format!("{}", (i*8+5))).unwrap();
//             // scalar || 110 
//             let scalar_y_high_0 = E::Fr::from_str(&format!("{}", (i*8+6))).unwrap();
//             // scalar || 111
//             let scalar_y_high_1 = E::Fr::from_str(&format!("{}", (i*8+7))).unwrap();

//             for j in 0..bit_window{

//                 let (_, scalar_num_2) = vec_of_bit(j, window);
//                 // sigh of scalar
//                 let a = i64::abs(scalar_num_2);
//                 let diff_2 = scalar_num_2 - a;
//                 let unsign_nuber_2 = i64::abs(scalar_num_2);

//                 let scalar2 = E::Fr::from_str(&format!("{}", j)).unwrap(); 

//                 column0.push(scalar_x_low_0);
//                 column0.push(scalar_x_low_1);
//                 column0.push(scalar_x_high_0);
//                 column0.push(scalar_x_high_1);
    
//                 column0.push(scalar_y_low_0);
//                 column0.push(scalar_y_low_1);
//                 column0.push(scalar_y_high_0);
//                 column0.push(scalar_y_high_1);

//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);
//                 column1.push(scalar2);

//                 let scalar_for_p = <E::G1Affine as GenericCurveAffine>::Scalar::from_str(&format!("{}", unsign_nuber)).unwrap();
//                 let scalar_for_q = <E::G1Affine as GenericCurveAffine>::Scalar::from_str(&format!("{}", unsign_nuber_2)).unwrap();
//                 // k*P = k1*P + k2*Q where Q = lambda*P

//                 let mut point_pk1 = offset_generator.mul(scalar_for_p);
//                 if diff != 0{
//                     point_pk1.negate();
//                 }

//                 let point_q = endomorphism_params.apply_to_g1_point(offset_generator);

//                 let mut point_qk2 = point_q.mul(scalar_for_q);
//                 if diff_2 != 0{
//                     point_qk2.negate();
//                 }

//                 point_pk1.add_assign(&point_qk2);
//                 let final_point = point_pk1;

//                 let generator = AffinePoint::constant(final_point.into_affine(), params);

//                 let limbs_x = FieldElement::into_limbs(generator.x.clone());
//                 // low_limb
//                 column2.push(limbs_x[0].get_value().unwrap());
//                 column2.push(limbs_x[1].get_value().unwrap());
//                 // high_limb
//                 column2.push(limbs_x[2].get_value().unwrap());
//                 column2.push(limbs_x[3].get_value().unwrap());
    
//                 map.insert((scalar_x_low_0, scalar2), limbs_x[0].get_value().unwrap());
//                 map.insert((scalar_x_low_1, scalar2), limbs_x[1].get_value().unwrap());
//                 map.insert((scalar_x_high_0, scalar2), limbs_x[2].get_value().unwrap());
//                 map.insert((scalar_x_high_1, scalar2), limbs_x[3].get_value().unwrap());
    
    
//                 let limbs_y = FieldElement::into_limbs(generator.y.clone());
//                 // low_limb
//                 column2.push(limbs_y[0].get_value().unwrap());
//                 column2.push(limbs_y[1].get_value().unwrap());
//                 // high_limb
//                 column2.push(limbs_y[2].get_value().unwrap());
//                 column2.push(limbs_y[3].get_value().unwrap());
    
//                 map.insert((scalar_y_low_0, scalar2), limbs_y[0].get_value().unwrap());
//                 map.insert((scalar_y_low_1, scalar2), limbs_y[1].get_value().unwrap());
//                 map.insert((scalar_y_high_0, scalar2), limbs_y[2].get_value().unwrap());
//                 map.insert((scalar_y_high_1, scalar2), limbs_y[3].get_value().unwrap());
    
//             }
//         }

//         Self { 
//             table_entries: [column0, column1, column2],
//             table_lookup_map: map, 
//             table_len,
//             name
//         }

//     }
// }

// impl<E: Engine> std::fmt::Debug for ScalarPointEndoTable<E> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_struct("ScalarPointEndoTable").finish()
//     }
// }
// impl<E: Engine> LookupTableInternal<E> for ScalarPointEndoTable<E> {
//     fn name(&self) -> &'static str {
//         self.name
//     }
//     fn table_size(&self) -> usize {
//         self.table_len
//     }
//     fn num_keys(&self) -> usize {
//         1
//     }
//     fn num_values(&self) -> usize {
//         2
//     }
//     fn allows_combining(&self) -> bool {
//         true
//     }
//     fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
//         vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
//     }
//     fn table_id(&self) -> E::Fr {
//         table_id_from_string(self.name)
//     }
//     fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
//         unimplemented!()
//     }
//     fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
//         Box::from(self.clone())
//     }
//     fn column_is_trivial(&self, column_num: usize) -> bool {
//         assert!(column_num < 3);
//         false
//     }

//     fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
//         assert!(keys.len() == self.num_keys());
//         assert!(values.len() == self.num_values());

//         if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
//             return entry == &(values[0]);
//         }
//         false
//     }

//     fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
//         assert!(keys.len() == self.num_keys());

//         if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
//             return Ok(vec![*entry])
//         }

//         Err(SynthesisError::Unsatisfiable)
//     }
// }




// mod test {
//     use super::*;

//     use crate::plonk::circuit::*;
//     use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1Affine};

//     #[test]
//     fn test_table_for_point(){

//         let params = RnsParameters::<Bn256, Fq>::new_for_field(68, 110, 4);
//         let name : &'static str = "table for affine point";

//         let four = Fr::from_str("9").unwrap();
//         println!("{:?}", four);


//         let table = ScalarPointTable::<Bn256>::new::<Fq, G1Affine>(2, name, &params);

//         dbg!(&table.table_entries);

//         let column = table.get_table_values_for_polys();
//         println!("{:?}", column);
//         let res = table.query(&[four]).unwrap();
//         println!("{:?}", res);

//     }

// }

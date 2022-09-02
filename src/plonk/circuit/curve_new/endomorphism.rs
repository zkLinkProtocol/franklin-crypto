use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};
use crate::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr, BitIterator, ScalarEngine};
use crate::bellman::SynthesisError;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::Num;
use crate::plonk::circuit::bigint::bigint::*;

// we use parameters for decomposition as 
// k = k1 - \lambda * k2
// so affine point is transformed as 
// G1 -> (beta*x, -y) to be multiplied by +k2
// #[derive(Clone, Debug)]
// pub struct EndomorphismParameters<E: Engine> {
//     pub lambda: E::Fr,
//     pub beta: E::Fq,
//     pub a1: BigUint,
//     pub a2: BigUint,
//     pub minus_b1: BigUint,
//     pub b2: BigUint,
// }

// impl <E: Engine> EndomorphismParameters<E>  {
//     pub fn calculate_decomposition(&self, val: E::Fr) -> (E::Fr, E::Fr) {
//         // compute c1 = |b2 * k/ n | and c2 = | −b1k/n |.
//         // Compute k1 = k − c1*a1 −c2*a2 and k2 = −c1*b1 −c2*b2.
//         let k = repr_to_biguint::<E::Fr>(&val.into_repr());
//         let n = repr_to_biguint::<E::Fq>(&E::Fq::char().into_repr());
//         let target_bitlength = (E::Fq::NUM_BITS + 1) / 2;

//         let c1 = self.b2 * k / n; 
//         let c2 = self.minus_b1 * k / n;
//         let k1 = k - c1 * self.a1 - c2 * self.a2;
//         let k2 = self.minus_b1 * c1 - self.b2 * c2;
//         assert!(k1.num_bits() <= target_bitlength);
//         assert!(k2.num_bits() <= target_bitlength);

//         let k1 = biguint_to_fe::<E::Fr>(k1);
//         let k2 = biguint_to_fe::<E::Fr>(k2);

//         if cfg!(debug_assertions) { 
//             // assert that k = k1 + lambda * k2
//             let mut tmp = self.lambda;
//             tmp.mul_assign(&k2);
//             tmp.add_assign(&k1);
//             assert_eq!(val, tmp);
//         }

//         (k1, k2)
//     }

//     pub fn apply_to_g1_point(&self, point: E::G1Affine) -> E::G1Affine {
//         let (mut x, mut y) = point.into_xy_unchecked();
//         y.negate();
//         x.mul_assign(&self.beta);
//         debug_assert!(E::G1Affine::from_xy_checked(x, y).is_ok());
//         E::G1Affine::from_xy_unchecked(x, y)
//     }
// }


// pub fn bls12_endomorphism_parameters() -> EndomorphismParameters<crate::bellman::pairing::bls12_381::Bls12> {
//     let empty_fr_repr = crate::bellman::pairing::bn256::Fr::zero().into_repr();
//     let mut lambda_repr = empty_fr_repr;
//     lambda_repr.as_mut()[0] = 0x93e7cede4a0329b3;
//     lambda_repr.as_mut()[1] = 0x7d4fdca77a96c167;
//     lambda_repr.as_mut()[2] = 0x8be4ba08b19a750a;
//     lambda_repr.as_mut()[3] = 0x1cbd5653a5661c25;
//     let lambda = crate::bellman::pairing::bn256::Fr::from_raw_repr(lambda_repr).unwrap();

//     let mut may_be_one = lambda;
//     may_be_one.mul_assign(&lambda);
//     may_be_one.mul_assign(&lambda);
//     assert_eq!(may_be_one, crate::bellman::pairing::bn256::Fr::one());

//     let empty_fq_repr = crate::bellman::pairing::bn256::Fq::zero().into_repr();
//     let mut beta_g1_repr = empty_fq_repr;
//     beta_g1_repr.as_mut()[0] = 0x71930c11d782e155;
//     beta_g1_repr.as_mut()[1] = 0xa6bb947cffbe3323;
//     beta_g1_repr.as_mut()[2] = 0xaa303344d4741444;
//     beta_g1_repr.as_mut()[3] = 0x2c3b3f0d26594943;
//     let beta_g1 = crate::bellman::pairing::bn256::Fq::from_raw_repr(beta_g1_repr).unwrap();

//     let mut may_be_one = beta_g1;
//     may_be_one.mul_assign(&beta_g1);
//     may_be_one.mul_assign(&beta_g1);
//     assert_eq!(may_be_one, crate::bellman::pairing::bn256::Fq::one());

//     EndomorphismParameters::<crate::bellman::pairing::bn256::Bn256> {
//         lambda: lambda,
//         beta_g1: beta_g1,
//         a1: BigUint::from_str_radix("2d91d232ec7e0b3d7", 16).unwrap(),
//         a2: BigUint::from_str_radix("24ccef014a773d2cf7a7bd9d4391eb18d", 16).unwrap(),
//         minus_b1: BigUint::from_str_radix("6f4d8248eeb859fc8211bbeb7d4f1128", 16).unwrap(),
//         b2: BigUint::from_str_radix("89d3256894d213e3", 16).unwrap(),
//         scalar_width: 256,
//         target_scalar_width: 127
//     }
// }



// // # Decomposition of the scalar k in two scalars k1 and k2 with half bit-length, such that k=k1+k2*THETA (mod p)
// // # param theta is a root of the characteristic polynomial of an endomorphism of the curve
// // def endomorphism_params_calc(theta, n):
// //     bound = n.isqrt()
// //     u = n
// //     v = theta
// //     x1 = 1 
// //     y1 = 0
// //     x2 = 0
// //     y2 = 1
// //     while True:
// //         q = int(v/u)
// //         r = v - q*u 
// //         x = x2 - q*x1
// //         y = y2 - q*y1
// //         v = u
// //         u = r
// //         x2 = x1
// //         x1 = x
// //         y2 = y1
// //         y1 = y
// //         if r < bound:
// //             a1= r 
// //             b1 = -y1
// //             r_l = x2 * n + y2 * theta
// //             t_l = y2
// //             q = int(v/u)
// //             r_l2 = v - q*u 
// //             x_l2 = x2 - q*x1
// //             y_l2 = y2 - q*y1
// //             if r_l^2 + t_l^2 <= r_l2^2 + y_l2^2:
// //                 a2 = r_l,
// //                 b2 = -t_l
// //             else:
// //                 a2 = r_l2
// //                 b2 = -y_l2
// //             return (a1, b1, a2, b2)
            
            

// // n = 1461501637330902918203687013445034429194588307251
// // theta = 903860042511079968555273866340564498116022318806
// // print endomorphism_params_calc(theta, n)
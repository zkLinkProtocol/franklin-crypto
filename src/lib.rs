#![allow(dead_code, unused_imports, unused_macros)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
#![warn(unused_assignments)]


pub extern crate bellman;
extern crate blake2_rfc_bellman_edition as blake2_rfc;
extern crate byteorder;
extern crate digest;
extern crate hmac;
extern crate rand;
extern crate sha2;
extern crate sha3;
extern crate tiny_keccak;
// extern crate poseidon_hash;
extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;

extern crate blake2;
extern crate itertools;
extern crate regex;
extern crate splitmut;
extern crate serde;
extern crate num_derive;
extern crate indexmap;

use bellman::pairing;
use bellman::pairing::ff;


#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate arr_macro;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[cfg(test)]
extern crate hex;

pub mod generic_twisted_edwards;
pub mod alt_babyjubjub;
pub mod as_waksman;
pub mod baby_group_hash;
pub mod baby_pedersen_hash;
pub mod baby_util;
pub mod babyjubjub;
pub mod circuit;
pub mod constants;
pub mod eddsa;
pub mod group_hash;
pub mod interpolation;
pub mod jubjub;
pub mod pedersen_hash;
pub mod primitives;
pub mod redjubjub;
pub mod rescue;
pub mod poseidon;
pub mod util;

#[cfg(feature = "plonk")]
pub mod plonk;

pub fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow + 1)) <= num {
        pow += 1;
    }

    pow
}

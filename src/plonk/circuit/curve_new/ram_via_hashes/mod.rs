pub mod circuit;
#[allow(dead_code)]
mod common;
mod sponge;
pub mod rescue_prime;
mod traits;

use std::convert::TryInto;

use smallvec::SmallVec;
pub use self::traits::{HashParams, CustomGate, HashFamily};
pub use self::sponge::{generic_hash, generic_round_function, GenericSponge};
pub use self::rescue_prime::{params::RescuePrimeParams, rescue_prime_hash};
pub use self::common::domain_strategy::DomainStrategy;


pub trait BigArraySerde<'de>: Sized {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer;
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de>;
}

// some wrappers that make array wrappers serializable themselves (resursively)

pub struct BigArrayRefWrapper<'de, B: BigArraySerde<'de>>(&'de B);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayRefWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer {
        self.0.serialize(serializer)
    }
}

pub struct BigArrayWrapper<'de, B: BigArraySerde<'de>>(B, std::marker::PhantomData<& 'de ()>);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer {
        self.0.serialize(serializer)
    }
}

impl<'de, B: BigArraySerde<'de>> serde::Deserialize<'de> for BigArrayWrapper<'de, B> {
fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        let new = B::deserialize(deserializer)?;

        Ok(Self(new, std::marker::PhantomData))
    }
}

struct ArrayVisitor<T, const M: usize> {
    element: std::marker::PhantomData<T>,
}

impl<'de, T, const M: usize> serde::de::Visitor<'de> for ArrayVisitor<T, M>
    where T: serde::Deserialize<'de>
{
    type Value = [T; M];

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str(&format!("an array of length {}", M))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<[T; M], A::Error>
        where A: serde::de::SeqAccess<'de>
    {
        let mut arr = Vec::with_capacity(M);
        for i in 0..M {
            let el = seq.next_element()?
                .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
            arr.push(el);
        }
        use std::convert::TryInto;
        let arr: [T; M] = arr.try_into().map_err(|_| serde::de::Error::invalid_length(M, &self))?;

        Ok(arr)
    }
}

fn add_chain_pow_smallvec<F: crate::bellman::pairing::ff::PrimeField>(
    base: F,
    add_chain: &[traits::Step],
    scratch_space: &mut SmallVec<[F; 512]>,
) -> F {
    scratch_space.push(base);

    for (idx, el) in add_chain.iter().enumerate() {
        match el {
            traits::Step::Double { index } => {
                let mut el = scratch_space[*index];
                el.square();

                scratch_space.push(el);
            },
            traits::Step::Add { left, right } => {
                let mut el = scratch_space[*left];
                el.mul_assign(&scratch_space[*right]);

                scratch_space.push(el);
            }
        }
    }

    let result = scratch_space.pop().unwrap();

    scratch_space.clear();

    result
}
use crate::poseidon::traits::Sbox;
use crate::bellman::pairing::ff::Field;
use crate::bellman::pairing::Engine;

// Substitution box is non-linear part of permutation function.
// It basically computes power of each element in the state.
// Usually value of alpha is either 5 or 3. We keep a generic
// handler other values of alpha.
#[inline]
pub(crate) fn sbox<E: Engine>(power: &Sbox, state: &mut [E::Fr]) {
    match power {
        Sbox::Alpha(alpha) => sbox_alpha::<E>(alpha, state),
        Sbox::AlphaInverse(alpha_inv, _) => sbox_alpha_inv::<E>(alpha_inv, state),
        Sbox::AddChain(chain, _) => sbox_alpha_inv_via_add_chain::<E>(chain, state),
    }
}

#[inline]
pub(crate) fn sbox_alpha<E: Engine>(alpha: &u64, state: &mut [E::Fr]) {
    match alpha {
        5 => {
            for el in state.iter_mut() {
                let mut quad = *el;
                quad.square();
                quad.square();
                el.mul_assign(&quad);
            }
        }
        3 => {
            for el in state.iter_mut() {
                let mut quad = *el;
                quad.square();
                el.mul_assign(&quad);
            }
        }
        _ => {
            for el in state.iter_mut() {
                *el = el.pow(&[*alpha]);
            }
        }
    }
}

#[inline]
pub(crate) fn sbox_alpha_inv<E: Engine>(alpha_inv: &[u64], state: &mut [E::Fr]) {
    for el in state.iter_mut() {
        *el = el.pow(alpha_inv);
    }
}

pub fn add_chain_pow_smallvec<F: crate::bellman::pairing::ff::PrimeField>(
    base: F,
    add_chain: &[crate::poseidon::traits::Step],
    scratch_space: &mut smallvec::SmallVec<[F; 512]>,
) -> F {
    scratch_space.push(base);

    for (_idx, el) in add_chain.iter().enumerate() {
        match el {
            crate::poseidon::traits::Step::Double { index } => {
                let mut el = scratch_space[*index];
                el.square();

                scratch_space.push(el);
            },
            crate::poseidon::traits::Step::Add { left, right } => {
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

#[cfg(all(not(feature = "rayon"), not(feature = "futures")))]
#[inline]
pub(crate) fn sbox_alpha_inv_via_add_chain<E: Engine>(chain: &[crate::poseidon::traits::Step], state: &mut [E::Fr]) {
    let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
    for el in state.iter_mut() {
        *el = add_chain_pow_smallvec(*el, chain, &mut scratch);
    }
}

#[cfg(feature = "rayon")]
#[inline]
pub(crate) fn sbox_alpha_inv_via_add_chain<E: Engine>(chain: &[crate::traits::Step], state: &mut [E::Fr]) {
    use rayon::prelude::*;
    state.par_iter_mut()
        .for_each(|el| {
            let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
            *el = add_chain_pow_smallvec(*el, chain, &mut scratch);
        });
}

#[cfg(feature = "futures")]
lazy_static::lazy_static!{
    static ref EXECUTOR: futures::executor::ThreadPool = futures::executor::ThreadPool::builder().pool_size(3).create().expect("Failed to build pool");
}

#[cfg(feature = "futures")]
#[inline]
pub(crate) fn sbox_alpha_inv_via_add_chain<E: Engine>(chain: &[crate::traits::Step], state: &mut [E::Fr]) {
    let chain = unsafe {std::mem::transmute(chain)};
    use futures::task::SpawnExt;
    let f0 = EXECUTOR.spawn_with_handle(sbox_alpha_inv_via_add_chain_fut::<E>(state[0], chain)).unwrap();
    let f1 = EXECUTOR.spawn_with_handle(sbox_alpha_inv_via_add_chain_fut::<E>(state[1], chain)).unwrap();
    let f2 = EXECUTOR.spawn_with_handle(sbox_alpha_inv_via_add_chain_fut::<E>(state[2], chain)).unwrap();
    let join_all = futures::future::join_all([f0, f1, f2]);

    let res = futures::executor::block_on(join_all);
    state.copy_from_slice(&res[..3]);
}

#[cfg(feature = "futures")]
pub(crate) fn sbox_alpha_inv_via_add_chain_fut<E: Engine>(el: E::Fr, chain: &'static [crate::traits::Step]) -> E::Fr {
    let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
    add_chain_pow_smallvec(el, chain, &mut scratch)
}
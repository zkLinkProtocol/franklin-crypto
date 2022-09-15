use super::*;
use super::sw_affine::*;
use super::sw_projective::*;

use crate::bellman::pairing::{
    Engine,
    GenericCurveAffine,
    GenericCurveProjective,
};
use crate::bellman::pairing::ff::{
    Field,
    PrimeField,
    PrimeFieldRepr,
    BitIterator,
    ScalarEngine
};
use crate::bellman::SynthesisError;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use plonk::circuit::boolean::Boolean;
use plonk::circuit::bigint_new::Extension2Params;

use itertools::Itertools;

// The purpose of selection table is the following: 
// given n points P1, P2, .., Pn (in Affine or Projective coordinates),
// we want to store and later select linear combinations of the form +/ P1 +/ P2 +/- ... +/ Pn
// For example for 2 points P1, P2 naive selection tree looks like following:
//                              
//                         |true --- P + Q
//         |true---k2_bit--|
//         |               |false --- P - Q
// k1_bit--|
//         |        
//         |                |true --- -P + Q
//         |false---k2_bit--|
//                          |false --- -P - Q
//
// which results in 6 total selections: 3 selects for coordinate X and 3 selects for coordinate Y
// However, we may use te symmetry in negation formula for elliptic curve points: -P(x, y) = (x, -y) 
// hence the more optimal routine will look like:
// res.X = select(k1_bit ^ k2_bit, P-Q.X, P+Q.X)
// tmp.Y = select(k1_bit ^ k2_bit, P-Q.Y, P+Q.Y)
// res.Y = conditionally_negate(!k1, tmp.Y)
// which requires 3 total selects (as conditional negation costs the same as selection)
// in general the implementation trick is to replace selections by individual flags k1, k2, ..., k_n
// by selections by k1 ^ k2, k2 ^k3, ... , k_{n-1} ^ k_n.
// ideed the selected coordinate x is the same for combinations of flags: [k1, ..., k_n] and [!k1, ..., !k_n]

trait TreeSelectable<E: Engine>: Sized + Clone {
    fn add<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &mut Self, second: &mut Self
    ) -> Result<Self, SynthesisError>;
    
    fn sub<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &mut Self, second: &mut Self
    ) -> Result<Self, SynthesisError>;
    
    fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError>;
    
    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError>;
    
    fn conditionally_negate<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &mut Self
    ) -> Result<Self, SynthesisError>;
}

impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for AffinePoint<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    fn add<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        first.add_unequal_unchecked(cs, &second)
    }

    fn sub<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        first.sub_unequal_unchecked(cs, &mut second)
    }

    fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError> {
        AffinePoint::negate(first, cs)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        AffinePoint::conditionally_select(cs, flag, first, second)
    }
    
    fn conditionally_negate<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &mut Self
    ) -> Result<Self, SynthesisError> {
        first.conditionally_negate(cs, flag)
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for ProjectivePoint<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    fn add<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E> 
    {
        first.add(cs, &second)
    }

    fn sub<CS>(cs: &mut CS, first: &mut Self, second: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        first.sub(cs, &mut second)
    }

    fn negate<CS: ConstraintSystem<E>>(cs: &mut CS, first: &mut Self) -> Result<Self, SynthesisError> {
        ProjectivePoint::negate(first, cs)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        ProjectivePoint::conditionally_select(cs, flag, first, second)
    }
    
    fn conditionally_negate<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &mut Self
    ) -> Result<Self, SynthesisError> {
        first.conditionally_negate(cs, flag)
    }
}

#[derive(Clone, Debug)]
pub struct SelectorTree<E: Engine, T: TreeSelectable<E>> {
    entries: Vec<T>, // raw elements P1, P2, ..., Pn
    precompute: Vec<T>, // precomputed linear combinations +/ P1 +/ P2 +/- ... +/ Pn
    _marker: std::marker::PhantomData<E>
}

impl<E: Engine, T: TreeSelectable<E>> SelectorTree<E, T> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS, entries: &[T]) -> Result<Self, SynthesisError> {
        // using Selector tree makes sense only if there are more than 1 element
        assert!(entries.len() > 1);
        let mut entries = entries.to_vec();
        let mut workpad : Vec<T> = vec![entries[0].clone()];
        for elem in entries[1..].iter_mut() {
            let mut new_working_pad = Vec::<T>::with_capacity(workpad.len() << 1);
            for acc in workpad.iter_mut() {
                new_working_pad.push(T::add(cs, acc, elem)?);
                new_working_pad.push(T::sub(cs, acc, elem)?);
            }
            workpad = new_working_pad
        }
        let mut negations = Vec::<T>::with_capacity(workpad.len());
        for elem in workpad.iter_mut().rev() {
            negations.push(T::negate(cs, elem)?);
        }
        workpad.extend_from_slice(&negations[..]);
        assert_eq!(workpad.len(), 1 << entries.len());

        Ok(SelectorTree::<E, T> {
            entries, 
            precompute: workpad,
            _marker: std::marker::PhantomData::<E>
        })
    }

    pub fn select<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError> {
        assert_eq!(bits.len() == self.entries.len());
        let mut selector_subtree = self.precompute.clone(); 
        
        for (k0_bit, k1_bit) in bits.tuple_windows().rev() {
            let mut new_selector_subtree = Vec::<T>::with_capacity(selector_subtree.len() >> 1);
            let xor_flag = Boolean::xor(cs, &k0_bit, &k1_bit)?;
            for (first, second) in selector_subtree.into_iter().tuples() {
                let selected = T::conditionally_select(cs, &xor_flag, &first, &second)?;
                new_selector_subtree.push(selected);
            }
            selector_subtree = new_selector_subtree;
        }

        assert_eq!(selector_subtree.len(), 1);
        let last_flag = bits[0];
        let mut selected = selector_subtree.pop().unwrap();
        T::conditionally_negate(cs, &last_flag, &mut selected)
    }
}

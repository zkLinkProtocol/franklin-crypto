use super::*;
use super::sw_affine::*;
use super::sw_projective::*;
use super::super::permutation_network::*;

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
use crate::plonk::circuit::hashes_with_tables::utils::*;
use crate::bellman::plonk::commitments::transparent::utils::log2_floor;
use plonk::circuit::boolean::Boolean;
use plonk::circuit::bigint_new::*;
use plonk::circuit::allocated_num::Num;

use itertools::Itertools;
use std::collections::HashMap;

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

pub(crate) trait TreeSelectable<E: Engine>: Sized + Clone {
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

    // given x, returns y, such that x = 2 * y
    fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError>;
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
        first.sub_unequal_unchecked(cs, second)
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
        first.sub(cs, second)
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
pub(crate) struct SelectorTree<E: Engine, T: TreeSelectable<E>> {
    entries: Vec<T>, // raw elements P1, P2, ..., Pn
    precompute: Vec<T>, // precomputed linear combinations +/ P1 +/ P2 +/- ... +/ Pn
    initial_acc_idx: usize,
    _marker: std::marker::PhantomData<E>
}

impl<E: Engine, T: TreeSelectable<E>> SelectorTree<E, T> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS, entries: &[T]) -> Result<Self, SynthesisError> {
        // using Selector tree makes sense only if there are more than 1 element
        let mut entries = entries.to_vec();
        let mut workpad : Vec<T> = vec![entries.get(0).expect("Entries must be nonempty").clone()];
        let mut initial_acc_idx = 0;

        for (_is_first, is_last, elem) in entries[1..].iter_mut().identify_first_last() {
            if is_last {
                initial_acc_idx = workpad.len();
            }
            let mut new_working_pad = Vec::<T>::with_capacity(workpad.len() << 1);
            for acc in workpad.iter_mut() {
                new_working_pad.push(T::add(cs, acc, elem)?);
                new_working_pad.push(T::sub(cs, acc, elem)?);
            }
            workpad = new_working_pad
        }
        assert_eq!(workpad.len(), 1 << (entries.len() - 1));

        Ok(SelectorTree::<E, T> {
            entries, 
            precompute: workpad,
            initial_acc_idx,
            _marker: std::marker::PhantomData::<E>
        })
    }

    pub fn select<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError> {
        assert_eq!(bits.len(), self.entries.len() * 2);
        let mut selector_subtree = self.precompute.clone(); 
        
        for (k0_bit, k1_bit) in bits.iter().rev().tuple_windows() {
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

    pub fn select_last<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError>
    {
        // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
        // we want to retrieve the point which is dependent on bits as follows:
        // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
        // on the last iteratio we do however want to add the point \sum (b_i - 1) * P_i = B
        // if we denote the starting value of accumulator = /sum P_i as C
        // then it is obvious that the following relation always holds: A - C = 2 * B
        // hence we reduced the computation to one subtraction and one doubling
        let mut a = self.select(cs, &bits)?;
        let mut c = self.get_initial_accumulator();
        let tmp = T::sub(cs, &mut a, &mut c);
    }

    pub fn get_initial_accumulator(&self) -> T {
        // initial accumulator value is equal to + P1 + P2 + ... + Pn
        self.precompute[self.initial_acc_idx].clone()
    }
}

   
pub(crate) struct WaksmanMemory<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    queries: Vec<(Num<E>, AffinePoint<'a, E, G, T>)>,
    witness_map: HashMap<u64, Option<G>>,
    address_width: usize,
    validity_is_enforced: bool,
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Drop for WaksmanMemory<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    fn drop(&mut self) {
        assert!(self.validity_is_enforced);
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> WaksmanMemory<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField
{
    pub fn new(address_width: usize) -> Self {
        Self {
            queries: vec![],
            witness_map: HashMap::new(),
            address_width,
            validity_is_enforced: false,
        }
    }

    pub fn write(&mut self, addr: u64, point: AffinePoint<'a, E, G, T>) {
        assert!(log2_floor(addr as usize) as usize <= self.address_width);
        self.witness_map.insert(addr, point.get_value());
        let addr_as_num = Num::Constant(u64_to_ff(addr));
        self.queries.push((addr_as_num, point));
        self.validity_is_enforced = false; 
    }

    pub fn read<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, addr: Num<E>, params: &'a CurveCircuitParameters<E, G, T>
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> {
        let wit = addr.get_value().and_then(|x| { self.witness_map.get(&ff_to_u64(&x)).cloned().unwrap_or(None) });
        let res = AffinePoint::alloc(cs, wit, params)?;
        self.queries.push((addr, res));
        self.validity_is_enforced = false;

        Ok(res)
    }

    fn calculate_permutation(&self) -> IntegerPermutation {
        let mut keys = Vec::with_capacity(self.queries.len());
        for (idx, (addr, _)) in self.queries.iter().enumerate() {
            if let Some(addr) = addr.get_value() {
                let composite_key = ff_to_u64(&addr);
                keys.push((idx, composite_key));
            } else {
                return IntegerPermutation::new(self.queries.len());
            }
        }

        keys.sort_by(|a, b| a.1.cmp(&b.1));
        let integer_permutation: Vec<_> = keys.iter().map(|el| el.0).collect();
        IntegerPermutation::new_from_permutation(integer_permutation)
    }

    pub fn enforce_ram_correctness<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.validity_is_enforced = true;
        let shifts = compute_shifts::<E::Fr>();
        let size = self.queries.len();

        let permutation = self.calculate_permutation();
        let switches = order_into_switches_set(cs, &permutation)?;
        let mut unsorted_packed_elems_0 = Vec::with_capacity(size);
        let mut unsorted_packed_elems_1 = Vec::with_capacity(size);
        let mut sorted_packed_elems_0 = Vec::with_capacity(size);
        let mut sorted_packed_elems_1 = Vec::with_capacity(size);

        for (addr, point) in self.queries.iter() {
            let packed = point.pack(cs, addr, self.address_width)?;
            unsorted_packed_elems_0.push(packed[0]);
            unsorted_packed_elems_1.push(packed[1]);
        }
        for index in permutation.elements.iter() {
            let value_0 = unsorted_packed_elems_0[*index].clone();
            sorted_packed_elems_0.push(value_0);
            let value_1 = unsorted_packed_elems_1[*index].clone();
            sorted_packed_elems_1.push(value_1);
        }

        prove_permutation_of_nums_using_switches_witness(
            cs, &unsorted_packed_elems_0, &sorted_packed_elems_0, &switches
        )?;
        prove_permutation_of_nums_using_switches_witness(
            cs, &unsorted_packed_elems_1, &sorted_packed_elems_1, &switches
        )?;
       
        let limit = Num::Constant(u64_to_ff((1u64 << self.address_width) - 1));
        let mut counter = Num::zero();
        let iter = sorted_packed_elems_0.iter().zip(sorted_packed_elems_1.iter()).identify_first_last();
        let mut el_0_prev = Num::zero();
        let mut el_1_prev = Num::zero();
    
        for (is_first, _is_last, (el_0_cur, el_1_cur)) in iter {
            if !is_first {
                let is_equal_0 = Num::equals(cs, &el_0_prev, &el_0_cur)?;
                let is_equal_1 = Num::equals(cs, &el_1_prev, &el_1_cur)?;
                let both_are_equal = Boolean::and(cs, &is_equal_0, &is_equal_1)?;
                counter.conditionally_increment(cs, &both_are_equal.not())?;
            }
           
            el_0_prev = *el_0_cur;
            el_1_prev = *el_1_cur;
        }
        counter.enforce_equal(cs, &limit)
    }
}
 

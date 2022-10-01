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
use plonk::circuit::linear_combination::LinearCombination;

use itertools::Itertools;
use std::collections::HashMap;
use std::convert::TryInto;

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

    fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError> {
        let wit = elem.get_value().map(|x| {
            // if x = 2 * y and order of group is n - odd prime, then:
            // (n-1)/2 * x = (n-1) * y = -y
            let mut scalar = <G::Scalar as PrimeField>::char();
            scalar.div2();
            let mut res = x.mul(scalar).into_affine();
            res.negate();
            res
        });

        let halved = AffinePoint::alloc(cs, wit, elem.circuit_params)?;
        let mut initial = halved.double(cs)?;
        AffinePoint::enforce_equal(cs, elem, &mut initial)?;
        
        Ok(halved)
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T> TreeSelectable<E> for AffinePointExt<'a, E, G, T>
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
        AffinePointExt::negate(first, cs)
    }

    fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> {
        AffinePointExt::conditionally_select(cs, flag, first, second)
    }
    
    fn conditionally_negate<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &mut Self
    ) -> Result<Self, SynthesisError> {
        first.conditionally_negate(cs, flag)
    }

    fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, elem: &mut Self) -> Result<Self, SynthesisError> {
        let rns_params = elem.get_x().c0.representation_params;
        let (wit_x_c0, wit_x_c1, wit_y_c0, wit_y_c1)  = match elem.get_value() {
            Some((x_c0, x_c1, y_c0, y_c1)) => {
                // if x = 2 * y and order of group is n - odd prime, then:
                // (n-1)/2 * x = (n-1) * y = -y
                let mut scalar = <G::Scalar as PrimeField>::char();
                scalar.div2();
                
                // it is a dirty hack but fine for now
                // at least we enforce that no new constraints will appear this way
                let gate_count_start = cs.get_current_step_number();

                let to_add = AffinePointExt::<E, G, T>::constant(x_c0, x_c1, y_c0, y_c1, rns_params);
                let mut acc = to_add.clone();
                for bit in BitIterator::new(scalar).skip_while(|x| !x).skip(1) {
                    acc = acc.double(cs)?;
                    if bit {
                        acc = acc.add_unequal_unchecked(cs, &to_add)?;
                    }
                }
                let res = acc.negate(cs)?;

                let gate_count_end = cs.get_current_step_number();
                assert_eq!(gate_count_end - gate_count_start, 0);
                
                let (x_c0, x_c1, y_c0, y_c1) = res.get_value().expect("should be some");
                (Some(x_c0), Some(x_c1), Some(y_c0), Some(y_c1)) 
            },
            None => (None, None, None, None),
        };

        let halved = AffinePointExt::alloc(cs, wit_x_c0, wit_x_c1, wit_y_c0, wit_y_c1, rns_params)?;
        let mut initial = halved.double(cs)?;
        AffinePointExt::enforce_equal(cs, elem, &mut initial)?;
        
        Ok(halved)
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

    fn halving<CS: ConstraintSystem<E>>(cs: &mut CS, point: &mut Self) -> Result<Self, SynthesisError> {
        let default = AffinePoint::constant(G::one(), point.circuit_params);
        let (mut affine_point, is_point_at_infty) = point.convert_to_affine_or_default(cs, &default)?;
        let wit = affine_point.get_value().map(|x| {
            // if x = 2 * y and order of group is n - odd prime, then:
            // (n-1)/2 * x = (n-1) * y = -y
            let mut scalar = <G::Scalar as PrimeField>::char();
            scalar.div2();
            let mut res = x.mul(scalar).into_affine();
            res.negate();
            res
        });

        let halved = AffinePoint::alloc(cs, wit, point.circuit_params)?;
        let mut initial = halved.double(cs)?;
        AffinePoint::enforce_equal(cs, &mut affine_point, &mut initial)?;

        ProjectivePoint::conditionally_select(
            cs, &is_point_at_infty, &ProjectivePoint::zero(point.circuit_params), &ProjectivePoint::from(halved)
        )
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
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        enum Sign {
            Plus,
            Minus
        }

        // using Selector tree makes sense only if there are more than 1 element
        let mut entries = entries.to_vec();
        let mut workpad : Vec<(Sign, T)> = vec![(Sign::Plus, entries.get(0).expect("Entries must be nonempty").clone())];

        for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
            let mut new_working_pad = Vec::<(Sign, T)>::with_capacity(workpad.len() << 1);
            for (sign, acc) in workpad.iter_mut() {
                match sign {
                    Sign::Plus => {
                        new_working_pad.push((Sign::Minus, T::sub(cs, acc, elem)?));
                        new_working_pad.push((Sign::Plus, T::add(cs, acc, elem)?));   
                    },
                    Sign::Minus => {
                        new_working_pad.push((Sign::Plus, T::add(cs, acc, elem)?));   
                        new_working_pad.push((Sign::Minus, T::sub(cs, acc, elem)?));
                    },
                };
            }
            workpad = new_working_pad
        }
        assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
        let initial_acc_idx = workpad.len() - 1;
        let precompute = workpad.drain(..).map(|(_sign, pt)| pt).collect();

        Ok(SelectorTree::<E, T> {
            entries, 
            precompute,
            initial_acc_idx,
            _marker: std::marker::PhantomData::<E>
        })
    }

    pub fn select<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError> {
        assert_eq!(bits.len(), self.entries.len());
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
        T::conditionally_negate(cs, &last_flag.not(), &mut selected)
    }

    pub fn select_last<CS: ConstraintSystem<E>>(&self, cs: &mut CS, bits: &[Boolean]) -> Result<T, SynthesisError>
    {
        // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
        // we want to retrieve the point which is dependent on bits as follows:
        // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
        // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
        // if we denote the starting value of accumulator = /sum P_i as C
        // then it is obvious that the following relation always holds: A - C = 2 * B
        // hence we reduced the computation to one subtraction and one doubling
        let mut a = self.select(cs, &bits)?;
        let mut c = self.get_initial_accumulator();
        let mut tmp = T::sub(cs, &mut a, &mut c)?;
        let res = T::halving(cs, &mut tmp)?;
        Ok(res)
    }

    pub fn get_initial_accumulator(&self) -> T {
        // initial accumulator value is equal to + P1 + P2 + ... + Pn
        self.precompute[self.initial_acc_idx].clone()
    }
}


const RATE: usize = 2;
const WIDTH: usize = 3;

fn round_function_absorb<E: Engine, CS: ConstraintSystem<E>, P: HashParams<E, RATE, WIDTH>>(
    cs: &mut CS, state: &mut [Num<E>; WIDTH], input: &[Num<E>], hash_params: &P
) -> Result<(), SynthesisError> 
{
    assert_eq!(input.len(), RATE);
    
    let mut state_lcs = vec![];
    for (s, inp) in state.iter().zip(input.iter())  {
        let mut lc = LinearCombination::from(*s);
        lc.add_assign_number_with_coeff(&inp, E::Fr::one());
        state_lcs.push(lc);
    }

    for s in state[input.len()..].iter() {
        let lc = LinearCombination::from(*s);
        state_lcs.push(lc);
    }

    let mut state_lcs = state_lcs.try_into().expect("state width should match");
    
    use crate::plonk::circuit::curve_new::ram_via_hashes::circuit::sponge::circuit_generic_round_function;
    circuit_generic_round_function(cs, &mut state_lcs, hash_params)?;

    for (a, b) in state.iter_mut().zip(state_lcs.iter()) {
        *a = b.clone().into_num(cs)?;
    }

    Ok(())
}

fn round_function_squeeze<E: Engine>(state: &[Num<E>; WIDTH]) -> (Num<E>, Num<E>) {
    (state[0].clone(), state[1].clone())
}


#[derive(Clone, PartialEq, Eq, Debug)]
pub enum MemoryEnforcementStrategy {
    Waksman,
    HashSets,
}
   
pub(crate) struct Memory<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    queries: Vec<(Num<E>, AffinePoint<'a, E, G, T>)>,
    witness_map: HashMap<u64, Option<G>>,
    address_width: usize,
    validity_is_enforced: bool,
    permutation_enforcement_strategy: MemoryEnforcementStrategy,

    permutation: IntegerPermutation,
    unsorted_packed_elems_0: Vec<Num<E>>,
    unsorted_packed_elems_1: Vec<Num<E>>,
    sorted_packed_elems_0: Vec<Num<E>>,
    sorted_packed_elems_1: Vec<Num<E>>,
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Drop for Memory<'a, E, G, T> 
where <G as GenericCurveAffine>::Base: PrimeField
{
    fn drop(&mut self) {
        assert!(self.validity_is_enforced);
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> Memory<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField
{
    pub fn new(address_width: usize, permutation_enforcement_strategy: MemoryEnforcementStrategy) -> Self {
        Self {
            queries: vec![],
            witness_map: HashMap::new(),
            address_width,
            validity_is_enforced: false,
            permutation_enforcement_strategy,

            permutation: IntegerPermutation::new(1),
            unsorted_packed_elems_0: vec![],
            unsorted_packed_elems_1: vec![],
            sorted_packed_elems_0: vec![],
            sorted_packed_elems_1: vec![],
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
        self.queries.push((addr, res.clone()));
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

    fn enforce_correctness_of_sorted_packed_queries<CS>(&mut self, cs: &mut CS)-> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        let limit = Num::Constant(u64_to_ff((1u64 << self.address_width) - 1));
        let mut counter = Num::zero();
        let iter = self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter()).identify_first_last();
        let mut el_0_prev = Num::zero();
        let mut el_1_prev = Num::zero();
    
        for (is_first, _is_last, (el_0_cur, el_1_cur)) in iter {
            if !is_first {
                let is_equal_0 = Num::equals(cs, &el_0_prev, &el_0_cur)?;
                let is_equal_1 = Num::equals(cs, &el_1_prev, &el_1_cur)?;
                let both_are_equal = Boolean::and(cs, &is_equal_0, &is_equal_1)?;
                counter = counter.conditionally_increment(cs, &both_are_equal.not())?;
            }
           
            el_0_prev = *el_0_cur;
            el_1_prev = *el_1_cur;
        }
        counter.enforce_equal(cs, &limit)
    }

    pub fn enforce_ram_correctness<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> 
    {
        self.validity_is_enforced = true;
        let size = self.queries.len();

        let permutation = self.calculate_permutation();
        
        let mut unsorted_packed_elems_0 = Vec::with_capacity(size);
        let mut unsorted_packed_elems_1 = Vec::with_capacity(size);
        let mut sorted_packed_elems_0 = Vec::with_capacity(size);
        let mut sorted_packed_elems_1 = Vec::with_capacity(size);

        for (addr, point) in self.queries.iter_mut() {
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

        self.permutation = permutation;
        self.unsorted_packed_elems_0 = unsorted_packed_elems_0;
        self.unsorted_packed_elems_1 = unsorted_packed_elems_1;
        self.sorted_packed_elems_0 = sorted_packed_elems_0;
        self.sorted_packed_elems_1 = sorted_packed_elems_1;

        self.enforce_correctness_of_permutation(cs)?;
        self.enforce_correctness_of_sorted_packed_queries(cs)
    }

    

    fn enforce_correctness_of_permutation<CS>(&mut self, cs: &mut CS) -> Result<(), SynthesisError>
    where CS: ConstraintSystem<E>
    {
        match self.permutation_enforcement_strategy {
            MemoryEnforcementStrategy::Waksman => {
                let switches = order_into_switches_set(cs, &self.permutation)?;
                prove_permutation_of_nums_using_switches_witness(
                    cs, &self.unsorted_packed_elems_0, &self.sorted_packed_elems_0, &switches
                )?;
                prove_permutation_of_nums_using_switches_witness(
                    cs, &self.unsorted_packed_elems_1, &self.sorted_packed_elems_1, &switches
                )
            },
            MemoryEnforcementStrategy::HashSets => {
                let hash_params = RescuePrimeParams::<E, RATE, WIDTH>::new_with_width4_custom_gate();
                let mut state = [Num::<E>::zero(); WIDTH];

                let iter = self.unsorted_packed_elems_0.iter().zip(self.unsorted_packed_elems_1.iter()).chain(
                    self.sorted_packed_elems_0.iter().zip(self.sorted_packed_elems_1.iter())
                );
                for (x, y) in iter {
                    let input = [x.clone(), y.clone()];
                    round_function_absorb(cs, &mut state, &input, &hash_params)?;
                };
                let (challenge_a, challenge_b) = round_function_squeeze(&state);

                // (Polynomials are of the form X + c0 * Y + c1)
                // we substitute X and Y with challenge a and b correspondingly
                let mut lhs = Num::Constant(E::Fr::one());
                let mut rhs = Num::Constant(E::Fr::one());
                
                let outer_iter = std::iter::once(
                    (&self.unsorted_packed_elems_0, &self.unsorted_packed_elems_1, &mut lhs)
                ).chain(std::iter::once(
                    (&self.sorted_packed_elems_0, &self.sorted_packed_elems_1, &mut rhs)
                ));
                for (column_0, column_1, out) in outer_iter {
                    let inner_iter = column_0.iter().zip(column_1.iter());
                    for (c0, c1) in inner_iter {
                        let mut lc = LinearCombination::zero(); 
                        lc.add_assign_number_with_coeff(&challenge_a.clone(), E::Fr::one());
                        lc.add_assign_number_with_coeff(&c1, E::Fr::one());
                        let c0_mul_challenge = c0.mul(cs, &challenge_b)?;
                        lc.add_assign_number_with_coeff(&c0_mul_challenge, E::Fr::one());
                        let multiplier = lc.into_num(cs)?;
                        *out = Num::mul(out, cs, &multiplier)?;
                    }
                } 
                lhs.enforce_equal(cs, &rhs)
            }
        }    
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Fq, Bn256, Fr, G1, G1Affine};
    use crate::bellman::pairing::bls12_381::Bls12;
    use plonk::circuit::Width4WithCustomGates;
    use bellman::plonk::better_better_cs::gates::{selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self};
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;
    use plonk::circuit::boolean::AllocatedBit;
    use itertools::Itertools;

    struct TestSelectorTreeCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>,
        num_of_points: usize
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestSelectorTreeCircuit<E, G, T> 
    where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
    {
        type MainGate = SelectorOptimizedWidth4MainGateWithDNext;
        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![ SelectorOptimizedWidth4MainGateWithDNext::default().into_internal() ]
            )
        }
    
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let mut rng = rand::thread_rng();
            let mut points = Vec::with_capacity(self.num_of_points);
            let mut scalars = Vec::with_capacity(self.num_of_points);

            for _ in 0..self.num_of_points {
                let scalar_wit : G::Scalar = rng.gen();
                let point_wit : G = rng.gen();
    
                let point = AffinePoint::alloc(cs, Some(point_wit), &self.circuit_params)?;
                let scalar = FieldElement::alloc(cs, Some(scalar_wit), &self.circuit_params.scalar_field_rns_params)?;
    
                points.push(point);
                scalars.push(scalar);
            }

            let selector_tree = SelectorTree::new(cs, &points)?;
            let in_circuit_false = Boolean::Is(AllocatedBit::alloc(cs, Some(false))?);
            let in_circuit_true = Boolean::Is(AllocatedBit::alloc(cs, Some(true))?);
            let iter = (0..self.num_of_points).map(
                |_| std::iter::once(in_circuit_false).chain(std::iter::once(in_circuit_true))
            ).multi_cartesian_product();

            for bits in iter {
                let mut acc = points[0].conditionally_negate(cs, &bits[0].not())?;
                for (point, bit) in points.iter().zip(bits.iter()).skip(1) {
                    let mut to_add = point.conditionally_negate(cs, &bit.not())?;
                    acc = acc.add_unequal(cs, &mut to_add)?;
                }
                let mut chosen_from_selector_tree = selector_tree.select(cs, &bits[..])?;
                AffinePoint::enforce_equal(cs, &mut acc, &mut chosen_from_selector_tree)?;

                if bits.iter().all(|x| x.get_value().unwrap()) {
                    let mut sum_all = selector_tree.get_initial_accumulator();
                    AffinePoint::enforce_equal(cs, &mut acc, &mut sum_all)?;
                }

                // check what should be done on the last iterator
                let mut iter = bits.iter().enumerate().skip_while(|(_i, x)| x.get_value().unwrap()).peekable();
                if iter.peek().is_some() {
                    let (i, bit) = iter.next().unwrap();
                    assert_eq!(bit.get_value().unwrap(), false);
                    let mut acc = points[i].negate(cs)?;
                    for (idx, bit) in iter {
                        if !bit.get_value().unwrap() {
                            acc = acc.sub_unequal(cs, &mut points[idx])?;
                        }
                    }
                    let mut last_selection = selector_tree.select_last(cs, &bits)?;
                    AffinePoint::enforce_equal(cs, &mut acc, &mut last_selection)?;
                } 
            }
           
            Ok(())
        }
    }

    #[test]
    fn test_tree_selector_for_bn256() {
        const LIMB_SIZE: usize = 80;
        const NUM_OF_POINTS: usize = 3;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestSelectorTreeCircuit { circuit_params, num_of_points: NUM_OF_POINTS };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }    
}
 

use bellman::{ConstraintSystem, LinearCombination};
use circuit::expression::Expression;
use circuit::num::{AllocatedNum, Num};
use crate::{bellman::Engine, bellman::{Field, SynthesisError}};
use crate::poseidon::traits::{CustomGate, Sbox};
use crate::poseidon::common::sbox::add_chain_pow_smallvec;

// Substitution box is non-linear part of permutation function.
// It basically computes 5th power of each element in the state.
// Poseidon uses partial sbox which basically computes power of
// single element of state. If constraint system has support of
// custom gate then computation costs only single gate.
// TODO use const generics here
pub(crate) fn sbox<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    mut cs: CS,
    power: &Sbox,
    prev_state: &mut [Num<E>; WIDTH],
    use_partial_state: Option<std::ops::Range<usize>>,
    _custom_gate: CustomGate,
) -> Result<(), SynthesisError> {
    let state_range = if let Some(partial_range) = use_partial_state{
        partial_range
    }else{
        0..WIDTH
    };

    match power {
        Sbox::Alpha(alpha) => sbox_alpha(
            cs.namespace(|| "sbox_alpha"),
            alpha,
            prev_state,
            state_range,
        ),
        // Sbox::AlphaInverse(alpha_inv, alpha) => {
        //     // sbox_alpha_inv(cs.namespace(|| "sbox_alpha_inv"), alpha_inv, alpha, prev_state)
        // },
        // Sbox::AddChain(chain, alpha) => {
        //     // in circuit there is no difference
        //     // sbox_alpha_inv_via_add_chain(cs.namespace(|| "sbox_alpha_inv_via_add_chain"), chain, alpha, prev_state, custom_gate)
        // },
        _ => unreachable!(),
    }
}

fn sbox_alpha<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
    mut cs: CS,
    alpha: &u64,
    prev_state: &mut [Num<E>; WIDTH],
    state_range: std::ops::Range<usize>,
) -> Result<(), SynthesisError> {

    if *alpha != 5u64 {
        unimplemented!("only 5th power is supported!")
    }
    for (i, lc) in prev_state[state_range].iter_mut().enumerate() {
        let mut cs = cs.namespace(|| format!("update {}th state in sbox alpha", i));
        let value = lc.clone().into_allocated_num(cs.namespace(|| "into_allocated_num"))?;
        let square = value.square(cs.namespace(|| "x^2"))?;
        let quad = square.square(cs.namespace(|| "x^4"))?;
        let result = quad.mul(cs.namespace(|| "x^5"), &value)?;
        *lc = Num::from(result);
    }

    return Ok(());
}
//
// // This function computes power of inverse of alpha to each element of state.
// // By custom gate support, it costs only single gate. Under the hood, it proves
// // that 5th power of each element of state is equal to itself.(x^(1/5)^5==x)
// fn sbox_alpha_inv<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
//     cs: &mut CS,
//     alpha_inv: &[u64],
//     alpha: &u64,
//     prev_state: &mut [LinearCombination<E>; WIDTH],
//     custom_gate: CustomGate,
// ) -> Result<(), SynthesisError> {
//     let use_custom_gate = match custom_gate {
//         CustomGate::None => false,
//         _ => true,
//     };
//
//     if *alpha != 5u64 {
//         unimplemented!("only inverse for 5th power is supported!")
//     }
//
//     for lc in prev_state.iter_mut() {
//         match lc.clone().into_num(cs)? {
//             Num::Constant(value) => {
//                 let result = value.pow(alpha_inv);
//                 *lc = LinearCombination::zero();
//                 lc.add_assign_constant(result);
//             }
//             Num::Variable(ref value) => {
//                 let wit: Option<E::Fr> = value.get_value().map(|base| {
//                     let result = base.pow(alpha_inv);
//                     result
//                 });
//
//                 let powered = AllocatedNum::alloc(cs, || wit.grab())?;
//
//                 if use_custom_gate {
//                     // let _ = apply_5th_power(cs, &powered, Some(*value))?;
//                     let _ = inner_apply_5th_power(cs, &powered, Some(*value), custom_gate)?;
//                 } else {
//                     let squared = powered.square(cs)?;
//                     let quad = squared.square(cs)?;
//
//                     let mut term = MainGateTerm::<E>::new();
//                     let fifth_term = ArithmeticTerm::from_variable(quad.get_variable())
//                         .mul_by_variable(powered.get_variable());
//                     let el_term = ArithmeticTerm::from_variable(value.get_variable());
//                     term.add_assign(fifth_term);
//                     term.sub_assign(el_term);
//                     cs.allocate_main_gate(term)?;
//                 };
//                 *lc = LinearCombination::from(powered);
//             }
//         }
//     }
//
//     return Ok(());
// }
//
//
// // This function computes power of inverse of alpha to each element of state.
// // By custom gate support, it costs only single gate. Under the hood, it proves
// // that 5th power of each element of state is equal to itself.(x^(1/5)^5==x)
// fn sbox_alpha_inv_via_add_chain<E: Engine, CS: ConstraintSystem<E>, const WIDTH: usize>(
//     cs: &mut CS,
//     addition_chain: &[crate::poseidon::traits::Step],
//     alpha: &u64,
//     prev_state: &mut [LinearCombination<E>; WIDTH],
//     custom_gate: CustomGate,
// ) -> Result<(), SynthesisError> {
//     let use_custom_gate = match custom_gate {
//         CustomGate::None => false,
//         _ => true,
//     };
//
//     if *alpha != 5u64 {
//         unimplemented!("only inverse for 5th power is supported!")
//     }
//
//     for lc in prev_state.iter_mut() {
//         match lc.clone().into_num(cs)? {
//             Num::Constant(value) => {
//                 let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
//                 let result = crate::poseidon::common::sbox::add_chain_pow_smallvec(value, addition_chain, &mut scratch);
//                 *lc = LinearCombination::zero();
//                 lc.add_assign_constant(result);
//             }
//             Num::Variable(ref value) => {
//                 let wit: Option<E::Fr> = value.get_value().map(|el| {
//                     let mut scratch = smallvec::SmallVec::<[E::Fr; 512]>::new();
//                     let result = crate::poseidon::common::sbox::add_chain_pow_smallvec(el, addition_chain, &mut scratch);
//
//                     result
//                 });
//
//                 let powered = AllocatedNum::alloc(cs, || wit.grab())?;
//
//                 if use_custom_gate {
//                     // let _ = apply_5th_power(cs, &powered, Some(*value))?;
//                     let _ = inner_apply_5th_power(cs, &powered, Some(*value), custom_gate)?;
//                 } else {
//                     let squared = powered.square(cs)?;
//                     let quad = squared.square(cs)?;
//
//                     let mut term = MainGateTerm::<E>::new();
//                     let fifth_term = ArithmeticTerm::from_variable(quad.get_variable())
//                         .mul_by_variable(powered.get_variable());
//                     let el_term = ArithmeticTerm::from_variable(value.get_variable());
//                     term.add_assign(fifth_term);
//                     term.sub_assign(el_term);
//                     cs.allocate_main_gate(term)?;
//                 };
//                 *lc = LinearCombination::from(powered);
//             }
//         }
//     }
//
//     return Ok(());
// }
//
// fn inner_apply_5th_power<E: Engine, CS: ConstraintSystem<E>>(
//     cs: &mut CS,
//     value: &AllocatedNum<E>,
//     existing_5th: Option<AllocatedNum<E>>,
//     custom_gate: CustomGate,
// ) -> Result<AllocatedNum<E>, SynthesisError> {
//     assert!(
//         CS::Params::HAS_CUSTOM_GATES,
//         "CS should have custom gate support"
//     );
//     match custom_gate {
//         CustomGate::QuinticWidth4 => {
//             assert!(
//                 CS::Params::STATE_WIDTH >= 4,
//                 "state width should equal or large then 4"
//             );
//             crate::plonk::circuit::custom_rescue_gate::apply_5th_power(
//                 cs,
//                 value,
//                 existing_5th,
//             )
//         }
//         CustomGate::QuinticWidth3 => {
//             assert!(
//                 CS::Params::STATE_WIDTH >= 3,
//                 "state width should equal or large then 3"
//             );
//             crate::plonk::circuit::custom_rescue_gate::apply_5th_power(
//                 cs,
//                 value,
//                 existing_5th,
//             )
//         }
//         _ => unimplemented!(),
//     }
// }

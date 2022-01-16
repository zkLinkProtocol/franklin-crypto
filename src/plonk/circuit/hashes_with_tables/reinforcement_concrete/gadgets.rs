use crate::bellman::plonk::better_better_cs::cs::*;
use crate::bellman::plonk::better_better_cs::lookup_tables::*;
use crate::bellman::plonk::better_better_cs::utils;
use crate::bellman::pairing::ff::*;
use crate::bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::bellman::SynthesisError;
use crate::bellman::Engine;
use crate::plonk::circuit::allocated_num::{
    AllocatedNum,
    Num,
};
use crate::plonk::circuit::byte::{
    Byte,
};
use crate::plonk::circuit::assignment::{
    Assignment
};
use crate::plonk::circuit::custom_5th_degree_gate_optimized::Nonlinearity5CustomGate;
use crate::plonk::circuit::custom_rescue_gate::Rescue5CustomGate;
use crate::plonk::circuit::bigint::repr_to_biguint;
use crate::plonk::circuit::linear_combination::*;

use super::tables::*;
use super::super::utils::*;
use super::super::tables::*;
use sha3::{digest::ExtendableOutput, digest::Update, Sha3XofReader, Shake128, digest::XofReader};

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{ Zero, One };
use std::convert::TryInto;
use std::ops::{Index, IndexMut};

type Result<T> = std::result::Result<T, SynthesisError>;

pub const RC_STATE_WIDTH : usize = 3;
pub const RC_RATE: usize = 2;
pub const RC_PRE_ROUNDS_COUNT: usize = 3;
pub const RC_POST_ROUNDS_COUNT: usize = 3;
pub const RC_TOTAL_ROUNDS_COUNT: usize = RC_PRE_ROUNDS_COUNT + RC_POST_ROUNDS_COUNT;
pub const RC_INIT_SHAKE: &'static str = "ReinforcedConcrete";


#[derive(Clone)]
pub struct RCState<E: Engine>([Num<E>; RC_STATE_WIDTH]);

impl<E: Engine> Default for RCState<E> {
    fn default() -> Self {
        RCState(<[Num<E>; RC_STATE_WIDTH]>::default())
    }
}

impl<E: Engine> Index<usize> for RCState<E> {
    type Output = Num<E>;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < RC_STATE_WIDTH);
        &self.0[index]
    }
}

impl<E: Engine> IndexMut<usize> for RCState<E> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < RC_STATE_WIDTH);
        &mut self.0[index]
    }
}


#[derive(Clone)]
pub struct ReinforcementConcreteGadget<E: Engine>{
    // constants 
    alphas: [E::Fr; 2],
    betas: [E::Fr; 2],
    p_prime: u16,
    s_arr: Vec<u16>,
    u_arr: Vec<u16>,

    pub use_optimized_fifth_power: bool,
    mds_matrix: [[E::Fr; RC_STATE_WIDTH]; RC_STATE_WIDTH],
    round_constants: [E::Fr; RC_TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH],

    state: RCState<E>,
    num_squeezed: usize,
}

impl<E: Engine> ReinforcementConcreteGadget<E> {
    pub fn new<CS: ConstraintSystem<E>, F: Fn(u16) -> u16>(
        cs: &mut CS, alphas: [E::Fr; 2], betas: [E::Fr; 2], p_prime: u16, s_arr: Vec<u16>,
        perm_f: F, use_optimized_fifth_power: bool,
    ) -> Result<Self> 
    {
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name0: &'static str = "rc_helper_table0";
        let rc_helper_table0 = LookupTableApplication::new(
            name0,
            ReinforcementConcreterHelperTable0::new(name0),
            columns3.clone(),
            None,
            true
        );
        let rc_helper_table0 = cs.add_table(rc_helper_table0)?;

        // we are going to check that \prod s_i >= E::Fr::modulus
        // we compute the sequence of u_i and check that p <= u_i
        let modulus = repr_to_biguint::<E::Fr>(&<E::Fr as PrimeField>::char());
        let mut x = modulus - 1u64;
        let mut u_arr = Vec::with_capacity(s_arr.len());
        let mut s_prod = BigUint::one();

        for s in s_arr.iter().rev() {
            s_prod *= *s;
            let u = (x % s).to_u16().unwrap();
            u_arr.push(u);
            x = (x - u) / s;

            assert!(p_prime <= u);
        }
        assert!(s_prod >= modulus);
        u_arr.reverse();

        let name1: &'static str = "rc_helper_table1";
        let rc_helper_table1 = LookupTableApplication::new(
            name1,
            ReinforcementConcreterHelperTable1::new(p_prime, perm_f, &s_arr, &u_arr, name1),
            columns3.clone(),
            None,
            true
        );
        let rc_helper_table1 = cs.add_table(rc_helper_table1)?;

        // initialize MDS matrix:
        //
        //     (2  1  1)
        // M = (1  2  1)
        //     (1  1  2)
        let one_fr = E::Fr::one();
        let mut two_fr = one_fr.clone();
        two_fr.double();
        let mds_matrix = [
            [two_fr.clone(), one_fr.clone(), one_fr.clone()],
            [one_fr.clone(), two_fr.clone(), one_fr.clone()],
            [one_fr.clone(), one_fr.clone(), two_fr.clone()],
        ];

        // initialize round constants
        let mut shake = Shake128::default();
        shake.update(RC_INIT_SHAKE);
        for i in <E::Fr as PrimeField>::char().as_ref() {
            shake.update(u64::to_le_bytes(*i));
        }
        let mut reader = shake.finalize_xof();

        let bytes = f64::ceil(E::Fr::NUM_BITS as f64 / 8f64) as usize;
        let words = f64::ceil(bytes as f64 / 8f64) as usize;
        let mod_ = E::Fr::NUM_BITS % 8;
        let mask = if mod_ == 0 { 0xFF } else { (1u8 << mod_) - 1 };

        let round_constants : [E::Fr; RC_TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH] = (
            0..RC_TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH
        ).map(|_| {   
            let mut buf = vec![0u8; bytes];
            let mut word_buf = vec![0u64; words];
            let len = buf.len();

            loop {
                reader.read(&mut buf);
                buf[len - 1] &= mask;
                for i in 0..words {
                    let mut byte_array = [0u8; 8];
                    for j in i * 8..std::cmp::min((i + 1) * 8, len) {
                        byte_array[j - i * 8] = buf[j];
                    }
                    word_buf[i] = u64::from_le_bytes(byte_array);
                }

                let mut tmp = <E::Fr as PrimeField>::Repr::default();
                tmp.as_mut().copy_from_slice(&word_buf);
                let res = E::Fr::from_repr(tmp);

                if let Ok(el) = res {
                    break el
                }
            }
        }).collect::<Vec<E::Fr>>().as_slice().try_into().unwrap();

        Ok(ReinforcementConcreteGadget {
            alphas,
            betas,
            p_prime,
            s_arr,
            u_arr,
            use_optimized_fifth_power,
            mds_matrix,
            round_constants,
            state: RCState::default(),
            num_squeezed: 0
        })
    }

    fn apply_5th_power<CS: ConstraintSystem<E>>(&self, cs: &mut CS, elem: &Num<E>) -> Result<Num<E>> {
        let res = match elem {
            Num::Constant(constant) => {
                let mut result = *constant;
                result.square();
                result.square();
                result.mul_assign(constant);
                Num::Constant(result)
            },
            Num::Variable(var) => {
                let fifth_power_var = if self.use_optimized_fifth_power {
                    let third = AllocatedNum::alloc(
                        cs, 
                        || {
                            let val = *var.get_value().get()?;
                            let mut tmp = val;
                            tmp.square();
                            tmp.mul_assign(&val);
                            Ok(tmp)
                        }
                    )?;
                
                    let fifth = AllocatedNum::alloc(
                        cs, 
                        || {
                            let third = *third.get_value().get()?;
                            let val = *var.get_value().get()?;
                            let mut tmp = val;
                            tmp.square();
                            tmp.mul_assign(&third);
            
                            Ok(tmp)
                        }
                    )?;
                
                    cs.new_single_gate_for_trace_step(
                        &Nonlinearity5CustomGate::default(), 
                        &[], 
                        &[var.get_variable(), third.get_variable(), fifth.get_variable()], 
                        &[]
                    )?;
                
                    fifth
                }
                else {
                    let squared = AllocatedNum::alloc(
                        cs, 
                        || {
                            let mut val = *var.get_value().get()?;
                            val.square();
                            Ok(val)
                        }
                    )?;
                
                    let quad = AllocatedNum::alloc(
                        cs, 
                        || {
                            let mut val = *squared.get_value().get()?;
                            val.square();
                            Ok(val)
                        }
                    )?;
                
                    let fifth = AllocatedNum::alloc(
                        cs, 
                        || {
                            let mut val = *quad.get_value().get()?;
                            val.mul_assign(var.get_value().get()?);
            
                            Ok(val)
                        }
                    )?;
            
                    let one = E::Fr::one();
                    let mut minus_one = one;
                    minus_one.negate();
            
                    cs.new_single_gate_for_trace_step(
                        &Rescue5CustomGate::default(), 
                        &[], 
                        &[
                            var.get_variable(), squared.get_variable(), 
                            quad.get_variable(), fifth.get_variable()
                        ], 
                        &[]
                    )?;
            
                    fifth
                };

                Num::Variable(fifth_power_var)
            },
        };

        Ok(res)
    }

    // compute y = x^2 + a x + b
    fn compute_quadratic_term<CS>(cs: &mut CS, x: &Num<E>, alpha: &E::Fr, beta: &E::Fr) -> Result<Num<E>>
    where CS: ConstraintSystem<E>
    {
        let res = match x {
            Num::Constant(constant) => {
                let mut x_squared = constant.clone();
                x_squared.square();
                let mut res = *constant;
                res.mul_assign(alpha);
                res.add_assign(beta);
                res.add_assign(&x_squared);
                Num::Constant(res)
            },
            Num::Variable(var) => {
                let quadratic_term = {
                    ArithmeticTerm::from_variable(var.variable).mul_by_variable(var.variable)
                };
                let linear_term = ArithmeticTerm::from_variable_and_coeff(var.variable, alpha.clone());
                let cnst_term = ArithmeticTerm::constant(beta.clone());

                let res_var = AllocatedNum::alloc(cs, || {
                    let x = var.get_value().grab()?;
                    let mut x_squared = x.clone();
                    x_squared.square();
                    let mut res = x;
                    res.mul_assign(alpha);
                    res.add_assign(beta);
                    res.add_assign(&x_squared);
                    Ok(res)
                })?;
                let res_term = ArithmeticTerm::from_variable(res_var.variable);
                
                let mut gate = MainGateTerm::new();
                gate.add_assign(quadratic_term);
                gate.add_assign(linear_term);
                gate.add_assign(cnst_term);
                gate.sub_assign(res_term);
                cs.allocate_main_gate(gate)?;

                Num::Variable(res_var)
            },
        };

        Ok(res)
    }

    fn bricks<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()>
    {
        // Bricks(x_1, x_2, x_3) = (x_1^5, x_2 * (x_1^2 + a1 * x1 + b1), x_3 * (x_2^2 + a2 * x2 + b2))
        // Bricks is encoded as the following set of constraints:
        // y_1 = x_1 ^ 5 (using custom gate)
        // tmp_1 = x_1^2 + a1 * x1 + b1
        // y_2 = tmp_1 * x_2
        // tmp_2 = x_2^2 + a2 * x2 + b2
        // y_3 = x_3 * tmp_2
        // 4 constraints in total
        let mut new_state = RCState::default();

        // y_1 = x_1 ^ 5 (using custom gate)
        new_state[0] = self.apply_5th_power(cs, &self.state[0])?;
        // tmp_1 = x_1^2 + a1 * x1 + b1
        let tmp_1 = Self::compute_quadratic_term(cs, &self.state[1], &self.alphas[0], &self.betas[0])?;
        // y_2 = tmp_1 * x_2
        new_state[1] = tmp_1.mul(cs, &self.state[1])?;
        // tmp_2 = x_2^2 + a2 * x2 + b2
        let tmp_2 = Self::compute_quadratic_term(cs, &self.state[2], &self.alphas[1], &self.betas[1])?;
        // y_3 = x_3 * tmp_2
        new_state[2] = tmp_2.mul(cs, &self.state[2])?;

        self.state = new_state;
        Ok(())
    }

    fn concrete<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, round: usize) -> Result<()>
    {
        let mut new_state = RCState::default();
        let mut iter = self.mds_matrix.iter().zip(
            self.round_constants[3 * round..3*(round+1)].iter()).zip(new_state.0.iter_mut()
        );
        for ((row, cnst), out) in iter {
            let mut lc = LinearCombination::zero();
            for (coef, num) in row.iter().zip(self.state.0.iter()) {
                lc.add_assign_number_with_coeff(num, coef.clone());
            }
            lc.add_assign_constant(cnst.clone());
            *out = lc.into_num(cs)?;
        }

        self.state = new_state;
        Ok(())
    }

    // fn decompose(&self, val: &Option<E::Fr) -> Vec<u16> {
    //     let len = self.params.si.len();
    //     let mut res = vec![0; len];
    //     let mut repr = val.into_repr();

    //     for i in (1..self.params.si.len()).rev() {
    //         let (r, m) = utils::divide_long_using_recip::<F>(
    //             &repr,
    //             self.params.divisor_i[i],
    //             self.params.reciprokal_i[i],
    //             self.params.norm_shift_i[i],
    //         );
    //         repr = r;
    //         res[i] = m;
    //     }

    //     res[0] = repr.as_ref()[0] as u16;

    //     // just debugging
    //     if cfg!(debug_assertions) {
    //         let repr_ref = repr.as_ref();
    //         debug_assert!(repr_ref[0] < self.params.si[0] as u64);
    //         repr_ref
    //             .iter()
    //             .skip(1)
    //             .for_each(|el| debug_assert!(*el == 0));
    //     }

    //     res
    // }


    // fn bars<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()> {
    //     for elem in self.state.0.iter_mut() {
    //         let res = match in_elem {
    //             Num::Constant(cnst) => {

    //         }
    //     }

    //     Ok(())
    // }

    fn sponge_permutation<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<()> {
        self.num_squeezed = 0;

        // first concrete
        self.concrete(cs, 0)?;
        // first rounds
        for i in 1..=RC_PRE_ROUNDS_COUNT {
            self.bricks(cs)?;
            self.concrete(cs, i)?;
        }
        // bar round
        self.bars(cs)?;
        self.concrete(cs, RC_PRE_ROUNDS_COUNT + 1)?;
        // final rounds
        for i in RC_PRE_ROUNDS_COUNT + 2..=RC_TOTAL_ROUNDS_COUNT
        {
            self.bricks(cs)?;
            self.concrete(cs, i)?;
        }
        
        Ok(())
    }

    pub fn reset(&mut self) {
        self.state = RCState::default();
        self.num_squeezed = 0;
    }

    pub fn squeeze<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Num<E>> {
        if self.num_squeezed >= RC_RATE {
            self.sponge_permutation(cs)?;
        }
        let res = self.state[self.num_squeezed].clone();
        self.num_squeezed += 1;

        Ok(res)
    }

    pub fn absorb<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, elems_to_absorb: &[Num<E>]) -> Result<()>
    {
        assert!(elems_to_absorb.len() <= RC_RATE);
        for (state, elem_to_absorb) in self.state.0.iter_mut().zip(elems_to_absorb.iter()) {
            *state = state.add(cs, elem_to_absorb)?;
        }
        self.sponge_permutation(cs)
    }

    pub fn get_cur_state(&self) -> [Num<E>; RC_STATE_WIDTH] {
        self.state.0.clone()
    }
}
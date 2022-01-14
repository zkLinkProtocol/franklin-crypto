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

use super::tables::*;
use super::super::utils::*;
use super::super::tables::*;
use sha3::{digest::ExtendableOutput, digest::Update, Sha3XofReader, Shake128, digest::XofReader};

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{ Zero, One };
use std::convert::TryInto;

type Result<T> = std::result::Result<T, SynthesisError>;

pub const RC_STATE_WIDTH : usize = 3;
pub const PRE_ROUNDS_COUNT: usize = 3;
pub const POST_ROUNDS_COUNT: usize = 3;
pub const TOTAL_ROUNDS_COUNT: usize = PRE_ROUNDS_COUNT + POST_ROUNDS_COUNT;
pub const INIT_SHAKE: &'static str = "ReinforcedConcrete";


#[derive(Clone)]
pub struct RCState<E: Engine>([Num<E>; RC_STATE_WIDTH]);

impl<E: Engine> Default for RCState<E> {
    fn default() -> Self {
        RCState(<[Num<E>; RC_STATE_WIDTH]>::default())
    }
}


#[derive(Clone, Debug)]
pub struct ReinforcementConcreteGadget<E: Engine>{
    // constants 
    pub alphas: [E::Fr; 2],
    pub betas: [E::Fr; 2],
    pub p_prime: u16,
    pub s_arr: Vec<u16>,
    pub u_arr: Vec<u16>,

    pub use_optimized_fifth_power: bool,
    mds_matrix: [[E::Fr; RC_STATE_WIDTH]; RC_STATE_WIDTH],
    round_constants: [E::Fr; TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH]
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
        let modulus = repr_to_biguint(&<E::Fr as PrimeField>::char());
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
            ReinforcementConcreterHelperTable1::new(name1),
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
        shake.update(INIT_SHAKE);
        for i in <E::Fr as PrimeField>::char().as_ref() {
            shake.update(u64::to_le_bytes(*i));
        }
        let mut reader = shake.finalize_xof();

        let bytes = f64::ceil(E::Fr::NUM_BITS as f64 / 8f64) as usize;
        let words = f64::ceil(bytes as f64 / 8f64) as usize;
        let mod_ = E::Fr::NUM_BITS % 8;
        let mask = if mod_ == 0 { 0xFF } else { (1u8 << mod_) - 1 };

        let round_constants : [E::Fr; TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH] = (
            0..TOTAL_ROUNDS_COUNT * RC_STATE_WIDTH
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
            round_constants
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

    fn bricks<CS>(&self, cs: &mut CS, state: RCState<E>) -> Result<RCState<E>>
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
        new_state[0] = self.apply_5th_power(cs, &state[0])?;

        let tmp1 = match new_state[1] {
            Num::Constant(constant) => {
                let mut x_squared = *constant;
                x_squared.square();
                let mut res = *constant;
                res.mul_assign(&self.alphas[0]);
                res.add_assign(&self.betas[0]);
                res.add_assign(&x_squared);
                Num::Constant(res)
            },
            Num::Variable(var) => {
                let self_term = ArithmeticTerm::from_variable(var.variable);
                let mut constant = *cnst1;
                constant.add_assign(cnst2);
                let other_term = ArithmeticTerm::constant(constant);
                let result_term = ArithmeticTerm::from_variable(addition_result);
                let mut term = MainGateTerm::new();
                term.add_assign(self_term);
                term.add_assign(other_term);
                term.sub_assign(result_term);

                cs.allocate_main_gate(term)?;

                Num::Variable(AllocatedNum {
                    value: value,
                    variable: addition_result
                })
            },
        };
        
        Ok(new_state)
    }

    fn concrete<CS>(&self, cs: &mut CS, state: RCState<E>, round: usize) -> Result<RCState<E>>
    where CS: ConstraintSystem<E> 
    {
        let mut new_state = RCState::default();
        let coefs = 
        for (coefs, round_constant) in 
    }


   
    // we expect input to be well formed and padded
    pub fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, message: &[Num<E>]) -> Result<[Num<E>; 8]>
    {    
        // we assume that input is already well-padded
        assert!(message.len() % 16 == 0);
        
        let mut regs = Sha256Registers {
            a: Num::Constant(self.iv[0].clone()).into(),
            b: Num::Constant(self.iv[1].clone()).into(),
            c: Num::Constant(self.iv[2].clone()).into(),
            d: Num::Constant(self.iv[3].clone()).into(),
            e: Num::Constant(self.iv[4].clone()).into(),
            f: Num::Constant(self.iv[5].clone()).into(),
            g: Num::Constant(self.iv[6].clone()).into(),
            h: Num::Constant(self.iv[7].clone()).into(),
        };


        for block in message.chunks(16) {
            let expanded_block = self.message_expansion(cs, block)?;
            regs = self.sha256_inner_block(cs, regs, &expanded_block[..], &self.round_constants)?;
        }

        let res = [
            self.extact_32_bits_from_tracked_num(cs, regs.a)?,
            self.extact_32_bits_from_tracked_num(cs, regs.b)?,
            self.extact_32_bits_from_tracked_num(cs, regs.c)?,
            self.extact_32_bits_from_tracked_num(cs, regs.d)?,
            self.extact_32_bits_from_tracked_num(cs, regs.e)?,
            self.extact_32_bits_from_tracked_num(cs, regs.f)?,
            self.extact_32_bits_from_tracked_num(cs, regs.g)?,
            self.extact_32_bits_from_tracked_num(cs, regs.h)?,
        ];

        Ok(res)
    }
}
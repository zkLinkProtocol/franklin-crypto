use super::*;
use std::ops::Index;
use crate::plonk::circuit::SomeArithmetizable;
use crate::plonk::circuit::bigint::traits::*;

use crate::bellman::pairing::bn256::Fq as Bn256Fq;
use crate::bellman::pairing::bn256::Fq2 as Bn256Fq2;
use crate::bellman::pairing::bn256::Fq6 as Bn256Fq6;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ6_C1 as BN256_FROBENIUS_COEFF_FQ6_C1;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ6_C2 as BN256_FROBENIUS_COEFF_FQ6_C2;
use crate::bellman::pairing::bn256::fq::FROBENIUS_COEFF_FQ12_C1 as BN256_FROBENIUS_COEFF_FQ12_C1;

use crate::bellman::pairing::bls12_381::Fq as Bls12Fq;
use crate::bellman::pairing::bls12_381::Fq2 as Bls12Fq2;

use super::super::curve::secp256k1::fq::Fq as SecpFq;
use super::super::curve::secp256k1::fq2::Fq2 as SecpFq2;


const EXT_DEGREE: usize = 3;
pub trait Extension6Params<E: Engine, F: Field>: FieldExtensionParams<E, F, EXT_DEGREE> {
    const NON_RESIDUE: (u64, u64);
    const FROBENIUS_COEFFS_C1: [Self::BaseField; 6];
    const FROBENIUS_COEFFS_C2: [Self::BaseField; 6];
    const FROBENIUS_COEFFS_FQ12_C1:  [Self::BaseField; 12];
  
    fn non_residue() -> (u64,u64) { Self::NON_RESIDUE.clone() }
}
pub type Fp6<E, F, T> = ExtField<E, F, EXT_DEGREE, T>;


#[derive(Clone)]
pub struct Bn256Extension6Params {}
impl<E: Engine> FieldExtensionParams<E, Bn256Fq6, EXT_DEGREE> for Bn256Extension6Params {
    type BaseField = Bn256Fq2;
    type BaseCircuitField = Fp2<E, Bn256Fq2, Bn256Extension2Params>;
                
    fn convert_to_structured_witness(arr: [Self::BaseField; EXT_DEGREE]) -> Bn256Fq6 {
        Bn256Fq6 { c0: arr[0], c1: arr[1], c2: arr[2] }
    }

    fn convert_from_structured_witness(val: Bn256Fq6) -> [Self::BaseField; EXT_DEGREE] {
        [val.c0, val.c1, val.c2]
    }
}
impl<E: Engine> Extension6Params<E, Bn256Fq6> for Bn256Extension6Params {
    const NON_RESIDUE: (u64, u64) = (9, 1);
    const FROBENIUS_COEFFS_C1: [Bn256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C1;
    const FROBENIUS_COEFFS_C2: [Bn256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C2;
    const FROBENIUS_COEFFS_FQ12_C1: [Bn256Fq2; 12] = BN256_FROBENIUS_COEFF_FQ12_C1;
}


impl<E: Engine, F: Field, T: Extension6Params<E, F>> std::fmt::Display for ExtField<E, F, EXT_DEGREE, T> 
where T::BaseCircuitField : std::fmt::Display
{
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp6({} + {} * u + {} * u^2)", self[0], self[1], self[2])
    }
}

impl<E: Engine, F: Field, T: Extension6Params<E, F>> std::fmt::Debug for ExtField<E, F, EXT_DEGREE, T> 
where T::BaseCircuitField : std::fmt::Debug
{
    #[inline(always)]
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fp2({:?} + {:?} * u + {:?} * u^2)", self[0], self[1], self[2])
    }
}


impl<E: Engine, F: Field, T: Extension6Params<E, F>> CircuitField<E, F> for ExtField<E, F, EXT_DEGREE, T> {  
    #[track_caller]
    fn mul_with_chain<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError> 
    {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.21
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) v2 = a2 * b2
        // 4) c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        // 5) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        // 6) c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let v0 = first[0].mul_by(cs, &second[0])?;  
        let v1 = first[1].mul_by(cs, &second[1])?; 
        let v2 = first[2].mul_by(cs, &second[2])?;
        let tempa01 = first[0].add(cs, &first[1])?;  //tempaij=ai+aj
        let tempa12 = first[1].add(cs, &first[2])?;  
        let tempa02 = first[0].add(cs, &first[2])?; 
        let tempb01 = second[0].add(cs, &second[1])?; //tempbij=bi+bj
        let tempb12 = second[1].add(cs, &second[2])?;  
        let tempb02 = second[0].add(cs, &second[2])?;
        let alpha = T::non_residue();

        // c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        let mut sub_chain = FieldElementsChain::new();
        sub_chain.add_neg_term(&v1).add_neg_term(&v2);
        let mut c0 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(
            cs, &tempa12, &tempb12, sub_chain
        )?;
        let mut sub_chain = chain.get_coordinate_subchain(0);
        sub_chain.add_pos_term(&v0);
        c0 = c0.mul_by_small_constant_with_chain(cs, alpha, sub_chain)?;
        
        // c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        let scaled_v2 = v2.mul_by_small_constant(cs, alpha)?;
        let mut sub_chain = chain.get_coordinate_subchain(1);
        sub_chain.add_neg_term(&v0).add_neg_term(&v1).add_pos_term(&scaled_v2);
        let c1 = Fp2::mul_with_chain(cs, &tempa01, &tempb01, sub_chain)?;
           
        // c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let mut sub_chain = chain.get_coordinate_subchain(2);
        sub_chain.add_neg_term(&v0).add_neg_term(&v2).add_pos_term(&v1);
        let c2 = Fp2::mul_with_chain(cs, &tempa02, &tempb02, sub_chain)?;

        let res = Self::from_coordinates([c0, c1, c2]);
        Ok(res)
    }

    #[track_caller]
    fn constraint_fma<CS: ConstraintSystem<E>>(
        cs: &mut CS, first: &Self, second: &Self, chain: FieldElementsChain<E, F, Self>
    ) -> Result<(), SynthesisError> 
    {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.21
        // 1) v0 = a0 * b0
        // 2) v1 = a1 * b1
        // 3) v2 = a2 * b2
        // 4) c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        // 5) c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        // 6) c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let v0 = first[0].mul_by(cs, &second[0])?;  
        let v1 = first[1].mul_by(cs, &second[1])?; 
        let v2 = first[2].mul_by(cs, &second[2])?;
        let tempa01 = first[0].add(cs, &first[1])?;  //tempaij=ai+aj
        let tempa12 = first[1].add(cs, &first[2])?;  
        let tempa02 = first[0].add(cs, &first[2])?; 
        let tempb01 = second[0].add(cs, &second[1])?; //tempbij=bi+bj
        let tempb12 = second[1].add(cs, &second[2])?;  
        let tempb02 = second[0].add(cs, &second[2])?;
        let alpha = T::non_residue();

        // c0 = ((a1 + a2) * (b1 + b2) - v1 - v2) * \alpha + v0
        let mut subchain = FieldElementsChain::new();
        subchain.add_neg_term(&v1).add_neg_term(&v2);
        let c0 = <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::mul_with_chain(cs, &tempa12, &tempb12, subchain)?;
        let mut subchain = chain.get_coordinate_subchain(0);
        subchain.add_pos_term(&v0);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::constraint_mul_by_small_constant_with_chain(cs, &c0, alpha, subchain)?;
        
        // c1 = (a0 + a1) * (b0 + b1) - v0 - v1 + \alpha * v2
        let scaled_v2 = v2.mul_by_small_constant(cs, alpha)?;
        let mut subchain = chain.get_coordinate_subchain(1);
        subchain.add_neg_term(&v0).add_neg_term(&v1).add_pos_term(&scaled_v2);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::constraint_fma(cs,  &tempa01, &tempb01, subchain)?;
           
        // c2 = (a0 + a2) * (b0 + b2) - v0 - v2 + v1
        let mut subchain = chain.get_coordinate_subchain(2);
        subchain.add_neg_term(&v0).add_neg_term(&v2).add_pos_term(&v1);
        <T as FieldExtensionParams<E, F, EXT_DEGREE>>::BaseCircuitField::constraint_fma(cs, &tempa02, &tempb02, subchain)
    }
 
    fn square<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // multiplication Guide to Pairing-based Cryptography, Mbrabet, Joye  Algorithm 5.22
        // 1) v0 = 2 * a1 * a2
        // 2) v1 = a0^2
        // 3) c0 = \alpha * v0 + v1
        // 4) v2 = 2 * a0 * a1;
        // 5) v3 = a2^2
        // 6) c1 = \alpha * v2 + v3 
        // 7) v4 = a0 - a1 + q2
        // 8) c2 = v4^2 + v2 - v3 + v0 - v1
        let alpha = T::non_residue();
        let a1_scaled = self[1].double(cs)?;
        let v0 = a1_scaled.mul(cs, &self[2])?;
        let v1 = self[0].square(cs)?;
        let v2 = a1_scaled.mul(cs, &self[0])?;
        let v3 = self[2].square(cs)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&self[0]).add_neg_term(&self[1]).add_pos_term(&self[2]);
        let v4 = Fp2::collapse_chain(cs, chain)?;
        
        // c0 = \alpha * v0 + v1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v1);
        let c0 = v0.mul_by_small_constant_with_chain(cs, alpha, chain)?;

        // c1 = \alpha * v2 + v3 
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v3);
        let c1 = v2.mul_by_small_constant_with_chain(cs, alpha, chain)?;

        // c2 = v4^2 + v2 - v3 + v0 - v1
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&v2).add_neg_term(&v3).add_pos_term(&v0).add_neg_term(&v1);
        let c2 = v4.square_with_chain(cs, chain)?;
       
        Ok(Self::from_coordinates([c0, c1, c2]))
    }

    pub fn div_with_chain<CS: ConstraintSystem<E> >(
        cs: &mut CS, num: FieldElementsChain<E, F, Self>, denom: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let params = denom[0][0].representation_params;
        let res_wit = match (num.get_value(), denom.get_value()) {
            (Some(num), Some(denom)) => {
                let denom_inv = denom.inverse().unwrap();
                let mut res = num;
                res.mul_assign(&denom_inv);
                Some(res)
            },
            _ => None
        };
        
        let res = if num.is_constant() && denom.is_constant() {
            Self::constant(res_wit.unwrap(), params)
        } else {
            let res = Self::alloc(cs, res_wit, params)?;
            let chain = num.negate();
            Self::constraints_fma(cs, &res, denom, chain)?;
            res
        };

        Ok(res)
    }

    fn frobenius_power_map<CS>(&self, cs: &mut CS, power:usize)-> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        match power % 6 {
            0 | 1 | 2 | 3 => {},
            _ => {
                unreachable!("can not reach power {}", power);// May be change to option and none?
            }
        }

        let params= self[0][0].representation_params;
        let frob_c1 = Fp2::constant(T::FROBENIUS_COEFFS_C1[power % 6], params);
        let frob_c2 =  Fp2::constant(T::FROBENIUS_COEFFS_C2[power % 6], params);

        let new_c0 = self[0].frobenius_power_map(cs, power)?;
        let mut new_c1 = self[1].frobenius_power_map(cs, power)?;
        let mut new_c2 = self[2].frobenius_power_map(cs, power)?;
        new_c1 = new_c1.mul(cs, &frob_c1)?;
        new_c2 = new_c2.mul(cs, &frob_c2)?;
        
        let res = Self::from_coordinates([new_c0, new_c1, new_c2]);
        let actual_value = self.get_value().map(|x| {
            let mut tmp = x;
            tmp.frobenius_map(power);
            tmp
        });
        assert_eq!(res.get_value(), actual_value);

        // TODO: get rid of this
        self.get_value().map(|x| {
            let mut tmp = x;
            tmp.frobenius_map(2);
            tmp.frobenius_map(1);
            let mut qr = x;
            qr.frobenius_map(3);
            assert_eq!(tmp, qr);

            qr
        });

        Ok(res)
    }   

    fn square_with_chain<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, chain: FieldElementsChain<E, F, Self>
    ) -> Result<Self, SynthesisError> {
        unimplemented!();
    } 
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::*;
    use crate::bellman::pairing::bn256::fq6::Fq6 as Bn256Fq6;
    use crate::plonk::circuit::curve::*;
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::bellman::plonk::better_better_cs::gates::selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext;
    use rand::{XorShiftRng, SeedableRng, Rng};
    use crate::bellman::plonk::better_better_cs::cs::*;
    use crate::bellman::kate_commitment::{Crs, CrsForMonomialForm};
    use crate::bellman::worker::Worker;

    #[test]
    fn test_fp6_arithmetic_for_bn256_curve() {
        const LIMB_SIZE: usize = 80;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let mut rng = rand::thread_rng();
        let a_wit: Bn256Fq6 = rng.gen();
        let b_wit: Bn256Fq6 = rng.gen();
        let mut res_wit = a_wit.clone();
        res_wit.mul_assign(&b_wit);

        let a = Fp6::<_, _, Bn256Extension6Params>::alloc(
            &mut cs, Some(a_wit), &circuit_params.base_field_rns_params
        ).unwrap();
        let b = Fp6::alloc(&mut cs, Some(b_wit), &circuit_params.base_field_rns_params).unwrap();  
        let mut actual_res = Fp6::alloc(&mut cs, Some(res_wit), &circuit_params.base_field_rns_params).unwrap();  
        
        let counter_start = cs.get_current_step_number();
        let mut res = Fp6::mul(&mut cs, &a, &b).unwrap();
        let counter_end = cs.get_current_step_number();
        println!("num of gates: {}", counter_end - counter_start);
        
        Fp6::enforce_equal(&mut cs, &mut res, &mut actual_res).unwrap();
        assert!(cs.is_satisfied()); 
    }
}
  
use super::*;
use crate::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::plonk::circuit::boolean::Boolean;
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

use crate::bellman::{
    SynthesisError,
};
use plonk::circuit::bigint::*;
use plonk::circuit::hashes_with_tables::utils::IdentifyFirstLast;


#[derive(Clone, Debug)]
pub(crate) struct Combiner2<'a, E: Engine, G: GenericCurveAffine, T, S: Selector<'a, E, G, T>> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>
{
    entries: Vec<AffinePoint<'a, E, G, T>>, // raw elements P1, P2, ..., Pn
    selector_impl: S,
    initial_point: AffinePointChecked<'a, E, G, T>,
    params: &'a CurveCircuitParameters<E, G, T>,
}

impl<'a, E: Engine, G: GenericCurveAffine, T, S: Selector<'a, E, G, T>> Combiner2<'a, E, G, T, S> 
where <G as GenericCurveAffine>::Base: PrimeField, T: Extension2Params<G::Base>, G: rand::Rand
{
    pub fn postprocess<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.selector_impl.postprocess(cs)
    }
    
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, entries: &[AffinePoint<'a, E, G, T>], geometry: MultiExpGeometry
    ) -> Result<Self, SynthesisError> {
        let first_elem = entries.get(0).expect("Entries must be nonempty");
        let params = first_elem.circuit_params;

        let get_bit_at_pos = |num: u64, pos: usize| -> bool {
            (num >> pos) & 1 != 0
        };
        let extend_addr = |num: u64, pos: usize, msb: bool| -> u64 {
            if msb { (1u64 << (pos+1)) + num } else { num }
        }; 
        
        let initial = AffinePointChecked::from(first_elem.clone());
        let mut entries = entries.to_vec();
        let mut workpad : Vec<(u64, AffinePointChecked<'a, E, G, T>)> = vec![(1, initial)];
        let mut pos = 0;

        for (_is_first, _is_last, elem) in entries[1..].iter_mut().identify_first_last() {
            let mut new_working_pad = Vec::with_capacity(workpad.len() << 1);
            for (addr, acc) in workpad.iter_mut() {
                let msb = get_bit_at_pos(*addr, pos);
                if msb { 
                    new_working_pad.push((extend_addr(*addr, pos, !msb), acc.sub_mixed(cs, elem)?));
                    new_working_pad.push((extend_addr(*addr, pos, msb), acc.add_mixed(cs, elem)?));   
                }
                else {
                    new_working_pad.push((extend_addr(*addr, pos, !msb), acc.add_mixed(cs, elem)?));   
                    new_working_pad.push((extend_addr(*addr, pos, msb), acc.sub_mixed(cs, elem)?));
                }
            };
            pos += 1;
            workpad = new_working_pad
        }
        assert_eq!(workpad.len(), 1 << (entries.len() - 1));
        
        let mut precompute = Vec::with_capacity(workpad.len());
        let mut initial_point = AffinePointChecked::infty(params);

        for (_is_first, is_last, elem) in workpad.into_iter().identify_first_last() {
            let (addr, point) = elem;
            if is_last {
                initial_point = point.clone();
            }
            let point_affine = point.convert_to_affine_or_uninitialized(cs)?;
            precompute.push((addr, point_affine));
        }

        let mut selector = S::new(geometry);
        selector.absorb_precompute(cs, precompute)?;

        Ok(Combiner2 {
            entries,
            selector_impl: selector,
            initial_point,
            params
        })
    }

    fn select<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean]
    ) -> Result<AffinePointChecked<'a, E, G, T>, SynthesisError> {
        let candidate = self.selector_impl.select(cs, bits, self.params)?;
        let is_point_at_infty = FieldElement::is_zero(&mut candidate.get_y(), cs)?;
        let infty = AffinePointChecked::infty(self.params);
        let checked_candidate = AffinePointChecked::conditionally_select(
            cs, &is_point_at_infty, &infty, &AffinePointChecked::from(candidate)
        )?;
        Ok(checked_candidate)
    }

    fn select_last<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, bits: &[Boolean]
    ) -> Result<AffinePointChecked<'a, E, G, T>, SynthesisError> {
        // on every iteration of the inner loop (except the last one) of the point by scalar mul algorithm
        // we want to retrieve the point which is dependent on bits as follows:
        // bits = [b_0, b_1, .., b_n] -> /sum (2* b_i - 1) P_i = A
        // on the last iteration we do however want to add the point \sum (b_i - 1) * P_i = B
        // if we denote the starting value of accumulator = /sum P_i as C
        // then it is obvious that the following relation always holds: A - C = 2 * B
        // hence we reduced the computation to one subtraction and one doubling
        let mut a = self.select(cs, &bits)?;
        let mut a_minus_c = a.sub(cs, &mut self.initial_point)?;
        AffinePointChecked::halving(&mut a_minus_c, cs)
    }

    fn get_initial(&self) -> AffinePointChecked<'a, E, G, T> {
        self.initial_point.clone()
    }
}



// NB: works only if there are no points of order 2 on the curve
// So it al least works for all our three curves of interest
#[derive(Clone, Debug)]
pub struct AffinePointChecked<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>>  
where <G as GenericCurveAffine>::Base: PrimeField 
{
    inner: AffinePoint<'a, E, G, T>,
    is_infty: Boolean,
}

impl<'a, E, G, T> From<AffinePoint<'a, E, G, T>> for AffinePointChecked<'a, E, G, T>
where E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>, <G as GenericCurveAffine>::Base: PrimeField {
    fn from(value: AffinePoint<'a, E, G, T>) -> Self {
        AffinePointChecked {
            inner: value,
            is_infty: Boolean::Constant(false),
        }
    }
}

impl<'a, E: Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> AffinePointChecked<'a, E, G, T>
where <G as GenericCurveAffine>::Base: PrimeField, G: rand::Rand {
    pub fn infty(circuit_params: &'a CurveCircuitParameters<E, G, T>) -> Self {
        AffinePointChecked {
            inner: AffinePoint::generator(circuit_params),
            is_infty: Boolean::Constant(true),
        }
    }

    pub fn is_constant(&self) -> bool {
        self.inner.is_constant()
    }

    pub fn convert_to_affine_or_uninitialized<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS
    ) -> Result<AffinePoint<'a, E, G, T>, SynthesisError> 
    {
        let zero = FieldElement::zero(&self.inner.circuit_params.base_field_rns_params);
        let y = FieldElement::conditionally_select(cs, &self.is_infty, &zero, &self.inner.y)?;
        let res = unsafe { AffinePoint::from_xy_unchecked(self.inner.get_x(), y, &self.inner.circuit_params) };
        Ok(res)
    }

    pub fn get_value(&self) -> Option<G> {
        self.is_infty.get_value().map(|flag| if flag { Some(G::zero()) } else { self.inner.value } ).flatten()
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        res.inner = res.inner.negate(cs)?;
        Ok(res)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let mut res = self.clone();
        res.inner = res.inner.conditionally_negate(cs, flag)?;
        Ok(res)
    }
   
    pub fn conditionally_select<CS: ConstraintSystem<E>>(
        cs: &mut CS, flag: &Boolean, first: &Self, second: &Self
    ) -> Result<Self, SynthesisError> 
    {
        let inner = AffinePoint::conditionally_select(cs, flag, &first.inner, &second.inner)?;
        let is_infty = Boolean::conditionally_select(cs, flag, &first.is_infty, &second.is_infty)?;
        Ok(AffinePointChecked { inner, is_infty })
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let mut res = self.clone();
        res.inner = res.inner.double(cs)?;
        Ok(res)
    }

    #[track_caller]
    pub fn add_mixed<CS>(&mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let xs_are_equal = FieldElement::equals(cs, &mut self.inner.x, &mut other.x)?;
        let mut other_negated_y = other.y.negate(cs)?;
        let ys_are_equal = FieldElement::equals(cs, &mut self.inner.y, &mut other_negated_y)?;
        let coords_are_equal = Boolean::and(cs, &xs_are_equal, &ys_are_equal)?;

        let lambda_for_double = {
            // lambda = (3 x^2) / (2 * y) 
            let x_squared = self.inner.x.square(cs)?;
            let x_squared_mul_3 = x_squared.scale(cs, 3)?;
            let two_y = self.inner.y.double(cs)?;
            FieldElement::div(&x_squared_mul_3, cs, &two_y)?
        };
        let lambda_for_add = {
            let mut chain = FieldElementsChain::new();
            let x_eq_flag_as_fe = FieldElement::from_boolean(&xs_are_equal, &other.circuit_params.base_field_rns_params);
            chain.add_pos_term(&other.x).add_neg_term(&self.inner.x).add_pos_term(&x_eq_flag_as_fe);
            let denom = FieldElement::collapse_chain(cs, chain)?;
            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&other.y).add_neg_term(&self.inner.y);
            FieldElement::div_with_chain(cs, chain, &denom)?
        };
        let lambda = FieldElement::conditionally_select(cs, &xs_are_equal, &lambda_for_double, &lambda_for_add)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.inner.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        let selected_x = FieldElement::conditionally_select(cs, &self.is_infty, &other.x, &new_x)?;
        let selected_y = FieldElement::conditionally_select(cs, &self.is_infty, &other.y, &new_y)?;  

        let inner = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, self.inner.circuit_params) };
        let is_infty = Boolean::and(cs, &coords_are_equal, &self.is_infty.not())?;
        Ok(AffinePointChecked { inner, is_infty})
    }

    pub fn double_and_add_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::double(&self, cs)?;
        tmp.add_mixed(cs, other)
    }  

    pub fn sub_mixed<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut AffinePoint<'a, E, G, T>
    ) -> Result<Self, SynthesisError> {
        let mut tmp = AffinePoint::negate(other, cs)?;
        self.add_mixed(cs, &mut tmp)
    }

    pub fn mul_by_scalar_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS, point: &mut AffinePoint<'a, E, G, T>, scalar: &mut FieldElement<'a, E, G::Scalar> 
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        let res = Self::mul_by_scalar_checked_impl(cs, point, scalar)?;
        let AffinePointChecked { inner, is_infty } = res;
        Ok((inner, is_infty))
    }

    #[track_caller]
    fn mul_by_scalar_checked_impl<CS: ConstraintSystem<E>>(
        cs: &mut CS, point: &mut AffinePoint<'a, E, G, T>, scalar: &mut FieldElement<'a, E, G::Scalar> 
    ) -> Result<Self, SynthesisError> {
        if scalar.is_constant() {
            unimplemented!();
        }
        let params = point.circuit_params;
        let aux_data = AffinePoint::compute_endo_aux_data(cs, point, scalar)?;
        let point_minus_point_endo = aux_data.point.sub_unequal_unchecked(cs, &aux_data.point_endo)?;
        let point_plus_point_endo = aux_data.point.add_unequal_unchecked(cs, &aux_data.point_endo)?;

        let mut acc = Self::from(point_plus_point_endo.clone());
        let iter = aux_data.point_scalar_decomposition[1..].iter().zip(
            aux_data.point_endo_scalar_decomposition[1..].iter()
        ).rev();

        for (k1_bit, k2_bit) in iter {
            let xor_flag = Boolean::xor(cs, &k1_bit, &k2_bit)?;
            let selected_x = FieldElement:: conditionally_select(
                cs, &xor_flag, &point_minus_point_endo.get_x(), &point_plus_point_endo.get_x()
            )?;
            let tmp_y = FieldElement::conditionally_select(
                cs, &xor_flag, &point_minus_point_endo.get_y(), &point_plus_point_endo.get_y()
            )?;
            let selected_y = tmp_y.conditionally_negate(cs, &k1_bit.not())?;
            let mut tmp = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, params) };
            acc = acc.double_and_add_mixed(cs, &mut tmp)?;
        }

        let k1_bit = aux_data.point_scalar_decomposition.first().unwrap();
        let k2_bit = aux_data.point_endo_scalar_decomposition.first().unwrap();
        let acc_is_unchanged = Boolean::and(cs, &k1_bit, &k2_bit)?; 
        let mut tmp = AffinePoint::conditionally_select(cs, &k2_bit, &aux_data.point, &point_plus_point_endo)?;
        tmp = AffinePoint::conditionally_select(cs, &k1_bit, &aux_data.point_endo, &tmp)?;
        let skew_acc = acc.sub_mixed(cs, &mut tmp)?;
        acc = Self::conditionally_select(cs, &acc_is_unchanged, &acc, &skew_acc)?;
        Ok(acc)
    }

    #[track_caller]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError> 
    where CS: ConstraintSystem<E>
    {
        let xs_are_equal = FieldElement::equals(cs, &mut self.inner.x, &mut other.inner.x)?;
        let mut other_negated_y = other.inner.y.negate(cs)?;
        let ys_are_equal = FieldElement::equals(cs, &mut self.inner.y, &mut other_negated_y)?;
        let coords_are_equal = Boolean::and(cs, &xs_are_equal, &ys_are_equal)?;

        let lambda_for_double = {
            // lambda = (3 x^2) / (2 * y) 
            let x_squared = self.inner.x.square(cs)?;
            let x_squared_mul_3 = x_squared.scale(cs, 3)?;
            let two_y = self.inner.y.double(cs)?;
            FieldElement::div(&x_squared_mul_3, cs, &two_y)?
        };
        let lambda_for_add = {
            let mut chain = FieldElementsChain::new();
            let x_eq_flag_as_fe = FieldElement::from_boolean(
                &xs_are_equal, &other.inner.circuit_params.base_field_rns_params
            );
            chain.add_pos_term(&other.inner.x).add_neg_term(&self.inner.x).add_pos_term(&x_eq_flag_as_fe);
            let denom = FieldElement::collapse_chain(cs, chain)?;
            let mut chain = FieldElementsChain::new();
            chain.add_pos_term(&other.inner.y).add_neg_term(&self.inner.y);
            FieldElement::div_with_chain(cs, chain, &denom)?
        };
        let lambda = FieldElement::conditionally_select(cs, &xs_are_equal, &lambda_for_double, &lambda_for_add)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.x).add_neg_term(&other.inner.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.inner.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.inner.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        // resulting_inner is equal to:
        // [self.is_infty] -> other.inner, other.is_infty -> self.inner, and (new_x, new_y) otherwise
        let mut selected_x = FieldElement::conditionally_select(cs, &self.is_infty, &other.inner.x, &new_x)?;
        selected_x = FieldElement::conditionally_select(cs, &other.is_infty, &self.inner.x, &selected_x)?;
        let mut selected_y = FieldElement::conditionally_select(cs, &self.is_infty, &other.inner.y, &new_y)?;
        selected_y = FieldElement::conditionally_select(cs, &other.is_infty, &self.inner.y, &selected_y)?;
        let inner = unsafe { AffinePoint::from_xy_unchecked(selected_x, selected_y, self.inner.circuit_params) };
        
        // is_infty = either booth_are_infty or both are not infty and coordinates are equal
        let both_is_infty = Boolean::and(cs, &self.is_infty, &other.is_infty)?;
        let tmp_check = Boolean::and(cs, &both_is_infty.not(), &coords_are_equal)?;
        let is_infty = Boolean::or(cs, &both_is_infty, &tmp_check)?;

        Ok(AffinePointChecked { inner, is_infty})
    }

    pub fn double_and_add<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::double(&self, cs)?;
        tmp.add(cs, other)
    }  

    pub fn sub<CS: ConstraintSystem<E>>(
        &mut self, cs: &mut CS, other: &mut Self
    ) -> Result<Self, SynthesisError> {
        let mut tmp = Self::negate(other, cs)?;
        self.add(cs, &mut tmp)
    }

    pub fn is_infty(&self) -> Boolean {
        self.is_infty
    }

    pub fn enforce_equal<CS: ConstraintSystem<E>>(cs: &mut CS, left: &Self, right: &Self) -> Result<(), SynthesisError> 
    {
        let gen = AffinePoint::generator(left.inner.circuit_params);
        Boolean::enforce_equal(cs, &left.is_infty, &right.is_infty)?;
        let mut lhs = AffinePoint::conditionally_select(cs, &left.is_infty, &gen, &left.inner)?;
        let mut rhs = AffinePoint::conditionally_select(cs, &right.is_infty, &gen, &right.inner)?;
        AffinePoint::enforce_equal(cs, &mut lhs, &mut rhs)
    }

    fn enforce_equal_strict<CS: ConstraintSystem<E>>(
        cs: &mut CS, left: &mut Self, right: &mut Self
    ) -> Result<(), SynthesisError> {
        Boolean::enforce_equal(cs, &left.is_infty, &right.is_infty)?;
        AffinePoint::enforce_equal(cs, &mut left.inner, &mut right.inner)
    }

    pub fn halving<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let inner_wit = self.inner.get_value().map(|x| {
            // if x = 2 * y and order of group is n - odd prime, then:
            // (n-1)/2 * x = (n-1) * y = -y
            let mut scalar = <G::Scalar as PrimeField>::char();
            scalar.div2();
            let mut res = x.mul(scalar).into_affine();
            res.negate();
            res
        });

        let inner_halved = AffinePoint::alloc(cs, inner_wit, self.inner.circuit_params)?;
        inner_halved.enforce_if_on_curve(cs)?;
        let halved = AffinePointChecked { inner: inner_halved, is_infty: self.is_infty };
        let mut initial = halved.double(cs)?;
        Self::enforce_equal_strict(cs, self, &mut initial)?;
        
        Ok(halved)
    }

    pub fn multiexp_checked<CS: ConstraintSystem<E>>(
        cs: &mut CS, points: &mut [AffinePoint<'a, E, G, T>], scalars: &mut [FieldElement<'a, E, G::Scalar>],
        geometry: MultiExpGeometry,
    ) -> Result<(AffinePoint<'a, E, G, T>, Boolean), SynthesisError> {
        assert_eq!(scalars.len(), points.len());
        let params = points[0].circuit_params;
        let mut acc = AffinePointChecked::infty(params);
        let mut idx = 0;

        while idx < points.len() {
            let chunk_size = std::cmp::min(points.len() - idx, geometry.width);
            let mut chunk_res = if chunk_size == 1 {
                Self::mul_by_scalar_checked_impl(cs, &mut points[idx], &mut scalars[idx])?
            } else {
                let cur_chunk_geometry = MultiExpGeometry { strategy: geometry.strategy, width: chunk_size };
                match geometry.strategy {
                    MultiexpStrategy::SelectionTree => Self::multiexp_checked_impl::<_, TreeSelector<'a, E, G, T>>(
                        cs, &mut points[idx..idx+chunk_size], &mut scalars[idx..idx+chunk_size], cur_chunk_geometry
                    )?,
                    MultiexpStrategy::HashSetsBasedRam | MultiexpStrategy::WaksmanBasedRam => {
                        Self::multiexp_checked_impl::<_, Memory<'a, E, G, T>>(
                            cs, &mut points[idx..idx+chunk_size], &mut scalars[idx..idx+chunk_size], cur_chunk_geometry
                        )?
                    },
                }
               
            };
            acc = if idx == 0 {
                chunk_res
            } else {
                acc.add(cs, &mut chunk_res)?
            };
            idx += chunk_size;
        }

        let Self { inner, is_infty } = acc;
        Ok((inner, is_infty))
    }

    #[track_caller]
    fn multiexp_checked_impl<CS: ConstraintSystem<E>, S: Selector<'a, E, G, T>>(
        cs: &mut CS, points: &[AffinePoint<'a, E, G, T>], scalars: &mut [FieldElement<'a, E, G::Scalar>],
        geometry: MultiExpGeometry,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(points.len(), scalars.len());
        assert!(scalars.len() > 1);
     
        struct Multizip<T>(Vec<T>);
        impl<T> Iterator for Multizip<T>
        where T: Iterator,
        {
            type Item = Vec<T::Item>;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.iter_mut().map(Iterator::next).collect()
            }
        }
                
        let mut points_unrolled = Vec::with_capacity(points.len() << 1);
        let mut scalars_unrolled = Vec::with_capacity(points.len() << 1);
        for (mut scalar, point) in scalars.iter_mut().zip(points.iter()) { 
            let aux_data = AffinePoint::compute_endo_aux_data(cs, point, &mut scalar)?;
            scalars_unrolled.push(aux_data.point_scalar_decomposition.into_iter().rev());
            scalars_unrolled.push(aux_data.point_endo_scalar_decomposition.into_iter().rev());

            points_unrolled.push(aux_data.point);
            points_unrolled.push(aux_data.point_endo);
        }

        let mut combiner = Combiner2::<E, G, T, S>::new(cs, &points_unrolled, geometry)?;
        let mut acc = combiner.get_initial();
       
        for (_, is_last, bits) in Multizip(scalars_unrolled).identify_first_last() {
            if !is_last {
                let mut to_add = combiner.select(cs, &bits)?;
                acc = acc.double_and_add(cs, &mut to_add)?
            }
            else {
                let mut to_add  = combiner.select_last(cs, &bits)?;
                acc = acc.add(cs, &mut to_add)?;
            }
        }

        combiner.postprocess(cs)?;
        Ok(acc)
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256;
    use crate::bellman::{Field, PrimeField, GenericCurveAffine, GenericCurveProjective};
    use crate::plonk::circuit::Width4WithCustomGates;
    use crate::plonk::circuit::Engine;
    use crate::plonk::circuit::SynthesisError;
    use bellman::plonk::better_better_cs::gates::{
        selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext, self
    };
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::plonk::better_better_cs::cs::*;
    use crate::plonk::circuit::curve::sw_affine_checked::Extension2Params;
    use plonk::circuit::curve::CurveCircuitParameters;
   
    struct TestCheckedAffineCurveCircuit<E:Engine, G: GenericCurveAffine, T: Extension2Params<G::Base>> 
    where <G as GenericCurveAffine>::Base: PrimeField
    {
        circuit_params: CurveCircuitParameters<E, G, T>
    }
    
    impl<E: Engine, G: GenericCurveAffine + rand::Rand, T> Circuit<E> for TestCheckedAffineCurveCircuit<E, G, T> 
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
            let a_wit: G = rng.gen();
            let mut a = AffinePointChecked::from(AffinePoint::alloc(cs, Some(a_wit), &self.circuit_params)?);
            let b_wit: G = rng.gen();
            let mut b = AffinePointChecked::from(AffinePoint::alloc(cs, Some(b_wit), &self.circuit_params)?);
            let mut a_neg = a.negate(cs)?;
            let mut infty_1 = AffinePointChecked::infty(&self.circuit_params);
            let mut infty_2 = AffinePointChecked::infty(&self.circuit_params);

            // corner cases:
            // 1) add: infty + infty
            let res = infty_1.add(cs, &mut infty_2)?;
            AffinePointChecked::enforce_equal(cs, &res, &infty_1)?;

            // 2) add: infty + a
            let res = infty_1.add(cs, &mut a)?;
            AffinePointChecked::enforce_equal(cs, &res, &a)?;

            // 3) add: a + (-a)
            let res = a.add(cs, &mut a_neg)?;
            AffinePointChecked::enforce_equal(cs, &res, &infty_1)?;

            // 4) mixed add: infty + a
            let res = infty_1.add_mixed(cs, &mut a.inner)?;
            AffinePointChecked::enforce_equal(cs, &res, &a)?;
            
            // 5) a + (-a) + b
            let mut res = a.add(cs, &mut a_neg)?;
            res = res.add(cs, &mut b)?;
            AffinePointChecked::enforce_equal(cs, &res, &b)?;

            Ok(())
        }
    }

    #[test]
    fn test_affine_point_checked_for_bn256() {
        use self::bn256::Bn256;
        const LIMB_SIZE: usize = 72;

        let mut cs = TrivialAssembly::<
            Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext
        >::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let circuit_params = generate_optimal_circuit_params_for_bn256::<Bn256, _>(&mut cs, LIMB_SIZE, LIMB_SIZE);

        let circuit = TestCheckedAffineCurveCircuit { circuit_params };
        circuit.synthesize(&mut cs).expect("must work");
        cs.finalize();
        assert!(cs.is_satisfied()); 
    }
}

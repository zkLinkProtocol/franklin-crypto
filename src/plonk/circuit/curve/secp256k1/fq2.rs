use crate::bellman::pairing::ff::*;
use super::Fq;
use rand::{Rand, Rng};
use std::cmp::Ordering;

/// An element of Fq2, represented by c0 + c1 * u.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default, ::serde::Serialize, ::serde::Deserialize)]
pub struct Fq2 {
    pub c0: Fq,
    pub c1: Fq,
}

impl ::std::fmt::Display for Fq2 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq2({} + {} * u)", self.c0, self.c1)
    }
}

/// `Fq2` elements are ordered lexicographically.
impl Ord for Fq2 {
    #[inline(always)]
    fn cmp(&self, other: &Fq2) -> Ordering {
        match self.c1.cmp(&other.c1) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c0.cmp(&other.c0),
        }
    }
}

impl PartialOrd for Fq2 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq2) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Rand for Fq2 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq2 {
            c0: rng.gen(),
            c1: rng.gen(),
        }
    }
}

impl Field for Fq2 {
    fn zero() -> Self {
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        }
    }

    fn one() -> Self {
        Fq2 {
            c0: Fq::one(),
            c1: Fq::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    fn square(&mut self) {
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut c0c1 = self.c0;
        c0c1.add_assign(&self.c1);
        let mut c0 = self.c1;
        c0.negate();
        c0.add_assign(&self.c0);
        c0.mul_assign(&c0c1);
        c0.sub_assign(&ab);
        self.c1 = ab;
        self.c1.add_assign(&ab);
        c0.add_assign(&ab);
        self.c0 = c0;
    }

    fn double(&mut self) {
        self.c0.double();
        self.c1.double();
    }

    fn negate(&mut self) {
        self.c0.negate();
        self.c1.negate();
    }

    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
    }

    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
    }

    fn mul_assign(&mut self, other: &Self) {
        let mut aa = self.c0;
        aa.mul_assign(&other.c0);
        let mut bb = self.c1;
        bb.mul_assign(&other.c1);
        let mut o = other.c0;
        o.add_assign(&other.c1);
        self.c1.add_assign(&self.c0);
        self.c1.mul_assign(&o);
        self.c1.sub_assign(&aa);
        self.c1.sub_assign(&bb);
        self.c0 = aa;
        self.c0.sub_assign(&bb);
    }

    fn inverse(&self) -> Option<Self> {
        let mut t1 = self.c1;
        t1.square();
        let mut t0 = self.c0;
        t0.square();
        t0.add_assign(&t1);
        t0.inverse().map(|t| {
            let mut tmp = Fq2 {
                c0: self.c0,
                c1: self.c1,
            };
            tmp.c0.mul_assign(&t);
            tmp.c1.mul_assign(&t);
            tmp.c1.negate();

            tmp
        })
    }

    fn frobenius_map(&mut self, power: usize) {
        unimplemented!();
    }
}

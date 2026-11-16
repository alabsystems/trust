//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Review round 65: the keyed-collect licence erased a `BTreeMap`/`BTreeSet` collect
//! after checking only the key's `Ord`, but `from_iter` also SORTS (`PartialOrd::lt`)
//! and DEDUPS (`PartialEq::ne`), and a derived `Ord` may sit beside a hand-written
//! `PartialOrd`/`PartialEq`. A `requires` on that `eq`/`partial_cmp` was then never
//! charged, and the built program panicked. The hash family checked the method-less
//! `Eq` marker where hashbrown calls `PartialEq::eq`. Both now require the partial
//! traits to be total, so these collects keep their row and `certify` refuses them.
#![allow(dead_code)]
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialOrd, Ord, Eq)]
pub struct K(pub u8);

impl PartialEq for K {
    fn eq(&self, o: &Self) -> bool
        requires self.0 < 10
    {
        let t = [0u8; 10];
        let _probe = t[self.0 as usize];
        self.0 == o.0
    }
}

#[derive(Clone, Copy, PartialEq, Ord, Eq)]
pub struct L(pub u8);

impl PartialOrd for L {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering>
        requires self.0 < 10
    {
        let t = [0u8; 10];
        let _probe = t[self.0 as usize];
        Some(self.0.cmp(&o.0))
    }
}

pub fn keyed_map(s: &[(K, u8)]) -> BTreeMap<K, u8> {
    //~^ ERROR Trust strict verification failed for `keyed_collect_requires_total_partial_traits::keyed_map`
    s.iter().copied().collect()
}

pub fn keyed_set(s: &[L]) -> BTreeSet<L> {
    //~^ ERROR Trust strict verification failed for `keyed_collect_requires_total_partial_traits::keyed_set`
    s.iter().copied().collect()
}

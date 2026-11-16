//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `comparison_on_local_type_through_core_default.rs`: when the local
//! comparison core's default body calls can panic, every caller is refused. `bad_lt`
//! is the shape the flag-gated comparator sub-lane once certified (docs/KNOWN_HAZARDS.md,
//! `TRUST_PARTIALORD_SUBLANE`).
use std::cmp::Ordering;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Bad(pub u8);

impl PartialOrd for Bad {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bad {
    fn cmp(&self, other: &Self) -> Ordering { //~ ERROR verification
        let t = [0u8; 4];
        t[self.0 as usize].cmp(&other.0)
    }
}

pub fn bad_lt(a: Bad, b: Bad) -> bool { //~ ERROR verification
    a < b
}

pub fn bad_max(a: Bad, b: Bad) -> Bad { //~ ERROR verification
    a.max(b)
}

pub struct T(pub u8);

impl PartialEq for T {
    fn eq(&self, other: &Self) -> bool {
        self.0 + 1 == other.0
    }
}

pub fn bad_ne(a: &T, b: &T) -> bool { //~ ERROR verification
    a != b
}

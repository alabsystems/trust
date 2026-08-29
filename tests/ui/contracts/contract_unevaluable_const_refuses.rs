//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust D3 (associated-constant half), the refusal side. A constant that has
//! no single value at this boundary must REFUSE — never pick an instantiation,
//! never substitute a value.
//!
//! `T::LIMIT` on a generic function is the case that matters: there is no one
//! number it denotes, and silently choosing one would be precisely the false
//! assumption this work exists to remove. The clause fails closed: the
//! predicate becomes `Unsupported`, the precondition is NOT assumed (so it
//! cannot weaken anything downstream), and the build fails on unproved
//! coverage rather than compiling clean.
//!
//! This is the negative twin of `contract_assoc_const_resolves_exactly.rs`:
//! together they pin that resolution happens exactly where it is exact, and
//! nowhere else.

#![allow(dead_code)]

pub trait Limited {
    const LIMIT: u32;
}

// No single value here -> must refuse, and the body's assert must NOT be
// discharged by an invented bound.
#[trust::requires(id <= T::LIMIT)]
pub fn generic<T: Limited>(id: u32) -> u32 { //~ WARN `#[trust::requires]` on `generic` is not assumed
    assert!(id <= 10);
    id
}

pub struct Small;
impl Limited for Small {
    const LIMIT: u32 = 10;
}

fn main() { //~ WARN Trust Level 0 safety verification incomplete
    let _ = generic::<Small>(3);
}

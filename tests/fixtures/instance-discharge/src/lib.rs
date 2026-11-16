//! Instance-discharge accounting fixture (OD-1 phase 1, owner note 56 of
//! 2026-10-12). The smallest crate with one `proved` instance-discharge row:
//! a generic with one trait-method site, named at one concrete instance whose
//! resolved callee is panic-free.
//!
//! `f` carries the instance hypothesis (its `t.m()` is an open dispatch), and
//! `use_good` names `f::<Good>`, so the compiler publishes, in `use_good`,
//! `[instance-hypothesis:discharge] ... resolves to <Good as Tr>::m` with outcome
//! `proved`, and counts that row `skipped` in the function's summary.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

/// Carries the instance hypothesis: `t.m()` is an open generic dispatch.
pub fn f<T: Tr>(t: &T) -> u32 {
    t.m()
}

/// Names the instance `f::<Good>`: the discharge row is published here.
pub fn use_good() -> u32 {
    f(&Good)
}

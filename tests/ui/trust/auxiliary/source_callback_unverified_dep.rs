//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so NOTHING in this file is verified. Each item
//! panics on the input `7`, and each reaches a downstream `collect`/`extend`
//! only as code that runs INSIDE that call: a hand-written `Clone` behind
//! `cloned()`, a hand-written `Ord` or `Hash` behind a set operation, and an
//! iterator's own `next`. Used by `collect_extend_source_runs_unverified_code.rs`.

use std::cmp::Ordering;

/// A hand-written `Clone` that panics.
pub struct K(pub u32);

impl Clone for K {
    fn clone(&self) -> K {
        if self.0 == 7 {
            panic!("source_callback_unverified_dep::K::clone")
        }
        K(self.0)
    }
}

/// A hand-written `Ord` that panics (`PartialOrd` agrees with it).
#[derive(PartialEq, Eq)]
pub struct O(pub u32);

impl Ord for O {
    fn cmp(&self, other: &O) -> Ordering {
        if self.0 == 7 || other.0 == 7 {
            panic!("source_callback_unverified_dep::O::cmp")
        }
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for O {
    fn partial_cmp(&self, other: &O) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Arms `H::hash` (so a set can hold `H(7)` before its hash panics).
pub static ARMED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// A hand-written `Hash` that panics once `ARMED` (`Eq` is derived).
#[derive(PartialEq, Eq)]
pub struct H(pub u32);

impl std::hash::Hash for H {
    fn hash<S: std::hash::Hasher>(&self, state: &mut S) {
        if self.0 == 7 && ARMED.load(std::sync::atomic::Ordering::SeqCst) {
            panic!("source_callback_unverified_dep::H::hash")
        }
        self.0.hash(state)
    }
}

/// An iterator whose `next` panics on reaching `7`.
pub struct Countdown(pub u32);

impl Iterator for Countdown {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.0 == 7 {
            panic!("source_callback_unverified_dep::Countdown::next")
        }
        if self.0 == 0 {
            None
        } else {
            self.0 -= 1;
            Some(self.0)
        }
    }
}

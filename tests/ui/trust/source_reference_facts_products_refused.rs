//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Negative twin of `source_reference_facts_products_and_constants.rs`
//! (`docs/TCB.md`, "Source reference facts"; `docs/DECISION_QUEUE.md`,
//! 2026-11-07). Each function is its positive twin's shape with the pointee
//! changed to one the compiler must NOT claim, so each must stay non-proved:
//!
//! * `w_is_zero`: a local struct whose field is a `core` wrapper
//!   (`Wrapping<u8>`), refused by the library rule;
//! * `cell_pair_is_zero`: a tuple holding `Cell<u8>` (interior mutability);
//! * `m_is_zero`: a local struct holding `MaybeUninit<u8>`, read after
//!   `assume_init` (initializedness is the caller's unsafe obligation, never a
//!   validity fact of the reference);
//! * `use_n`: `f(&N(5))`, the promoted borrow of a NON-zero-sized struct. The
//!   value carrier is held to the stateless-ZST shape trust-mc's contract names,
//!   and a pointee-free value fact could not meet the callee's requirement on
//!   the pointee anyway.
//!
//! `M`'s own `score` fails on its unsafe read whatever the facts say, so `m`
//! pins only the end-to-end non-proved verdict; the library and `MaybeUninit`
//! refusals themselves are pinned by the bridge unit tests in
//! `crates/trust-ir-bridge/src/source_reference_sites/tests.rs`.

use std::cell::Cell;
use std::mem::MaybeUninit;
use std::num::Wrapping;

pub trait Score {
    fn score(&self) -> u8;
    fn is_zero(&self) -> bool {
        self.score() == 0
    }
}

pub struct W(pub Wrapping<u8>);

impl Score for W {
    fn score(&self) -> u8 {
        (self.0).0
    }
}

pub fn w_is_zero(w: &W) -> bool {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    w.is_zero()
}

impl Score for (u8, Cell<u8>) {
    fn score(&self) -> u8 {
        self.0 ^ self.1.get()
    }
}

pub fn cell_pair_is_zero(p: &(u8, Cell<u8>)) -> bool {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    p.is_zero()
}

pub struct M {
    pub a: MaybeUninit<u8>,
    pub b: u8,
}

impl Score for M {
    fn score(&self) -> u8 {
        //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
        //~| ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        // SAFETY: the caller's obligation; deliberately not established here.
        unsafe { self.a.assume_init() ^ self.b }
    }
}

pub fn m_is_zero(m: &M) -> bool {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~| ERROR Trust instance discharge not established
    //~| ERROR Trust strict verification failed
    m.is_zero()
}

pub trait Tr {
    fn m(&self) -> u32;
}

pub struct N(pub u8);

impl Tr for N {
    fn m(&self) -> u32 {
        self.0 as u32
    }
}

pub fn f<T: Tr>(t: &T) -> u32 {
    t.m()
}

pub fn use_n() -> u32 {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    f(&N(5))
}

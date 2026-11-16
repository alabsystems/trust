//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// (RE-PINNED 2026-09-14: in_a_closure's whole-function panic-freedom aggregate is
// runtime-checked — trust-mc's CHC/PDR transport "solved obligation … without a
// proof" — and ruling B reports it as an advisory WARN pair. That row is not what
// this file pins; the annotations above/below are.)
//! Trust: a loop clause in a body the verifier's contract inventory cannot
//! reach is a HARD ERROR, on BOTH surfaces.
//!
//! This closes a silent acceptance that predates the attribute transport and
//! is reachable from the native grammar alone. `lower_body_with_contract`
//! synthesises a HIR `FnContract` out of loop clauses ALONE, in ANY body, and
//! its own comment claimed "no authored clause can silently drop". But
//! `TrustContractBundle::def_may_have_contracts` admits only `Fn`, `AssocFn`
//! and `Closure`, so everything in between worked perfectly and the clause was
//! then discarded without ever being asked.
//!
//! MEASURED on the integrated stage2 before this check existed, with the
//! identical false invariant and bogus measure over a loop running `n` from 0
//! to 3 (`invariant n == 99 decreases 0`):
//!
//!     pub fn h() -> u32 { .. }                -> strict exit 1  (refused)
//!     pub const C: u32 = { .. };              -> strict exit 0, ZERO obligations
//!     pub static S: u32 = { .. };             -> strict exit 0, ZERO obligations
//!     fn g() -> u32 { const { .. } }          -> strict exit 0, ZERO obligations
//!     impl T { pub const A: u32 = { .. }; }   -> strict exit 0, ZERO obligations
//!     let f = || { .. };  (a CLOSURE)         -> strict exit 0, ZERO obligations
//!
//! The closure row is the one that matters most: `Closure` IS named in
//! `def_may_have_contracts`, so it looks supported. It is not -- the predicate
//! also requires `opt_hir_owner_nodes(..).is_some()` and a closure is not its
//! own HIR owner, so that arm is dead. `tests/ui/trust/native_loop_clauses.rs`
//! has carried a loop clause inside a closure since it was written, unnoticed
//! because that file runs with `-Z trust-verify=off`.
//!
//! A FALSE clause accepted with exit 0 is precisely the fake-proof class this
//! campaign exists to remove. The refusal is checked where the inventory is
//! built, so the check and the admission predicate cannot drift apart.

pub const C: u32 = {
    let mut n = 0u32;
    loop invariant n == 99 decreases 0 {
        //~^ ERROR a loop clause here would never be verified
        if n >= 3 {
            break;
        }
        n += 1;
    }
    n
};

pub static S: u32 = {
    let mut n = 0u32;
    while n < 3 invariant n == 99 {
        //~^ ERROR a loop clause here would never be verified
        n += 1;
    }
    n
};

pub struct T;

impl T {
    pub const A: u32 = {
        let mut n = 0u32;
        while n < 3 invariant n == 99 {
            //~^ ERROR a loop clause here would never be verified
            n += 1;
        }
        n
    };
}

// Inline consts are separate HIR body owners even when nested in an accepted
// free function. A surrounding function must not make this inner clause look
// inventoried.
pub fn in_an_inline_const() -> u32 {
    const {
        let mut n = 0u32;
        while n < 3 invariant n == 99 {
            //~^ ERROR a loop clause here would never be verified
            n += 1;
        }
        n
    }
}

// The same hole reached through the attribute transport rather than the native
// grammar: one check must cover both, or the surfaces drift.
pub const D: u32 = {
    let mut n = 0u32;
    #[cfg_attr(trust_verify, trust::loop_invariant(n == 99))]
    //~^ ERROR a loop clause here would never be verified
    while n < 3 {
        n += 1;
    }
    n
};

// A CLOSURE. Measured on the sealed toolchain: the identical false invariant
// gives strict exit 0 and produces only the body's `ArithmeticOverflow` row --
// zero loop obligations.
pub fn in_a_closure() -> u32 {
    let f = || {
        let mut n = 0u32;
        while n < 3 invariant n == 99 {
            //~^ ERROR a loop clause here would never be verified
            n += 1;
        }
        n
    };
    f()
}

fn main() {}

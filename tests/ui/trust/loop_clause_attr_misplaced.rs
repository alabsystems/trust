//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on
//! Trust: the stock-surviving loop-clause transport is refused everywhere it
//! is not on a `while` or `loop`, and each refusal names what the author
//! actually wrote.
//!
//! This is the fail-closed half of the transport, and it is the half that
//! matters. `#[trust::loop_invariant(..)]` is compiler-owned vocabulary
//! consumed before name resolution; if a misplaced one were merely IGNORED it
//! would be an annotation that looks like a specification, is accepted without
//! complaint, and contributes nothing — the exact bug class that made
//! `#[trust::invariant]` a refusal at every position and made a `decreases`
//! passthrough credit a function whose FALSE measure had been erased.
//!
//! `for` is refused with the SAME measured reason the native clause position
//! gives it, deliberately: a `for` is entered through the
//! `IntoIterator::into_iter` call, so its header is not reached by a
//! straight-line path and vcgen has no exact initiation model for it
//! (`e45.transition.entry-not-straight-line`). A transport that accepted a
//! position the native grammar refuses would widen the accepted surface behind
//! the native refusal's back.

pub fn on_a_for_loop(v: &[u8]) -> u32 {
    let mut acc = 0u32;
    #[cfg_attr(trust_verify, trust::loop_invariant(acc == 0))]
    //~^ ERROR `trust::loop_invariant` is a loop clause, and this is not a loop
    for _x in v {
        acc = 0;
    }
    acc
}

pub fn for_decreases(v: &[u8]) -> u32 {
    let mut acc = 0u32;
    #[cfg_attr(trust_verify, trust::decreases(acc))]
    //~^ ERROR `trust::decreases` is a loop clause, and this is not a loop
    for _x in v {
        acc = 0;
    }
    acc
}

pub fn on_a_block() -> u32 {
    #[cfg_attr(trust_verify, trust::loop_invariant(1 == 1))]
    //~^ ERROR `trust::loop_invariant` is a loop clause, and this is not a loop
    {
        7
    }
}

pub fn on_an_if(c: bool) -> u32 {
    #[cfg_attr(trust_verify, trust::loop_invariant(1 == 1))]
    //~^ ERROR `trust::loop_invariant` is a loop clause, and this is not a loop
    if c {
        1
    } else {
        2
    }
}

pub fn on_a_call() -> u32 {
    #[cfg_attr(trust_verify, trust::loop_invariant(1 == 1))]
    //~^ ERROR `trust::loop_invariant` is a loop clause, and this is not a loop
    on_a_block()
}

// An attribute outside a macro invocation is attached to the `MacCall`, not to
// whatever the macro eventually expands to. Carrying it through and guessing
// the association would be a program-point fiction; refuse it.
macro_rules! a_loop {
    () => {
        loop {
            break;
        }
    };
}

pub fn on_a_mac_call() {
    #[cfg_attr(trust_verify, trust::loop_invariant(1 == 1))]
    //~^ ERROR `trust::loop_invariant` is a loop clause, and this is not a loop
    a_loop!()
}

fn main() {}

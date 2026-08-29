//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on
//! Trust: a transported loop clause whose payload cannot be captured EXACTLY
//! is a hard error, never a dropped clause.
//!
//! Every arm here is a shape where the obvious implementation quietly does
//! nothing: an attribute with no payload, an attribute with a `= "…"` payload,
//! a non-parenthesized delimiter, an empty predicate, and two `decreases` on
//! one loop. Each must fail the build, because the alternative is an
//! annotation that reads as a specification and constrains nothing.
//!
//! The duplicate-`decreases` rule is the native parser's rule (E5, one
//! termination surface per loop), enforced again here so the two surfaces
//! cannot disagree about how many measures a loop may carry.

pub fn no_payload() {
    let mut n = 3u32;
    #[cfg_attr(trust_verify, trust::loop_invariant)]
    //~^ ERROR `trust::loop_invariant` needs a parenthesized predicate
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

pub fn eq_payload() {
    let mut n = 3u32;
    #[cfg_attr(trust_verify, trust::loop_invariant = "n <= 3")]
    //~^ ERROR `trust::loop_invariant` needs a parenthesized predicate
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

pub fn brace_payload() {
    let mut n = 3u32;
    #[cfg_attr(trust_verify, trust::loop_invariant { n <= 3 })]
    //~^ ERROR `trust::loop_invariant` takes its predicate in parentheses
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

pub fn empty_payload() {
    let mut n = 3u32;
    #[cfg_attr(trust_verify, trust::loop_invariant())]
    //~^ ERROR expected a predicate expression after the contract clause keyword
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

pub fn duplicate_decreases() {
    let mut n = 3u32;
    #[cfg_attr(trust_verify, trust::decreases(n))]
    #[cfg_attr(trust_verify, trust::decreases(n + 1))]
    //~^ ERROR duplicate `decreases` clause on this loop
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
}

fn main() {}

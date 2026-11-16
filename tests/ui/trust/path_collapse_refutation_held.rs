//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! S1 (2026-10-16): a refutation over a COLLAPSED path condition is withheld.
//!
//! `validate_carry` is aterm-parser `carry.rs:390`'s shape: two `matches!` over a
//! ten-variant state, an `||` chain and early returns give the shift's block more
//! than 64 root paths, its path list collapses to the single empty path, and the
//! solver refuted `mask >> params.len()` with two of the early returns firing in
//! the model. The row (and its hardened twin) is now `UNKNOWN` with the held
//! reason, and the build is STILL an error: a held row keeps no runtime-check
//! tolerance.
//!
//! Negative control: `shift_entry` has no path at all; `s = 32` is a real bug and
//! stays `FAILED`.
//!
//! MEASURED 2026-10-20 on the stage 1 of the SRH-1 land merge: `validate_carry`'s
//! `[shift:right]` row is `UNKNOWN` with `generic solver counterexample withheld:
//! path condition collapsed; the block's dominating guards are absent`, and
//! `shift_entry` is `[shift:right] FAILED`, in both revisions (`default`'s
//! counterexample: `_3 = false, s = 32, x = 0`).

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum State {
    Ground,
    Escape,
    CsiEntry,
    CsiParam,
    CsiIntermediate,
    CsiIgnore,
    DcsEntry,
    DcsParam,
    DcsIntermediate,
    DcsPassthrough,
}

pub struct Carry {
    pub state: State,
    pub params: Vec<u16>,
    pub subparam_mask: u32,
    pub current_param: u16,
    pub param_started: bool,
    pub last_was_colon: bool,
}

pub fn validate_carry(carry: &Carry) -> Result<(), u8> {
    //~^ NOTE generic solver counterexample withheld: path condition collapsed
    if carry.state == State::DcsPassthrough {
        return Err(0);
    }
    let header = matches!(
        carry.state,
        State::CsiEntry
            | State::CsiParam
            | State::CsiIntermediate
            | State::CsiIgnore
            | State::DcsEntry
            | State::DcsParam
            | State::DcsIntermediate
    );
    let parameters = matches!(
        carry.state,
        State::CsiParam | State::CsiIntermediate | State::DcsParam | State::DcsIntermediate
    );
    let has_params = !carry.params.is_empty()
        || carry.subparam_mask != 0
        || carry.current_param != 0
        || carry.param_started
        || carry.last_was_colon;
    if has_params && !parameters {
        return Err(1);
    }
    if carry.params.len() > 24 {
        return Err(2);
    }
    if carry.subparam_mask >> carry.params.len() != 0 {
        return Err(3);
    }
    if header { Ok(()) } else { Err(4) }
}

pub fn shift_entry(x: u32, s: u32) -> u32 {
    //~^ NOTE [shift:right] FAILED (ay-in-process); counterexample:
    x >> s
}

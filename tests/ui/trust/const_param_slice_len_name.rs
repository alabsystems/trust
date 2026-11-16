//@ revisions: default certify control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SLICE-LEN-NAME-1, the const-parameter half (2026-10-05): a const-generic
//! parameter's NAME must not decide that its symbol is a length.
//!
//! A const parameter reaches a formula as `__trust_constparam_{index}_{name}`
//! (`trust_types::const_param_symbol`), and the name used to be copied in as
//! written. Every consumer of the length symbol keys on the reserved suffix
//! `__slice_len` and reads it as `>= 0` (trust-vcgen's length facts, the interval
//! engine's floor), so `const n__slice_len: i8` minted
//! `__trust_constparam_0_n__slice_len` and `const _slice_len: i8` minted
//! `__trust_constparam_0__slice_len` (through the `_` that joins index and name):
//! both read as lengths, and `n - 1` on `i8` was proved. The first SLICE-LEN-NAME-1
//! fix keyed the floor on the double underscore and argued that a user name with
//! `__` is demoted before it reaches a formula; that holds for locals, not for
//! const parameters. The symbol now encodes any name that could spell `__`.
//!
//! This is worse than the local-name case: the false row is KERNEL-CERTIFIED and
//! the overflow check is ELIDED, so a consumer gets the wrapped value
//! (`const_param_slice_len_name_run.rs`).
//!
//! BEFORE (stage 1 of `dc15b882f6` at `scratchpad/stage1-w16`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05): `default`
//! and `certify` exit 0, and each function reports `1 proved` and `of which 1
//! kernel-certified by the clean CIC kernel`. `control` (the same bodies over plain
//! names) exits 1 with `[overflow:sub] FAILED (ay-in-process)` and the
//! counterexample `-128` for both functions.
//! A parameter named `x_slice_len` (one underscore) already failed, so the suffix
//! alone decided.
//!
//! AFTER: every revision reports what `control` reports.
#![allow(non_upper_case_globals)]

#[cfg(not(control))]
pub fn dec<const n__slice_len: i8>() -> i8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [overflow:sub] FAILED
    n__slice_len - 1
}

// The joining `_`: the name has no `__`, the symbol did.
#[cfg(not(control))]
pub fn dec_joined<const _slice_len: i8>() -> i8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [overflow:sub] FAILED
    _slice_len - 1
}

// The honest twins: refused with a counterexample before and after.
#[cfg(control)]
pub fn dec<const n: i8>() -> i8 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    //[control]~| NOTE [overflow:sub] FAILED
    n - 1
}

#[cfg(control)]
pub fn dec_joined<const slice_len: i8>() -> i8 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    //[control]~| NOTE [overflow:sub] FAILED
    slice_len - 1
}

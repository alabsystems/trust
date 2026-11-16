//@ revisions: default certify control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SLICE-LEN-NAME-1 (2026-10-05): the interval engine's non-negativity floor
//! belongs to the RESERVED length symbol `<place>__slice_len` that trust-vcgen
//! mints, never to a source name that merely ends in `_slice_len`.
//!
//! `IntervalBackend::bound_of` floored every variable whose name satisfied
//! `ends_with("_slice_len")` at 0, so a signed PARAMETER named `x_slice_len`
//! became `[0, 127]`. The interval lane then proved `x_slice_len - 1`, and the
//! compiler's held interval proof was committed over ay's refutation at
//! `x_slice_len = -128`: the default policy accepted the function with a
//! `runtime_checked` row while the same body over a parameter named `x` was
//! refused with a counterexample. The floor now needs the double underscore,
//! the spelling every other consumer of the length symbol already keys on; a
//! source local whose name contains `__` never reaches a formula under its own
//! name (`place_to_var_name` demotes it to `_<local>`).
//!
//! The binary was never wrong: no check was elided (`TRUST_ELIDE` elided 0), and
//! `dec(-128)` panics with 'attempt to subtract with overflow' with verification
//! on or off. The lie is the default lane ACCEPTING a refuted overflow because
//! of a parameter's name.
//!
//! BEFORE (stage 1 of `76a6ea45b2`, each revision's own flags plus
//! `--cfg <revision> --emit=metadata`, measured 2026-10-05): `default` exits 0
//! with warnings only; `dec` and `half` each carry `[overflow:sub]
//! runtime-checked: solver interval reported Proved without exact kernel/native
//! proof authority`. `certify` exits 1 with that same interval row (no proof
//! authority), so its `FAILED` notes are missing. `control` exits 1: the same
//! bodies over a parameter named `x` report `[overflow:sub] FAILED
//! (ay-in-process); counterexample: x = -128`.
//!
//! AFTER (predicted, not built): `dec` and `half` report what their `control`
//! twins report, `[overflow:sub] FAILED` with a counterexample, under both
//! policies.

#[cfg(not(control))]
pub fn dec(x_slice_len: i8) -> i8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [overflow:sub] FAILED
    x_slice_len - 1
}

// The floor's own purpose was a finite lower endpoint for `len / 2`: it made
// this underflow (at `x_slice_len = i64::MIN`) look impossible.
#[cfg(not(control))]
pub fn half(x_slice_len: i64) -> i64 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [overflow:sub] FAILED
    x_slice_len / 2 - (i64::MAX / 2) - 2
}

// The honest twins: refused with a counterexample before and after.
#[cfg(control)]
pub fn dec(x: i8) -> i8 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    //[control]~| NOTE [overflow:sub] FAILED
    x - 1
}

#[cfg(control)]
pub fn half(x: i64) -> i64 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    //[control]~| NOTE [overflow:sub] FAILED
    x / 2 - (i64::MAX / 2) - 2
}

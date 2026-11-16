//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D5-A (2026-09-24): a solver counterexample that CHOSE the return value of a
//! same-crate helper no summary models is withheld, never reported as a
//! refutation.
//!
//! Before (stage-1 `a8c853de6f`, both revisions), every caller below printed
//! `[shift:right] FAILED (ay-in-process); counterexample: _3 = true, … bit = 64`
//! (or the divzero twin `_3 = 0`). `_3` is the helper's result. It is a free
//! variable of the query, so the solver picked it — `nz` never returns 0, and
//! `g_or(64)` / `g_not(64)` are what they are regardless of the model.
//!
//! After: each caller row is `UNKNOWN` with the held-refutation reason naming
//! the helper, and the build is STILL an error in both revisions — a held row
//! keeps no runtime-check tolerance (`result_is_held_assert_refutation`). The
//! trailing NOTE pins are the mechanism: if the screen stops firing, the
//! `FAILED … counterexample` row comes back and the NOTE vanishes.
//!
//! D5-B (2026-09-24) MOVED three rows out of this file, deliberately: `guard`
//! (`bit < 64`), `cell_width_ok` (`cell > 0`) and `guard_bad` (`bit < 65`) now
//! carry a KERNEL-CHECKED body-inferred return lemma, so `shift_via_guard` and
//! `cell_index` PROVE (`inferred_return_helper_proves.rs`) and `shift_bad` is a
//! GROUNDED `FAILED … bit = 64` (`inferred_return_real_bug_refutes.rs`). Measured
//! before D5-B on stage-1 `4e9fe36bf`: all three held here, as the rows below.
//!
//! D5-B follow-up (2026-09-25, the kernel-checked rewriting lane in
//! trust-certify, `rewrite_eval.rs`): diamonds, short-circuits and temporaries now
//! certify too, measured on stage 1. `nz` gets its lemma, so `div_nz` PROVES and
//! moved to `inferred_return_helper_proves.rs`; `g_or` and `g_not` get theirs, so
//! `shift_or` / `shift_not` are no longer held — they are GROUNDED `FAILED … bit =
//! 64` refutations, and correct ones (`g_or(64)` is `true`, `g_not` inverts the
//! guard). The paragraph below is the pre-lane record.
//!
//! What stays held after D5-B, and why (each measured on the D5-B synthesizer +
//! the stage-1 certifier, `crates/trust-vcgen/tests/inferred_return_realmir.rs`):
//!
//! * `nz` (diamond), `g_or` (short-circuit), `g_not` (a temporary): the
//!   synthesizer proposes the right `E`, but the Clean kernel certifies none of
//!   their check rows (no certifier lane for the Bool-reified temp / implication
//!   pair the generator emits), so nothing is minted. `shift_or` / `shift_not` are
//!   REAL bugs (`g_or(64)` is `true`; `g_not` inverts the guard): held, never
//!   compiled.
//! * Outside the fragment: `ext_guard` (calls `leading_zeros`), `scale` (a
//!   checked `Mul`; its OWN `overflow:mul` row is a genuine refutation with no
//!   call in it and stays `FAILED`), `g_static` (reads a `static mut`).
//!
//! Controls that the screen does not over-hold live in
//! `call_dest_refutation_genuine_kept.rs`; the positive twin that proves through
//! a pinned helper is `call_dest_pinned_callees_prove.rs`.


pub fn ext_guard(bit: u32) -> bool {
    bit.leading_zeros() > 25
}

pub fn shift_ext(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_refutation_held::ext_guard`
    if !ext_guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn scale(k: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [overflow:mul] FAILED
    k * 8
}

pub fn shl_scale(x: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_refutation_held::scale`
    x << scale(8)
}

pub static mut LIM: u32 = 64;

pub fn g_static(b: u32) -> bool {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    b < unsafe { LIM }
}

pub fn shift_static(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_refutation_held::g_static`
    if !g_static(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn g_or(b: u32) -> bool {
    b < 64 || b == 64
}

pub fn shift_or(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample: _3 = true, _4 = false, _5 = 0, bit = 64, x = 0
    if !g_or(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn g_not(b: u32) -> bool {
    let t = b < 64;
    !t
}

pub fn shift_not(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample: _3 = true, _4 = false, _5 = 0, bit = 64, x = 0
    if !g_not(bit) {
        return None;
    }
    Some(x >> bit)
}

//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D5-B's ADVERSARIAL twin of `inferred_return_helper_proves.rs`: a kernel-
//! checked return lemma pins the helper's result to what the helper REALLY
//! returns, so a real bug behind a helper is refuted with a GROUNDED witness —
//! never proved, never held.
//!
//! * `shift_bad`: `guard_bad` is `bit < 65`, so `bit = 64` passes the guard and
//!   `x >> 64` overflows. BEFORE (stage-1 `4e9fe36bf`, both revisions): the D5-A
//!   held row `UNKNOWN … generic solver counterexample withheld: query depends on
//!   the unmodeled return of same-crate `…::guard_bad``. AFTER: `[shift:right]
//!   FAILED (ay-in-process); counterexample: _3 = true, … bit = 64` — `_3 =
//!   true` is now what `guard_bad(64)` returns, not a solver's choice.
//! * `ma::guard` / `mb::guard`: two helpers with the SAME name in different
//!   modules (different `DefId`s and def paths). `shift_mb` must be refuted on
//!   `mb::guard`'s own lemma (`bit < 65`), never proved on `ma::guard`'s
//!   (`bit < 64`); `shift_ma` proves (BEFORE: both held).
//! * `unguarded_after_guard`: `let _ = guard(bit); x >> bit` — a correct,
//!   SUMMARIZED helper whose result the shift never reads must not discharge it.
//!   FAILED before and after (the control that the lemma is about `_3` only).
//! * `extern_alias_sum`: a bodyless FOREIGN `boom_alias` and a LOCAL block-scoped
//!   `fn boom_alias() -> 1` under the same parent (the
//!   `foreign_import_key_alias_grandparent_merge_stays_closed.rs` shape). The local
//!   one is in the fragment and gets `_0 == 1`; the foreign one must stay havoc,
//!   so `a + b` must stay REFUTED (`a = u32::MAX`). Keyed by `DefId` at the mint
//!   and by the call's own rendered key (`…::{extern#0}::boom_alias` vs
//!   `…::boom_alias`) at the use, the lemma cannot reach the import. FAILED before
//!   and after.

pub fn guard(bit: u32) -> bool {
    bit < 64
}

pub fn guard_bad(bit: u32) -> bool {
    bit < 65
}

pub fn shift_bad(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    if !guard_bad(bit) {
        return None;
    }
    Some(x >> bit)
}

pub mod ma {
    pub fn guard(bit: u32) -> bool {
        bit < 64
    }
}

pub mod mb {
    pub fn guard(bit: u32) -> bool {
        bit < 65
    }
}

pub fn shift_ma(x: u64, bit: u32) -> Option<u64> {
    if !ma::guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn shift_mb(x: u64, bit: u32) -> Option<u64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    if !mb::guard(bit) {
        return None;
    }
    Some(x >> bit)
}

pub fn unguarded_after_guard(x: u64, bit: u32) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [shift:right] FAILED (ay-in-process); counterexample:
    let _ = guard(bit);
    x >> bit
}

pub fn extern_alias_sum(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE [overflow:add] FAILED
    let a = {
        unsafe extern "C" {
            safe fn boom_alias(x: u32) -> u32;
        }
        boom_alias(x)
    };
    let b = {
        fn boom_alias(_x: u32) -> u32 {
            1
        }
        boom_alias(x)
    };
    a + b
}

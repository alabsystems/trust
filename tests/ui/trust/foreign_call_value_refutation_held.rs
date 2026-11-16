//@ revisions: default hardened
//@ needs-trust-verify
//@ aux-build:foreign_call_value_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[hardened] compile-flags: -Ztrust-verify-profile=unix_hardened
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! S3 (2026-10-16): a refutation that rests on the value of an unmodelled
//! FOREIGN call, or on its `Option` result's `Some` payload, is withheld.
//!
//! * `at_cap` is aterm-parser `dispatch.rs:745`: `c.len() + 1` over a foreign
//!   `Cap::len`. The L0 row was already declined (`UnmodeledCalleeReturn`); its
//!   `HardenedBoundary` twin (revision `hardened`) has no obligation record and
//!   was refuted with `len = u64::MAX`. The twin is now read through its sibling
//!   and held.
//! * `split_fields` is `dispatch.rs:751-752`: `position` over a REASSIGNED slice
//!   has no length fact, and `rest[..k]` was refuted with `Some(1)` on an empty
//!   slice. Held on the payload (`rest[k + 1..]` also reads the loop-carried
//!   `rest` and is held by S2).
//!
//! Negative controls: `255 + (val() | 1)` overflows for EVERY value of the
//! foreign call, and the non-reseated `s[k + 1]` is pinned by the `position`
//! yield fact and really out of bounds at `k = len - 1`; both stay `FAILED`.
//! `cross_crate_value_refutes_real_overflow.rs` must still report `failed`.
//!
//! No `certify` revision: the aux crate is built with the default panic
//! strategy, as in `cross_crate_value_refutes_real_overflow.rs`.
//!
//! MEASURED 2026-10-20 on the stage 1 of the SRH-1 land merge. The `default`
//! revision has no `HardenedBoundary` twins, so `at_cap`'s only rows are the L0
//! row generation declines (`unsupported MIR \`UnmodeledCalleeReturn\``) and its
//! held assertion; the `hardened` revision (`-Ztrust-verify-profile=unix_hardened`,
//! `targo trust check`'s profile) has the twin, and it is `[hardened_panic_boundary]
//! UNKNOWN`, withheld on the foreign `_2`. `split_fields`'s two `[slice]` rows are
//! withheld on the `position` payload `_6@1.0` in both. `always_overflows` is
//! `[overflow:add] FAILED (… _0 = 256 …)` and `after_semicolon` `[slice] FAILED (…
//! k = 0, s__slice_len = 1)` in both (in `hardened`, `after_semicolon`'s twin over
//! the `position` payload `_2@1.0` is withheld beside its FAILED L0 row).

extern crate foreign_call_value_dep as dep;

pub fn at_cap(c: &dep::Cap) -> bool {
    //[default]~^ NOTE unsupported MIR `UnmodeledCalleeReturn`
    //[hardened]~^^ NOTE [hardened_panic_boundary] UNKNOWN (trust-full-verifier): generic solver counterexample withheld: query rests on the unmodelled return of a foreign call
    c.len() + 1 == 16
}

pub fn split_fields(mut rest: &[u8], out: &mut [usize; 4]) -> usize {
    //~^ NOTE generic solver counterexample withheld: query rests on the unmodelled return of a foreign call
    let mut n = 0usize;
    while n < 3 {
        match rest.iter().position(|&b| b == b';') {
            Some(k) => {
                out[n] = rest[..k].len();
                rest = &rest[k + 1..];
            }
            None => break,
        }
        n += 1;
    }
    n
}

pub fn always_overflows() -> u8 {
    //~^ NOTE [overflow:add] FAILED
    255u8 + (dep::val() | 1)
}

pub fn after_semicolon(s: &[u8]) -> u8 {
    //~^ NOTE [slice] FAILED
    if let Some(k) = s.iter().position(|&b| b == b';') { s[k + 1] } else { 0 }
}

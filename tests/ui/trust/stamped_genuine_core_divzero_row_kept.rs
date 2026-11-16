//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`, not `aux-build`: the aux's crate name is `core`, so only an explicit
// `--extern fakecore=<path>` puts it in the graph under another name.
//@ aux-crate: fakecore=stamped_genuine_core/core.rs
//@ revisions: default certify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A STAMPED GENUINE CORE KEEPS ITS ZERO-DIVISOR ROW (wave-21 integration,
//! 2026-10-09). DIVZERO-NAME-1 made `panic_calls::divzero_call` mint core's
//! `divisor != 0` row only under an authenticated sysroot root, so a user function
//! merely NAMED `div_euclid` is no longer refuted. An authenticated root refuses
//! every `__trust_crate@` stamp, and the extractor stamps the REAL core's paths
//! (`__trust_crate@<id>::core::num::<impl u32>::div_euclid`) when a second crate
//! named `core` is in the graph (here `auxiliary/stamped_genuine_core/core.rs`) and
//! under `-Zbuild-std`. STAMPED-CORE-MINT-1 (wave-19 review) ruled that a minting arm
//! reads past ONE well-formed leading stamp; `divzero_call` now does too
//! (`numeric_panic::after_one_identity_stamp`).
//!
//! Each function below is refused with or without the row: its `runtime_checked`
//! absent-callee row alone refuses it under both policies. The annotation pins the
//! ROW: "Level 0 safety verification incomplete … 2 obligation(s) were not proved"
//! counts the `[divzero]` / `[remzero] FAILED` row (counterexample a = 0, b = 0)
//! beside the absent-callee row; without the row only "strict verification failed …
//! 1 obligation(s)" is reported, as for a guarded twin.
//!
//! MEASURED 2026-10-10 (each revision's flags plus `--cfg <revision>`, the aux built
//! verify-off as `--crate-name core`): on the stage 1 of origin/main `32b6ef82d6`
//! (before wave 21, whose tail-only `divzero_call` minted the row for every
//! spelling) and on the stage 1 of `d58bad8195` (`integ/wave21`, with the fix) both
//! functions carry the row under both policies, beside one runtime-checked
//! absent-callee row. A guarded twin (`if b != 0 { a.div_euclid(b) } else { 0 }`) is
//! refused on that absent-callee row alone ("strict verification failed … 1
//! obligation(s)"). The fails-before of the fix is the unit test
//! `divzero_call_tests::a_stamped_genuine_core_keeps_its_divisor_row` (with the stamp
//! read removed, `__trust_crate@0123456789abcdef::core::num::<impl u32>::div_ceil`
//! answers `None`; measured 2026-10-10).

extern crate fakecore as _;

pub fn deuc_unguarded(a: u32, b: u32) -> u32 {
    //~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_divzero_row_kept::deuc_unguarded`: 2 obligation(s) were not proved
    a.div_euclid(b)
}

pub fn reuc_unguarded(a: u32, b: u32) -> u32 {
    //~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_divzero_row_kept::reuc_unguarded`: 2 obligation(s) were not proved
    a.rem_euclid(b)
}

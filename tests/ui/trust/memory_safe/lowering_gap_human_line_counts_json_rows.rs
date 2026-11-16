//~ NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":1}
//~| NOTE "proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":3}
//~| NOTE "proved":1,"failed":0,"unknown":2,"timed_out":0,"skipped":2,"runtime_checked":1,"cached":0,"total":4}
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! When the native typed-TrustIr lowering of a memory-safe body does not complete,
//! the rows the function PUBLISHES are not the VC-level results the human line
//! used to count: the `assumption:native-lowering` collapse drops every row it
//! cannot keep and adds one skipped row, and a refused collapse adds one
//! `native-verification-gap` row. Neither has a VC counterpart, so the human line
//! now counts the published rows. The JSON counts `skipped` inside `unknown`; the
//! human line lists it on its own, so each pair below agrees row for row. Lines 1-3
//! pin the JSON rows of `stop`, `vec_generic_alone` and `vec_alone` (compiletest reads
//! the span-less `TRUST_JSON:` transport note at line 1).
//!
//! Measured on stage-1 `f0e3202c07` (before this): `stop` printed "0 proved, 0
//! failed, 1 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)" while
//! its one JSON row is the skipped collapse row; `vec_alone` was ADMITTED on the
//! collapse, printing "1 proved, …, 1 skipped out of 2 obligation(s)" while its
//! JSON said `proved: 1, unknown: 2, skipped: 2, total: 3`. The same measurement on
//! stage-1 `b4bc7cdf9d` found `g(v, i) { if i >= v.len() { stop() } v[i] }` admitted
//! on the collapse with "1 proved … out of 1" and no warning; since `a84aa67936`
//! that `-> !` call lowers, so it no longer collapses.
//!
//! **The vehicle changed on 2026-09-28 (local line).** A `Vec` scalar index now lowers
//! (`vec_scalar_index_on_seq_receiver.rs`), so `vec_alone` no longer exercised a lowering
//! gap. The local line replaced it with `to_string_after_index` (a guarded slice index
//! beside `u32::to_string`, whose `_fmt_inner` member the bundle refused), which printed
//! `vec_alone`'s old human line and JSON row. Main reached the same point independently
//! with W4 (below) and pins that exact line and row on `vec_generic_alone`, whose stop is
//! a LOCAL generic member and holds on any std; `_fmt_inner` is an authentic std member
//! that main's `de66170e69` disposition may keep as a runtime-checked row. The merge
//! (2026-10-14) therefore keeps `vec_generic_alone` and drops `to_string_after_index` as
//! subsumed.
//!
//! `stop` stays refused (its `[termination]` row is not a demotable gap).
//! `vec_alone` was REFUSED from then on: its lowering stops at the
//! Assert-bearing `Vec::index` member, and its sysroot calls are edges the collapse
//! may not stand for (`memory_safe_assumption_uncharged_edges`) — the price of
//! closing `reject_lowering_gap_launders_uncharged_callee.rs`, which is the same
//! body plus a verify-off dependency call.
//!
//! `vec_alone` changed again with W4 VEC-AS-SLICE (branch `w4-vecslice`, re-pinned at
//! the W4 salvage rebase onto `296873da69`, 2026-09-29): a `Vec` scalar index is
//! charged at the CALLER's row and its member `Assert` forwarded, so the lowering no
//! longer stops at `Vec::index` and there is no gap row. Its rows are ordinary ones:
//! `v[1]` is refuted (vcgen has no length for the `vec![..]` literal) and memory-safe
//! demotes it to an `assumption:memory-safe-panic` row, and the literal's
//! `box_assume_init_into_vec_unsafe` is charged as an absent callee, runtime-checked.
//! It stays REFUSED, on that charge. Its pair USED TO differ by exactly the demoted
//! panic: the human line reported the VC's outcome (`1 failed`, demoted to a warning),
//! the JSON publishes the assumption row (`skipped`); main printed the same split for
//! any demoted memory-safe panic (`pub fn f(v: &[u32], i: usize) -> u32 { v[i] }` on
//! `0.10.0+g296873da6`: human `1 failed`, JSON `"failed":0 … "skipped":1`). Since
//! 2026-09-30 every body's line counts the published rows through the JSON's own tally
//! (`PublishedRowTally`), so the pair agrees: `1 proved, 0 failed, …, 1
//! runtime-checked, 2 skipped out of 4`, and `human_line_counts_published_rows.rs`
//! pins the plain `v[i]` case.
//! `vec_generic_alone` keeps the refused-collapse case `vec_alone` used to pin: its
//! lowering stops at the Assert-bearing bundled member `bump::<u32>` — a LOCAL generic
//! instance, so its `Overflow(Add)` Assert is neither exempt (the own-root run
//! verified the polymorphic body) nor eligible for the runtime-checked std-member
//! disposition (not a sysroot body) — and it calls sysroot functions (the `vec![..]`
//! literal), so it gets the `native-verification-gap` row. Its human line and JSON
//! rows are `vec_alone`'s old ones (measured on the W4 landing stage 1
//! `0.10.0+g452d2eef7`, on origin/main `fbb9fa383d`). `bump` itself is refuted
//! (`k + len` can overflow) and memory-safe demotes that to a warning.
//!
//! (W4 landing, 2026-09-29: the twin used to be `vec_count_alone`, whose lowering
//! stopped at `.count()`'s bundled `Iterator::count::{closure#0}`. That member's
//! `Overflow(Add)` Assert exists only in a std built with overflow checks, and since
//! main's `de66170e69` an authentic std member's refused Assert keeps the bundle as a
//! runtime-checked row, so `.count()` no longer reaches the gap — and its kept-bundle
//! rows pushed this file's JSON output past compiletest's 512 KiB capture limit,
//! truncating the diagnostics of the last function. A local generic member reaches
//! the gap on any std.)
fn bump<T>(w: &[T], k: u32) -> u32 {
    k + w.len() as u32
}

fn stop() -> ! {
    //~^ ERROR Trust memory-safe verification failed for `lowering_gap_human_line_counts_json_rows::stop`
    //~| NOTE 0 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 1 obligation(s)
    loop {}
}

pub fn vec_alone() -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `lowering_gap_human_line_counts_json_rows::vec_alone`
    //~| NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 4 obligation(s)
    let v = vec![1u32, 2, 3];
    v[1]
}

pub fn vec_generic_alone() -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `lowering_gap_human_line_counts_json_rows::vec_generic_alone`
    //~| NOTE 1 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 3 obligation(s)
    let v = vec![1u32, 2, 3];
    bump(&v, 1)
}

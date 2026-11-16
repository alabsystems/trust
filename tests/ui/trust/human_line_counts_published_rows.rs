//[memory_safe]~ NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":1}
//[default]~^ NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":3,"cached":0,"total":4}
//[held]~^^ NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
//@ revisions: default memory_safe held
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Copt-level=0
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[default] check-pass
//@[memory_safe] check-pass
//@[held] check-fail
//! The human summary line and the JSON transport count the SAME rows through ONE
//! tally (`PublishedRowTally`), so they cannot put a row in different categories.
//!
//! The line used to count the VC-level results and add every policy row minted after
//! them as "skipped", whatever its outcome; a row the policy REWROTE kept its
//! VC-level category; and the transport called a held assertion refutation
//! `runtime_checked` where the line and the strict failure accounting called it
//! unknown. MEASURED on stage-1 `f2e5ebbc0f`, `-Ztrust-verify-output=both`:
//!
//! * `default`: `std::env::args().count()` printed "0 proved, 0 failed, 0 unknown,
//!   0 timed out, 1 runtime-checked, 2 skipped out of 3 obligation(s)" while its JSON
//!   said `runtime_checked: 3, skipped: 0` — the two added rows are runtime-checked
//!   bundled std members, not skips (the same in every lane);
//! * `memory_safe`: `v[i]` printed "0 proved, 1 failed, … out of 1" for the row the
//!   JSON publishes as a skipped `assumption:memory-safe-panic` (`a / b` and
//!   `assert!(x != 7)` the same);
//! * `held` (an `assert!` over an unmodeled same-crate return, whose solver
//!   counterexample is held below proof authority): the line said "0 proved, 0
//!   failed, 1 unknown, 0 timed out, 1 runtime-checked out of 2" and the JSON
//!   `unknown: 0, runtime_checked: 2`; the held refutation now publishes as an
//!   `unknown` row, which is what the line and the strict verdict already said
//!   (`wrapping_binop_opt_level.rs` at `-O` showed the same, "2 unknown, 1
//!   runtime-checked" against `runtime_checked: 3`).
//!
//! Line 1-3 pin the JSON (compiletest reads the span-less `TRUST_JSON:` transport
//! notes there); the annotations on each function pin the human line.
//!
//! (2026-10-02) `args_count` allocates (`env::args` collects the argument
//! strings), so in this rlib it also carries the allocator premise row
//! (`contract:global-alloc-dealloc-panic-free`, DISCHARGED: the final link chooses
//! the global allocator). The line counts it "1 skipped"; the JSON counts it
//! `skipped: 1` and, by the JSON's documented legacy aggregate (`unknown` is every
//! row not proved, failed or runtime-checked, `TransportRowCounts`), `unknown: 1`.

#[cfg(default)]
pub fn args_count() -> usize {
    //[default]~^ NOTE 0 proved, 0 failed, 0 unknown, 0 timed out, 3 runtime-checked, 1 skipped out of 4 obligation(s)
    std::env::args().count()
}

#[cfg(memory_safe)]
pub fn index(v: &[u32], i: usize) -> u32 {
    //[memory_safe]~^ NOTE 0 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 1 obligation(s)
    v[i]
}

#[cfg(held)]
#[inline(never)]
fn opaque(x: u64) -> u64 {
    std::hint::black_box(x)
}

#[cfg(held)]
pub fn held_refutation() {
    //[held]~^ ERROR Trust Level 0 safety verification incomplete for `human_line_counts_published_rows::held_refutation`
    //[held]~| ERROR Trust strict verification failed for `human_line_counts_published_rows::held_refutation`
    //[held]~| NOTE 0 proved, 0 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    let a = opaque(3);
    assert!(a == 3, "opaque is the identity");
}

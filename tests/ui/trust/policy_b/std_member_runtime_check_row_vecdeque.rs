//@ needs-trust-verify
//@ revisions: strict default certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] check-fail
//@[default] check-fail
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The runtime-checked disposition beside a caller-value std panic (2026-09-29).
//!
//! `filter().count()` refuses core's `<usize as Sum>::sum::{closure#0}` (an
//! inherited `Overflow(Add)` Assert); `VecDeque::insert` panics on `index > len`.
//! Before: the refusal discarded the whole bundle, the lowering-failure tolerance
//! fired, and `q` was counted verified — `functions_verified` 2 of 2, no
//! `runtime_checked` row (MEASURED on stage-1 `f6773df328e`, m3 debug std and
//! release-like std); a verify-off `main` calling `q(Tag::A, &[1, 2, 3], &mut
//! VecDeque::new(), 5)` panicked "index out of bounds" inside `VecDeque::insert`
//! (exit 101). With m3's debug std even the `count()`-free twin was counted
//! verified (its `wrap_index` member's guarded Assert was tolerated the same way).
//!
//! After: the bundle is kept and `q` owes a `runtime_checked` row for each kept
//! member; it is not counted verified. `certify` refuses it.
//!
//! W4 VEC-INSERT (branch `w4-vecslice`, landed 2026-09-29): strict/default now
//! REFUSE `q` as well. The unguarded `d.insert(i, 1)` panics on `i > len` — a
//! panic on a CALLER-supplied value that docs/KNOWN_HAZARDS.md's std index/range
//! table listed as "ACCEPT — owned by branch `w4-vecslice`" — and the root call
//! site now gets the fail-closed `Call::insert::panic-freedom-unverified` row
//! (`unwrap_panic::is_caller_value_panicking_deque_method`, pinned by
//! `tests/ui/trust/vecdeque_caller_value_panic.rs`). The runtime-checked rows for
//! `count()`'s kept std members are published exactly as before (the RAW pins
//! below), and `q` is still never counted verified (`functions_verified` 1 of 2 —
//! the filter closure). Measured on the W4 landing stage 1 `0.10.0+g452d2eef7`
//! (origin/main `fbb9fa383d`): strict and default rc=1 ("2 obligation(s) were not
//! proved"; the `insert` row is `unknown`), certify rc=1 with its three lines.
use std::collections::VecDeque;

pub enum Tag {
    A,
    B,
}

pub fn q(t: Tag, v: &[u32; 3], d: &mut VecDeque<u32>, i: usize) {
    let k = v.iter().filter(|x| **x > 1).count();
    let n = match t {
        Tag::A => 1usize,
        Tag::B => 2usize,
    };
    if k == 7 || n == 7 {
        return;
    }
    d.insert(i, 1);
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): the member's internal Assert is now
// carried by the counted panic-freedom aggregate the soundness line mints for a call into
// a bundled body (docs/KNOWN_HAZARDS.md, "A may-panic MARKER is only as good as its
// CARRIER"), one `runtime_checked` row from `trust-full-verifier`, instead of the
// per-member `trust-std-member-runtime-check` row. Same grade, same invariant: the
// function is never counted verified, the non-certify lanes warn and `certify` refuses.
//[strict,default]~? RAW error: Trust Level 0 safety verification incomplete for `std_member_runtime_check_row_vecdeque::q`
//[strict,default]~? RAW error: Trust strict verification failed for `std_member_runtime_check_row_vecdeque::q`
//[strict,default]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"std_member_runtime_check_row_vecdeque","functions_analyzed":2,"functions_verified":1,
//[strict,default,certify]~? RAW "outcome":"runtime_checked","solver":"trust-full-verifier"

//[certify]~? RAW error: Trust Level 0 safety verification incomplete for `std_member_runtime_check_row_vecdeque::q`
//[certify]~? RAW error: Trust strict verification failed for `std_member_runtime_check_row_vecdeque::q`

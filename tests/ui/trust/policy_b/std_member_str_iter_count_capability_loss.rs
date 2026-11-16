//@ needs-trust-verify
//@ revisions: lines_count lines_filter_count split_count split_ws_count matches_count
//@ revisions: lines_last lines_for split_ws_for
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[lines_count] check-pass
//@[lines_filter_count] check-pass
//@[split_count] check-pass
//@[split_ws_count] check-pass
//@[matches_count] check-pass
//@[lines_last] check-pass
//@[lines_for] check-pass
//@[split_ws_for] check-pass
//! A CAPABILITY LOSS of the bundled std-member fix, pinned so that it is seen
//! (2026-09-29, Track R review finding 1; docs/KNOWN_HAZARDS.md, the CLOSED
//! 2026-09-29 entry, and docs/DECISION_QUEUE.md, "Rulings recorded 2026-09-29").
//!
//! `.count()` on core's borrowed `str` iterators — `lines()`, `split(char)`,
//! `split_whitespace()`, `matches(char)` — bundles core's `Iterator::count`
//! closure, whose inherited `Overflow(Add)` Assert the exact Div/Rem/BoundsCheck
//! lane refuses. Before the fix that refusal DISCARDED the whole bundle and the
//! lowering-failure tolerance accepted the function (exit 0, not counted
//! verified, one `native-verification-gap` row). The bundle is now KEPT, the
//! member owes a `runtime_checked` row, and the kept bundle also carries the
//! drop-glue row for the consumed iterator — "drop glue for
//! `core::str::iter::Lines` has unproven panic-freedom" — which is fail-closed on
//! the success path, so each `*_count` revision is refused under strict. Those
//! iterators own no field with drop glue (borrowed `&str`s, indices, `bool`s,
//! char searchers and zero-sized closures, library/core/src/str/{iter,pattern,
//! mod}.rs); the row is over glue that does nothing. Crediting it is WORK, and it
//! must be decided on rustc's own `needs_drop` of the monomorphic type, never on
//! the trust-ir `Ty` spelling (docs/DECISION_QUEUE.md, "DO NOT credit drop glue
//! whose type needs no drop").
//!
//! The `count()`-free twins are the controls and stay check-pass: `.last()` and a
//! `for` loop consume the same iterators and build (on origin/main too). When
//! the drop-glue credit lands, the `*_count` revisions are expected to flip to
//! check-pass; flip them then, with the measurement.
//!
//! FLIPPED 2026-10-15 (the merge of 2026-10-14). Measured on the merged stage 1 under
//! this header's flags: all five `*_count` revisions build. The `count` call is now
//! credited as total by the drive-only consumer lane
//! (`collect_verified_callable_consumer_total_calls`: `count` over a total std
//! receiver whose `Self` and items need no drop by rustc's own `needs_drop` of the
//! monomorphic type, the rule this header asks for), which the zero-obligation gate
//! reads as well (VERIFIED-CALLABLE-ZERO-ROW-PARITY, DECISION_QUEUE D103); the bundle,
//! and with it the drop-glue row, is no longer what decides the call.

#[cfg(lines_count)]
pub fn p(s: &str) -> usize {
    s.lines().count()
}

#[cfg(lines_filter_count)]
pub fn p(s: &str) -> usize {
    s.lines().filter(|l| !l.is_empty()).count()
}

#[cfg(split_count)]
pub fn p(s: &str) -> usize {
    s.split(',').count()
}

#[cfg(split_ws_count)]
pub fn p(s: &str) -> usize {
    s.split_whitespace().count()
}

#[cfg(matches_count)]
pub fn p(s: &str) -> usize {
    s.matches('a').count()
}

#[cfg(lines_last)]
pub fn p(s: &str) -> bool {
    s.lines().last().is_some()
}

#[cfg(lines_for)]
pub fn p(s: &str) -> u32 {
    let mut n = 0u32;
    for _l in s.lines() {
        n = n.wrapping_add(1);
    }
    n
}

#[cfg(split_ws_for)]
pub fn p(s: &str) -> u32 {
    let mut n = 0u32;
    for _w in s.split_whitespace() {
        n = n.wrapping_add(1);
    }
    n
}


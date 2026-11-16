//@ revisions: rpass1 rpass2
//@ needs-trust-verify
//@ compile-flags: -Zquery-dep-graph -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-no-r1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ ignore-backends: gcc

// The first session materializes `ping`'s non-disk-cached Trust MIR snapshot. In the second
// session `ping` is unchanged, while `pong` changes and invalidates the recursive verification
// closure. Re-optimizing `ping` must materialize its green snapshot before stealing the source
// MIR: an ensure-only query can mark the dep-node green without caching its value, after which
// `pong`'s traversal back through `ping` would try to borrow the stolen body and ICE.

#![feature(rustc_attrs)]

#[rustc_clean(cfg = "rpass2", except = "optimized_mir")]
#[inline(never)]
// Trust: `ping` and rpass1-`pong` carry incomplete-WARN annotations again, for a
// different reason than before. Their branch-guarded `n - 1` (`n != 0` dominates it)
// still PROVES, kernel-certified, since the trust-wp termination-callgraph holes
// were closed. But since c927d6fd7f (2026-09-25, owner-delegated ruling on
// KNOWN_HAZARDS "mutual recursion verifies and can abort on stack overflow") every
// call into a recursion SCC carries a `[termination]` row. Neither function has a
// `decreases` measure, so that row stays UNKNOWN: the documented over-refusal for
// unmeasured terminating mutual recursion. Re-measured 2026-09-29 at 71c7af9782,
// stage 2: rpass1 ping/pong each have 3 obligations with 1 unknown; rpass2 pong
// has 4 with 2 unknown, because its `1 + ...` adds a row. The verdicts are incidental
// vehicle diagnostics anyway. This test's payload is the `rustc_clean` assertion
// plus "rpass2 does not ICE on the green-ensure snapshot", which is unchanged.
//[rpass1,rpass2]~v WARN Trust Level 0 safety verification incomplete for `trust_mir_snapshot_after_green_ensure::ping`
fn ping(n: u32) -> u32 {
    if n == 0 { 0 } else { pong(n - 1) }
}

#[cfg(rpass1)]
#[inline(never)]
//[rpass1]~v WARN Trust Level 0 safety verification incomplete for `trust_mir_snapshot_after_green_ensure::pong`
fn pong(n: u32) -> u32 {
    if n == 0 { 0 } else { ping(n - 1) }
}

#[cfg(rpass2)]
#[inline(never)]
//[rpass2]~v WARN Trust Level 0 safety verification incomplete for `trust_mir_snapshot_after_green_ensure::pong`
fn pong(n: u32) -> u32 {
    // Deliberately change only this SCC member so `ping`'s snapshot is green while
    // its verification closure is red and must be rebuilt.
    if n == 0 { 0 } else { 1 + ping(n - 1) }
}

//[rpass1,rpass2]~v WARN Trust Level 0 safety verification incomplete for `trust_mir_snapshot_after_green_ensure::main`
fn main() {
    std::hint::black_box(ping(4));
}

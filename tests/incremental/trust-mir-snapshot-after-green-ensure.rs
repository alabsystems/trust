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
// Trust: `ping` and rpass1-`pong` carry NO incomplete-WARN annotations. Their sole
// obligation is the branch-guarded `n - 1` (`n != 0` dominates it), which PROVES —
// kernel-certified — since the trust-wp termination-callgraph holes were closed
// (the five ledgered false-accepts fix): a mutual-recursion SCC member's local
// arithmetic no longer stays conservatively unproved. The original annotations
// predate that and were stale, not wrong-when-written. The verdicts are incidental
// vehicle diagnostics anyway — this test's payload is the `rustc_clean` assertion
// plus "rpass2 does not ICE on the green-ensure snapshot", which is unchanged.
fn ping(n: u32) -> u32 {
    if n == 0 { 0 } else { pong(n - 1) }
}

#[cfg(rpass1)]
#[inline(never)]
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

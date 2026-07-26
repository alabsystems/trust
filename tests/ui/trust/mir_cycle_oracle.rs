//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-no-r1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ build-pass
//! Runtime query-cycle coverage for the compact Trust MIR SCC oracle.
//! A direct self edge is intentionally not a mutual SCC: the live-query guard
//! handles it without cloning a second MIR body or re-entering `optimized_mir`.

#[inline(never)]
fn direct_countdown(n: u32) -> u32 {
    // The `n - 1` underflow obligation under the `n != 0` else-guard now
    // proves AND kernel-certifies (the disequality order-split recognizer
    // closes `0 <= n ∧ n != 0 ∧ n - 1 < 0`), so the former
    // verification-incomplete warning no longer fires for this fn.
    if n == 0 { 0 } else { direct_countdown(n - 1) }
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `mir_cycle_oracle::main`
    std::hint::black_box(direct_countdown(4));
}

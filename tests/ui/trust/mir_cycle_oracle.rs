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
    //~^ NOTE Trust verification: 3 proved
    // The `n - 1` underflow obligation under the `n != 0` else-guard proves
    // AND kernel-certifies (the disequality order-split recognizer closes
    // `0 <= n ∧ n != 0 ∧ n - 1 < 0`), and the self-recursion's termination
    // row (`NonTermination { context: "recursion", measure: "n" }`) proves on
    // the native CHC/PDR lane. Re-pinned 2026-09-14 (trust-mc `23dd58a6c7`):
    // the third row, the aggregate panic-freedom obligation over the body,
    // proves too — trust-mc models the direct self-call by the inductive
    // hypothesis instead of an unconditional error rule — so the former
    // WARN "Level 0 safety verification incomplete" (the aggregate read
    // runtime-checked) no longer fires. WARN is not in
    // dont-require-annotations: if it returns, this test fails loudly.
    if n == 0 { 0 } else { direct_countdown(n - 1) }
}

fn main() {
    // Re-pinned 2026-08-14 (origin/main merge): the former WARN "Level 0
    // safety verification incomplete for `mir_cycle_oracle::main`" no longer
    // fires, and its absence is the verified-good state, not a swallowed
    // verdict. Under the merged lowering (upstream's ir-bridge CFG rework +
    // its trust-mc pin) the caller's native bundle carries BOTH bodies — no
    // absent-callee row, no whole-function panic-freedom carrier — vcgen
    // mints no VC for this body, and the only native row is the excluded
    // `trust_mc_default_function` admission sentinel: zero countable
    // obligations. With `direct_countdown` fully statically proved above,
    // strict fail-closed verification also accepts `main` (zero-obligation +
    // vacuously-clean native run), so an advisory WARN here would be a false
    // alarm. WARN is not in dont-require-annotations, so if a caller-side
    // WARN ever returns on this line the test fails loudly again.
    std::hint::black_box(direct_countdown(4));
}

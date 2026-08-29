//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t_c3
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ check-pass
//
// THE R1 PER-MONO LANE RUNS. This is the first fixture in the tree that reaches it:
// its blessed stderr carries `init: generic-mono covered=1 caller-closure=3`, where
// every other fixture in the suite reports `covered=0 caller-closure=0`.
//
// It exists because the opposite was asserted in `trust_verify.rs` as a STRUCTURAL
// fact — "`generic_mono_covered` cannot be populated by ANY program" — and shipped
// as the licence for keying `r1_generic_mono_caller_closure` however one liked. The
// nine lines below refute it, on the binary that claim was measured on.
//
// WHY THIS SHAPE and not the probes that read `covered=0`: the harvest keys its
// one-entry summary DB with the callee's IDENTITY args (`safe_def_path_str`), while
// `func_operand_name` keys the CALL with the CONCRETE args, and the callsite lookup
// is an exact `summaries.get`. A MONOMORPHIC caller therefore misses
// (`callee=t_g1::W::inner::<4>` against the key `t_g1::W::inner`). `mid` here is
// GENERIC, so its un-monomorphized MIR spells the callee `t_c3::W::<N>::inner` —
// byte-identical to the summary key — the precondition VC is minted, the mono is
// covered, and the flip is ADMITTED. The `if i < 4` guard is what makes the caller
// establish P; delete it and the mono is rejected.
//
// WHAT MOVES IT: the caller-closure count was the pre-patch RAW-keyed set
// {`W::<N>::inner`, `mid`, `h`, `main`}. Keying it through the seam and dropping the
// graph SEEDS makes it {`t_c3::mid`, `t_c3::h`, `t_c3::main`}.
//
// MEASURED 2026-08-22 on the first build carrying that hunk (stage2 `ec4783d80`):
// `caller-closure=3`, and the count is the ONLY line of this file's stderr that
// moved. That is the end-to-end measurement the hunk originally shipped without —
// it is now taken, and the 4 it replaced is recorded here so a regression back to
// the raw key is visible as a re-bless rather than as silence.
//
// Also pinned, and a separate open soundness item: `mono [N/#0]` — the "mono" this
// lane certifies is still a PARAM args vector, accepted because `Instance::try_resolve`
// succeeds on it.
struct W<const N: usize>;
impl<const N: usize> W<N> {
    fn inner(a: &[u8; 4], i: usize) -> u8 {
        a[i]
    }
}
fn mid<const N: usize>(a: &[u8; 4], i: usize) -> u8 {
    if i < 4 { W::<N>::inner(a, i) } else { 0 }
}
fn h() -> u8 {
    let a = [1u8, 2, 3, 4];
    mid::<4>(&a, 2)
}
fn main() {
    let _ = h();
}

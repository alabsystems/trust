//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ check-pass
//
// THE FAIL-OPEN, WITH A NON-EMPTY CLOSURE — present tense, not "once the lane goes
// live". `caller_closure_key_space_collision.rs` pins the two key spaces overlapping
// while the caller closure is EMPTY; this file is the same collision on a program
// that populates it (`init: generic-mono covered=1 caller-closure=3`).
//
// Crate `t` contains `mod t`. The transitive-caller walk reaches `t::t::mid`, and
// the pre-fix producer rendered it RAW, i.e. WITHOUT the local crate prefix:
//
//   RAW(t::t::mid)  == "t::mid"   <- `t::mid: GENERIC per-mono harvest` in the stderr
//   SEAM(t::t::mid) == "t::t::mid" <- `apply_r1_flips: NO flip for def_path='t::t::mid'`
//   SEAM(t::mid)    == "t::mid"   <- `apply_r1_flips: NO flip for def_path='t::mid'`
//
// The crate-root `mid` is NOT in the closure — nothing calls it from the covered
// generic's caller graph; it is reached only by `g`. Yet its SEAM key is byte-identical
// to the RAW key of the in-closure `t::t::mid`, so `r1_generic_mono_coverage("t::mid")`
// answers `is_caller_of_covered = true` for it, and that boolean is the `caller_ok`
// disjunct that suppresses the full-lane generic-lowering abort. A wrong-function
// suppression, not a missing one.
//
// WHAT IS MEASURED HERE and what is not: the two byte-identical strings and the
// non-empty closure are in the blessed stderr below. A suppressed verdict is NOT —
// the abort site's other conjuncts (`native_lowering_failure_is_generic_monomorphization_only`,
// all rows statically proved) are not met by this program, so no `abort SUPPRESSED`
// line appears. The guard is over the keys, which is where the defect is.
//
// After the fix (seam keying + seed exclusion) the closure is
// {`t::t::mid`, `t::h`, `t::main`}, "t::mid" is no longer in it, and the count drops
// to 3. MEASURED 2026-08-22 on stage2 `ec4783d80`, the first build carrying the
// hunk: `caller-closure=3`, and that count is the only line of the blessed stderr
// that moved — the fail-open key collision this file pins is closed.
struct V<const N: usize>;
impl<const N: usize> V<N> {
    fn inner(a: &[u8; 4], i: usize) -> u8 {
        a[i]
    }
}
mod t {
    pub(crate) fn mid<const N: usize>(a: &[u8; 4], i: usize) -> u8 {
        if i < 4 { crate::V::<N>::inner(a, i) } else { 0 }
    }
}
fn mid<const N: usize>(a: &[u8; N]) -> usize {
    a.len()
}
fn h() -> u8 {
    let a = [1u8, 2, 3, 4];
    t::mid::<4>(&a, 2)
}
fn g() -> usize {
    let b = [7u8; 3];
    mid::<3>(&b)
}
fn main() {
    let _ = h();
    let _ = g();
}

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-fail
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

// R1-MONO-SUPPRESSION-1: sealed row harvesting remains enabled, but its
// root-only evidence cannot suppress a failed/discarded native bundle.
// The former generic-coverage registry and transitive caller census are gone.
// This generic caller still exposes a non-concrete argument vector. Its
// harvest must refuse that vector; native lowering failures stay strict
// errors. No former wrong-function acceptance was measured by this case.
struct V<const N: usize>;
impl<const N: usize> V<N> {
    fn inner(a: &[u8; 4], i: usize) -> u8 {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed for
        a[i]
    }
}
mod t {
    pub(crate) fn mid<const N: usize>(a: &[u8; 4], i: usize) -> u8 { //~ ERROR Trust strict verification failed for
        if i < 4 { crate::V::<N>::inner(a, i) } else { 0 }
    }
}
fn mid<const N: usize>(a: &[u8; N]) -> usize {
    a.len()
}
fn h() -> u8 { //~ ERROR Trust full verification failed for
    let a = [1u8, 2, 3, 4];
    t::mid::<4>(&a, 2)
}
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
// R43-ZERO-ROW-PARITY (2026-10-13): `g` is accepted (ZERO-ROW-GATE refused it):
// its call `mid::<3>` is discharged by the R43 parametric premises.
fn g() -> usize {
    let b = [7u8; 3];
    mid::<3>(&b)
}
fn main() { //~ ERROR Trust full verification failed for
    let _ = h();
    let _ = g();
}

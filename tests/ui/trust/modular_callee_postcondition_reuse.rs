//@ ignore-test (capability alarm: sealed production postcondition authority is not implemented)
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-level=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ build-pass
//! Capability alarm for modular callee-postcondition reuse.
//!
//! This test is intentionally ignored while the lane is dark. It becomes a real
//! `build-pass` regression only after rustc transports replayed proof authority
//! bound to the exact callee identity, contract digest, and instantiated
//! obligation. Until then `FunctionSummary::has_reusable_postcondition_evidence`
//! must remain false, and this fixture must remain recorded rather than deleted.
//!
//! The caller cannot derive `i < 8` from the callee body: `index_of` is not
//! inlined into `read`, and the existing whole-crate return-bound recognizers do
//! not summarize `%`. The bounds check therefore closes only when the proved
//! `ensures` clause is soundly reusable at this call site.

pub fn index_of(x: usize) -> usize
    ensures result < 8
{
    x % 8
}

pub fn read(a: &[u8; 8], x: usize) -> u8 {
    let i = index_of(x);
    a[i]
}

fn main() {
    let a = [7_u8; 8];
    let _ = read(&a, 100);
}

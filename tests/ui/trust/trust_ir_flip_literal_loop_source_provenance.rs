//@ build-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0
//@ rustc-env:RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info
//@ normalize-stderr: "DefId\([^)]*\)" -> "DEF_ID"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "LINEAGE"
//! A structural literal invariant has no free source roots. Its exact binding
//! map is therefore empty, not absent, and the authenticated loop identity is
//! still sufficient for the TrustIR-to-MIR flip.

#[inline(never)]
pub fn countdown_literal(limit: u32) -> u32 {
    let mut n = limit;
    while n > 0 invariant true {
        n -= 1;
    }
    n
}

fn main() {
    assert_eq!(countdown_literal(3), 0);
}

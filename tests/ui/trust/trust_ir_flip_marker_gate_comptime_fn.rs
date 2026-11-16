//@ build-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=0
//@ compile-flags: -Zmir-opt-level=1
//@ rustc-env:RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info
//@ normalize-stderr: "\[[0-9a-f]{4}\]" -> "[HASH]"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "LINEAGE"
//! Trust (F4, review round 4, 2026-09-30): the marker gate's CTFE carve-out must key on the
//! seam that installs the body, not on its kind. `try_flip_ctfe` installs `mir_for_ctfe` for
//! every body whose `hir_body_const_context` is `Const { .. }` or `Static(_)`, and a
//! `#[rustc_comptime]` fn is `Const { .. }` while its `BodyKind` is `Fn`. `mir_for_ctfe` is
//! never touched by `RemoveStorageMarkers`, the const-eval interpreter runs it with its
//! markers, and the encoder records it for other crates, so the `-O0` exemption (no lifetime
//! intrinsics, the pass runs on `optimized_mir`) says nothing about it.
//!
//! `copy_ct` is `DerivedAgreed` with `markers_exact == false` (built marks the user local `x`,
//! the shim marks operand temps only); `D` is exact (a call with a constant argument, no
//! markers on either side). In this `-Zmir-opt-level=1` session, where the exemption holds for
//! codegen-seam bodies, `D` flips on the CTFE seam and `copy_ct` must NOT.
//! Measured on the pre-fix driver (round 3, keyed on `BodyKind::ConstInit`): `copy_ct` flipped
//! on the CTFE seam too. The `CTFE compiled from trust-ir` event is the witness.

#![crate_type = "lib"]
#![feature(rustc_attrs)]
#![allow(internal_features)]

#[rustc_comptime]
fn copy_ct(i: usize) -> usize {
    let x = i;
    x
}

pub const D: usize = copy_ct(5);

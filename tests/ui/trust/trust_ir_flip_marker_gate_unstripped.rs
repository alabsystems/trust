//@ build-pass
//@ revisions: stripped unstripped pass_off bisect
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=0
//@[stripped] compile-flags: -Zmir-opt-level=1
//@[unstripped] compile-flags: -Zmir-opt-level=0
//@[pass_off] compile-flags: -Zmir-opt-level=1 -Zmir-enable-passes=-RemoveStorageMarkers
//@[bisect] compile-flags: -Zmir-opt-level=1 -Zmir-opt-bisect-limit=0
//@ rustc-env:RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info
//@ normalize-stderr: "\[[0-9a-f]{4}\]" -> "[HASH]"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "LINEAGE"
//! Trust (F4, 2026-09-29; reworked after the review): the flip's per-body marker gate lets a
//! body whose marker sequence was NOT proven exact flip only where its markers cannot reach any
//! codegen or interpreter. `-Copt-level=0` alone used to decide that. The markers survive into
//! `optimized_mir` unless `RemoveStorageMarkers` runs, and `optimized_mir` is what metadata
//! encodes for other crates; the CTFE seam installs `mir_for_ctfe`, which that pass never
//! touches and the const-eval interpreter runs with its markers.
//!
//! `copy_through_local` (a plain fn) and the const `C` are `DerivedAgreed` with
//! `markers_exact == false` (built marks the user local, the shim marks operand temps only). So:
//!   * `stripped` (`-Zmir-opt-level=1`, the `-O0` default): the pass runs — the fn flips; the
//!     const does NOT (a `ConstInit` body never takes the exemption);
//!   * `unstripped` (`-Zmir-opt-level=0`), `pass_off` (the pass switched off by name) and
//!     `bisect` (`-Zmir-opt-bisect-limit`, which can skip the pass on any body and is not
//!     predicted here): nothing flips.
//! Measured on the pre-fix driver: the fn flipped in all four revisions (in `bisect` with its
//! markers left in place: `BISECT: NOT running pass (7) RemoveStorageMarkers`), and `C` flipped
//! on the CTFE seam. The `compiled from trust-ir` event is the witness.

#![crate_type = "lib"]

pub fn copy_through_local(i: usize) -> usize {
    let x = i;
    x
}

const fn id(v: usize) -> usize {
    v
}

pub const C: usize = {
    let x = id(5);
    let y = x;
    y
};

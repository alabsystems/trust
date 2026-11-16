//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! Trust (trust-ir v39, `FatPtrKind::ContainerVtable`): an enum that transitively holds an
//! `Arc<dyn Any + Send + Sync>` must register with a RESOLVABLE layout.
//!
//! THE DEFECT. `Arc<dyn Any>` is `NonNull<ArcInner<dyn Any>>`, which is
//! `*const ArcInner<dyn Any>`: a pointer whose pointee merely CONTAINS a `dyn` in tail
//! position. rustc lays it out as a 16-byte (data, vtable) pair. `map_ty`'s raw-pointer
//! catch-all asked `container_pointee_ty` for the spelling and got `None` for a `Vtable` tail
//! ("this producer carries no vtable component"), so the field was declared `Ty::Unit` under
//! the `Ty(raw-ptr fat/array pointee)` tag — a struct whose recorded size (16) no field sum
//! could reach. The v31 enum-layout validator then correctly refused EVERY enum holding one.
//! Measured 2026-09-08 on the nn-autodiff seal (trust-f2887e0d): `ConstTypeMismatch { .. layout
//! UNRESOLVABLE for type struct.11: struct.9 has no size layout metadata }` on each such enum;
//! the nn log named an `Option<Arc<dyn ..>>` niche case as well (what this file can and cannot
//! say about that shape is below).
//!
//! THE FIX. trust-ir v39 adds `FatPtrKind::ContainerVtable` — the `dyn`-tail sibling of v38's
//! `ContainerLen`: two pointer words laid out exactly like `TraitObject`, under a kind that
//! carries no trait id because nothing dispatches through a pointer to the CONTAINER header.
//! `container_pointee_ty` now spells a `Vtable` tail `Ty::FatPtr(ContainerVtable)`, and
//! `fat_shape_of_container_pointee` (derived from it) classifies it `Fat` in lockstep. Where
//! kinds are classified by what their metadata MEANS, `ContainerVtable` follows `TraitObject`
//! (an opaque vtable word), never the length kinds.
//!
//! WHAT THIS PIN GUARDS. This file is RED before the fix and green after it, on the DEFECT's own
//! channel: under `-Ztrust-ir-lower` (any mode, `on` included) the crate finalizer runs final
//! module validation and EVERY validation error is fatal — `crate_module.rs`
//! `final_module_validation_errors` feeds `summary.errors`, and rustc_mir_build's
//! `trust_ir_crate_finalize` turns a non-empty list into `dcx().fatal`. Measured on the pre-fix
//! toolchain (trust-f2887e0d) with compiletest's check-pass invocation (`--emit=metadata`):
//!
//!   error: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [ConstTypeMismatch]: ConstTypeMismatch { location: "enum.0 (TensorStorage) layout",
//!   expected: "variant 0 field 0 to have a resolvable layout (needed to bound it within size
//!   16)", actual: "offset 0, layout UNRESOLVABLE for type struct.11: struct.9 has no size
//!   layout metadata" }
//!
//! The reproducer's derived `Clone` body ALSO carries `EnumCtor(unsupported payload)`,
//! `EnumMatch(default arm no value)` and `Unsize(non-slice target)` (measured under `=strict`,
//! same toolchain) — none of them v39's, and under `=on` none of them an error — which is why
//! the reproducer lives here and not under `=strict`. The two niche bodies are green in
//! isolation on the pre-fix toolchain (measured; why the niche-laid-out `Option<Arc<dyn ..>>`
//! does not trip the same validator is not established here), so they ride along as the second
//! shape the nn log named, not as a second red.
//!
//! The SPELLING has two further pins: the crate-level `container_pointee_spelling_tests`
//! (`vtable_metadata_pointee_is_the_two_lane_container_vtable_pointer`), and the strict twin
//! `trust_ir_lower_dyn_tail_container_strict.rs`, which catches a regression on the per-body
//! TAG channel — a re-spelling that leaves the module valid but re-tags the type, which this
//! file cannot see.

#![allow(dead_code)]

// ---- the reproducer, verbatim (the minimal nn-autodiff shape)

use std::any::Any;
use std::sync::Arc;
#[derive(Clone)]
pub enum TensorStorage {
    Cpu(Arc<dyn Any + Send + Sync>),
}
pub struct DynTensor {
    dims: Vec<usize>,
    dtype: u8,
    pub storage: TensorStorage,
}
impl DynTensor {
    pub fn ndim(&self) -> usize { self.dims.len() }
}

// ---- the niche case the nn log also reported: `Option<Arc<dyn ..>>`

pub fn no_storage() -> Option<Arc<dyn Any + Send + Sync>> {
    None
}

pub fn forward_storage(
    s: Option<Arc<dyn Any + Send + Sync>>,
) -> Option<Arc<dyn Any + Send + Sync>> {
    s
}

fn main() {}

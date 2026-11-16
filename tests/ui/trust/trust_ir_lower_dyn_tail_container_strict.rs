//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//@ edition: 2021
//! Trust (trust-ir v39, `FatPtrKind::ContainerVtable`): the STRICT twin of
//! `trust_ir_lower_dyn_tail_container_layout.rs` — same defect, the other channel.
//!
//! The layout pin goes red on the DEFECT's channel: the crate finalizer's fatal final module
//! validation (`ConstTypeMismatch` on the enum holding the `Arc<dyn ..>`), which every
//! `-Ztrust-ir-lower` mode enforces. This file goes red on the SPELLING's channel: under
//! `=strict` every tag the producer pushes is a `span_err` (rustc_mir_build `builder/mod.rs`, the
//! `trust_ir_lower_strict()` gate), so a body whose ONLY tag was the dyn-tail spelling refusal is
//! red before v39 and green after it. It stays a detector for a regression the layout pin cannot
//! see — a re-spelling that leaves the module valid but re-tags the type.
//!
//! PORTED 2026-09-25 (from 7b85680de6). On today's main this file is NOT a red-to-green pin: it
//! is green on seal trust-7d5533b2 (built from main of 2026-09-23, `Vtable` arm still `None`) as
//! well as on the build carrying the new spelling, so main no longer raises these signature-only
//! tags as strict errors in these bodies. The layout pin is the discriminating one (measured red on
//! that seal, green with the port). This file is kept for the other direction: the
//! `FatPtr(ContainerVtable)` spelling must add NO strict tag to any of these bodies.
//!
//! MEASURED before the fix on the ORIGINAL line (toolchain trust-f2887e0d,
//! `-Ztrust-ir-lower=strict`), each body's COMPLETE tag list:
//!   * `take_ref`   — 1 tag: `Ty(fat pointee) at &Foo<dyn Any>` (the `ty::Ref` catch-all, where
//!     `container_pointee_ty(PointeeMeta::Vtable)` answered `None`).
//!   * `take_raw`   — 1 tag: `Ty(raw-ptr fat/array pointee) at *const Foo<dyn Any>` (the
//!     raw-pointer catch-all, same answer).
//!   * `arc_by_val` — 1 tag: `Ty(raw-ptr fat/array pointee) at *const ArcInner<dyn Any + Send +
//!     Sync>` — the nn-autodiff shape itself: `Arc<dyn ..>` is `NonNull<ArcInner<dyn ..>>`.
//!   * the controls `cl_take`, `cl_take_raw`, `dyn_take`, `arc_take` — no tag.
//! The v39 spelling removes exactly those three tags; nothing else in these bodies changes.
//!
//! WHY NO BODY READS ITS FAT PARAM. Two shapes that look simpler are deliberately absent, because
//! they carry tags that are not v39's and would keep this file red on both sides of the fix:
//!   * an identity forward (`fn f(w: &Foo<dyn Any>) -> &Foo<dyn Any> { w }`): rustc inserts an
//!     `Unsize` adjustment on a dyn-tailed CONTAINER even at identical types (it does not on a
//!     bare `&dyn Any`), and the wave-CD unsize arm refuses a `Vtable`-tailed target with
//!     `Unsize(non-slice target)` — measured on `&Foo<dyn Any>`, `*const Foo<dyn Any>` and
//!     `Arc<dyn Any + Send + Sync>` alike;
//!   * a field read through the container pointer (`w.head`, `(*p).head`) takes
//!     `Deref(non-borrow ptr)` + `Field(unsupported lhs)` for `ContainerLen` and
//!     `ContainerVtable` alike.
//! This pin is about the SPELLING of the type, which `map_ty` decides on the signature whether or
//! not the body touches the value; the bodies return their scalar so the spelling is all there is.

#![allow(dead_code, unused_variables)]

use std::any::Any;
use std::sync::Arc;

pub struct Foo<T: ?Sized> {
    pub head: u32,
    pub tail: T,
}

// Red before v39: `Ty(fat pointee)` off the `ty::Ref` catch-all.
pub fn take_ref(w: &Foo<dyn Any>, n: u32) -> u32 {
    n
}

// Red before v39: `Ty(raw-ptr fat/array pointee)` off the raw-pointer catch-all.
pub fn take_raw(p: *const Foo<dyn Any>, n: u32) -> u32 {
    n
}

// Red before v39: the nn-autodiff shape itself — `Arc<dyn ..>`'s `*const ArcInner<dyn ..>` field.
pub fn arc_by_val(a: Arc<dyn Any + Send + Sync>, n: u32) -> u32 {
    n
}

// Controls, measured clean before v39 (so they cannot be what goes green): the `ContainerLen`
// twins (v38, the slice-tail sibling of the same class) ...
pub fn cl_take(f: &Foo<[u8]>, n: u32) -> u32 {
    n
}
pub fn cl_take_raw(p: *const Foo<[u8]>, n: u32) -> u32 {
    n
}
// ... the `TraitObject` twin — a pointee that IS the dyn, not one that contains it ...
pub fn dyn_take(w: &dyn Any, n: u32) -> u32 {
    n
}
// ... and a thin shared reference to the container, which was never in the refused class.
pub fn arc_take(a: &Arc<dyn Any + Send + Sync>, n: u32) -> u32 {
    n
}

fn main() {}

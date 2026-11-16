//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aprivate_interfaces
//@ edition: 2021
//! Trust (wave-CDR): `&*r` where the pointee merely CONTAINS a DST in TAIL position -- `&Path`,
//! `&OsStr`, `&List<T> { skel: [T] }`.
//!
//! T5 gave that class a first-class 16-byte spelling in BOTH `map_ty` (the ref catch-all's
//! `container_pointee_ty(PointeeMeta::Len)` -> `Ty::FatPtr(ContainerLen)`) and `fat_shape`
//! (`fat_shape_of_container_pointee`, DERIVED from the same function so the two "CANNOT drift").
//! The reborrow gate was the third site nobody moved: it still tests the pre-T5 depth-0 list, so
//! `fat_shared_ref`'s `matches!(pointee.kind(), Str | Slice | Dynamic)` fails on an `Adt` pointee,
//! and the thin twin's `inner_thin` conjunct fails because `fat_shape` correctly answers `Fat`.
//! BOTH accept arms miss, for opposite reasons.
//!
//! One bit apart: `container_tail` below refuses today while `sized_tail` is clean through the
//! thin twin and `str_pointee` is clean through the fat one. The `&Wrap` SIGNATURE is already
//! clean, so the fat spelling is shipped and accepted as a param, a return, a tuple element and a
//! call argument -- everywhere except this gate.
//!
//! THE AFFIRMATIVE ALLOW-LIST is the `map_ty(expr_ty) == FatPtr(ContainerLen)` conjunct (since
//! trust-ir v39 also `FatPtr(ContainerVtable)`), not a negation. `map_ty` mints those spellings
//! from two sites, but only one is reachable once the first two conjuncts have required a shared
//! `ty::Ref` on both sides -- the other is the RAW-POINTER catch-all, which a reference cannot
//! reach. Reaching it requires `pointee_is_the_dst == false` (so `[T]`/`str`/`dyn` pointees are
//! excluded BY CONSTRUCTION) and `pointee_meta == Len | Vtable` (so `Thin`/`Unknown`, which map
//! to `Ty::Ptr`, are excluded). Before v39 `Vtable` mapped to `None` and was excluded here too;
//! it joins on the same identity-forward argument `fat_shared_ref` already makes for `&dyn`.
//!
//! A `&mut` SOURCE IS REFUSED BY CONJUNCTS 1 AND 3, NOT BY 4/5, and that is worth pinning because
//! the natural reading is the opposite. Measured: `fat_shape` of a `&mut` container pointee is
//! `Fat` -- the mut arm falls through to `fat_shape_of_container_pointee` for a container pointee
//! -- so `mut_container_source` passes conjuncts 4 and 5 AND the `map_ty` conjunct. It is the
//! refusal NEAREST the accepted set, and relaxing `inner_is_shared_ref` alone would admit it.
//!
//! Not under `=strict`: the negatives must keep their tags.

#![allow(dead_code, unused_variables)]

fn take<T: ?Sized>(_x: &T) {}

struct Wrap {
    n: u32,
    inner: [u8],
}

struct WrapS {
    n: u32,
    inner: u8,
}

struct StrTail {
    n: u32,
    t: str,
}

struct Nest {
    h: u64,
    inner: StrTail,
}

struct TupTail(u32, (u8, [u16]));

// THE LANE: a slice tail.
pub fn container_tail(w: &Wrap) {
    take(&*w);
}

// THE LANE: a `str` tail.
pub fn str_tail(w: &StrTail) {
    take(&*w);
}

// THE LANE: a NESTED struct tail.
pub fn nested_tail(w: &Nest) {
    take(&*w);
}

// THE LANE: a TUPLE tail.
pub fn tuple_tail(w: &TupTail) {
    take(&*w);
}

// CONTROL, clean before this wave: the same struct with a SIZED tail goes through the thin twin.
pub fn sized_tail(w: &WrapS) {
    take(&*w);
}

// CONTROL, clean before this wave: a DST pointee goes through the fat arm's depth-0 list.
pub fn str_pointee(s: &str) {
    take(&*s);
}

// CONTROL, clean before this wave: the fat container spelling is already accepted in a SIGNATURE.
pub fn container_signature(w: &Wrap) {
    let _ = w;
}

// FAIL-CLOSED, and the refusal NEAREST the accepted set: a `&mut` source. It passes the two
// fat-shape conjuncts and the `map_ty` conjunct, and is refused by the shared-ref and
// identity-modulo-regions conjuncts alone.
pub fn mut_container_source(d: &mut StrTail) {
    take(&*d);
}

// FAIL-CLOSED CONTROLS: the clean-today shapes a future widening of the tail walk would move
// first. Both keep `map_ty == Ty::Ptr`, so the last conjunct refuses them. (The extern-type tail
// -- `PointeeMeta::Thin` -- belongs here too and is the third such control; it needs a
// `#[repr(C)]`-shaped declaration this fixture does not otherwise want, so it is named rather
// than written.)
struct G<T: ?Sized> {
    n: u32,
    t: T,
}

pub fn param_tail_stays_thin<T: ?Sized>(w: &G<T>) {
    take(&*w);
}

pub fn sized_param_stays_thin(w: &G<u32>) {
    take(&*w);
}

fn main() {}

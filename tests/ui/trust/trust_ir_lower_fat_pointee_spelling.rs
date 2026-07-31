//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (plan 2026-07-29 T5): a pointer whose pointee CONTAINS a DST in tail
//! position is a FAT pointer, and `map_ty`'s two pointer CATCH-ALLS used to
//! spell every one of them thin.
//!
//! The reachable instance is `Arc<str>`: `Arc` holds `NonNull<ArcInner<str>>`,
//! which holds `*const ArcInner<str>`, whose pointee is an `ArcInner` with a
//! `str` TAIL — so rustc lays the pointer out as a 16-byte `(data, len)` pair.
//! The RawPtr arm's `_ => Ty::Ptr` matched it (the pointee is a `ty::Adt`, not
//! `ty::Str`/`ty::Slice`) and signed 8 bytes.
//!
//! MEASURED before the fix, on the 2026-07-13 seed trustc, dumping
//! `struct Holder { tag: u64, s: Arc<str> }` with
//! `-Ztrust-ir-lower=on -Ztrust-ir-dump=<dir>`:
//!
//! ```text
//! struct @NonNull { ptr } id=0
//! struct @Arc { struct.0, struct.1, struct.2 } id=3
//! struct @Holder { u64, struct.3 } id=4
//! ```
//!
//! ONE thin field for `NonNull<ArcInner<str>>`, while `register_struct` records
//! rustc's true `size = 16`. The def was self-inconsistent — declared 16 bytes,
//! field types summing to 8 — with the length lane simply absent, so a
//! whole-value `Load`/`Store` of that struct drops the metadata.
//!
//! This matters to the crystal because the chain is exactly
//! `Level::Param(Name)` -> `Name` -> `NameInner::Str(Arc<Name>, Arc<str>)`
//! -> `Arc<str>` (first-party/clean crates/clean-kernel/src/name.rs:157,
//! level/mod.rs:184), i.e. it is reachable from the designated width-one
//! target `Level::is_zero`.
//!
//! WHAT THIS FIXTURE PINS: check-pass, i.e. the tail walk TERMINATES and the
//! affected shapes still compile — including the recursive `Arc<MyName>` edge,
//! where a naive tail walk would loop. The SPELLING itself is pinned by the
//! crate-level `container_pointee_spelling_tests` (the metadata-class table and
//! the `map_ty` <-> `fat_shape` lockstep), because a ui test cannot read the
//! dumped module. The end-to-end census delta is measured by the next trustc
//! stage rebuild (plan job T4), not by this fixture.

#![allow(dead_code)]

use std::sync::Arc;

// ---- the reachable instance: a str-tailed pointee behind the raw-ptr catch-all

pub struct Holder {
    pub tag: u64,
    pub s: Arc<str>,
}

pub fn tag_of(h: Holder) -> u64 {
    h.tag
}

// The clean-kernel shape verbatim: a recursive name tree carrying `Arc<str>`,
// reached through an enum payload. Pins that the tail walk terminates on the
// `Arc<MyName>` cycle (it stops at the raw pointer; it does not recurse into
// pointees) and that the enum still registers.
pub struct MyName {
    inner: MyNameInner,
    cached_hash: u64,
}

pub enum MyNameInner {
    Anon,
    Str(Arc<MyName>, Arc<str>),
    Num(Arc<MyName>, u64),
}

pub enum MyLevel {
    Zero,
    Succ(Arc<MyLevel>),
    Param(MyName),
}

pub fn is_zero(l: &MyLevel) -> bool {
    match l {
        MyLevel::Zero => true,
        MyLevel::Succ(_) | MyLevel::Param(_) => false,
    }
}

// ---- other tail-metadata classes

// A slice tail (`usize` metadata) behind a struct, not a bare `[T]`.
pub struct SliceTailed {
    pub tag: u64,
    pub rest: [u8],
}
pub fn slice_tailed(_p: *const SliceTailed) -> u64 {
    0
}

// A boxed slice / boxed str: the same `NonNull<[T]>` / `NonNull<str>` shape one
// level up from `Arc`.
pub struct Boxed {
    pub a: Box<str>,
    pub b: Box<[u32]>,
}
pub fn boxed_tag(b: &Boxed) -> usize {
    b.a.len() + b.b.len()
}

// ---- THIN CONTROLS: these must keep their existing spelling, unchanged

// A sized pointee: genuinely one address.
pub struct ThinHolder {
    pub tag: u64,
    pub s: Arc<u64>,
}
pub fn thin_tag_of(h: ThinHolder) -> u64 {
    h.tag
}

// A sized-tailed struct behind a raw pointer.
pub struct SizedTail {
    pub a: u32,
    pub b: [u8; 8],
}
pub fn sized_tail(p: *const SizedTail) -> usize {
    p as usize
}

// A generic `?Sized` pointee forwarded by a generic body: the tail is a bare
// `ty::Param`, so the metadata is NOT determinable here and the pre-existing
// thin spelling is kept deliberately (its soundness is the wave-19
// `sig_shapes_coherent` argument: every unsized CONCRETE instantiation is
// rejected at the outer call site).
pub fn forward<T: ?Sized>(x: &T) -> *const T {
    x as *const T
}
pub fn forward_sized(x: &u64) -> *const u64 {
    forward(x)
}

// A thin reference to a sized local — the plainest control of all.
pub fn thin_ref(x: &u64) -> u64 {
    *x
}

fn main() {}

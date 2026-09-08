//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-CP): a THIN raw-pointer -> raw-pointer `as` cast is a pure
//! RE-TYPING of an already-opaque address, lowered to one
//! `Inst::Cast { op: PtrToPtr, Ty::Ptr -> Ty::Ptr }` — the identity on the
//! pointer value in the reference interpreter, carrying provenance through and
//! minting none.
//!
//! Every function below carried `Cast(ptr source)` before the wave; `strict`
//! turns that tag into a compile error, so this file IS the mutation check:
//! revert the lane and all six error at their own `fn` span.
//!
//! WHAT THIS FILE DELIBERATELY DOES NOT CONTAIN — and why it cannot. The lane's
//! load-bearing conjuncts are REFUSALS (`ptr -> int`, `int -> ptr`,
//! thin<->fat, a `ty::Ref` on either side, and any operand already in
//! `borrow_ptrs`), and under `strict` a refusal is a compile error, so a
//! refusal cannot share a file with a check-pass admission. They live in
//! `trust_ir_lower_ptr_ptr_cast_refuses.rs`, whose witness is the one that
//! matters: `let x = 5u32; core::ptr::addr_of!(x) as *const u8` returned from
//! the function. Its operand is a LEDGERED frame snapshot, returning it
//! uncast is already `Return(borrow ptr escapes tail)`, and dropping the
//! `is_borrow_ptr` guard here would launder it into an unledgered `Ty::Ptr`
//! and hand the return-escape guards a dangling frame address — a false
//! verify, not a coverage gain.

#![allow(dead_code)]

// ---- the plain thin re-typings

pub fn retype(p: *const u8) -> *const u32 {
    p as *const u32
}

// `*mut T -> *const T` is deliberately NOT pinned here. Measured on the subject
// build: it never reaches this arm at all — rustc inserts a COERCION for the
// mut->const direction, so the body refuses earlier with
// `Coercion(mut->const raw ptr)`. It is pinned as a still-refused shape in
// `trust_ir_lower_ptr_ptr_cast_refuses.rs` instead. The const->mut direction
// below IS a real `ExprKind::Cast` and is covered.

pub fn mutify(p: *const u32) -> *mut u32 {
    p as *mut u32
}

// ---- `tests/ui/cast/ptr-ptr-to-ptr-ptr-different-regions.rs`: a REGION-only
// re-typing behind two layers of indirection. The outer pointer is thin (its
// pointee is itself a pointer, which is `Sized`), so both sides map `Ty::Ptr`
// even though the innermost pointee is `dyn`.

pub trait Trait {
    fn foo(&self) -> u32 {
        0
    }
}

pub fn widen_region<'a>(a: *mut *mut (dyn Trait + 'a)) -> *mut *mut (dyn Trait + 'static) {
    a as _
}

// ---- `tests/ui/cast/cast-pointee-projection.rs`: the IDENTITY-ALIAS pointee.
// `<Self as Tag<'_>>::Type` is `?Sized` and does not normalize here, so
// `pointee_meta` answers `Unknown` and `map_ty` keeps the PRE-EXISTING thin
// spelling on BOTH sides (the same posture `unsize_dyn_source_is_thin_ptr`
// takes). The emitted instruction claims only "the result IS the operand",
// which holds at every instantiation whatever width the pointer really has;
// the thin SIGNATURE, which this cast does not touch, is what
// `sig_shapes_coherent` / `force_havoc` govern.

pub trait Tag<'a> {
    type Type: ?Sized;
}

pub trait IntoRaw: for<'a> Tag<'a> {
    fn into_raw(this: *const <Self as Tag<'_>>::Type) -> *mut <Self as Tag<'_>>::Type;
}

impl<T: for<'a> Tag<'a>> IntoRaw for T {
    fn into_raw(this: *const <Self as Tag<'_>>::Type) -> *mut <Self as Tag<'_>>::Type {
        this as *mut T::Type
    }
}

// ---- `tests/ui/consts/const-eval/heap/alloc_intrinsic_zero_sized.rs`: the
// re-typing whose operand is a CALL result rather than a parameter — the
// pointer is opaque either way, and the lane never reads it.

pub struct Zst;

pub fn retype_call_result(p: *mut u8) -> *mut Zst {
    p as *mut Zst
}

fn main() {}

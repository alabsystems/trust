//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-RAS): the array-to-slice unsize whose SOURCE IS ALREADY A
//! `&[T; N]` REFERENCE VALUE — a caller PARAMETER — rather than an array PLACE.
//!
//! `build_slice_fat_ptr` models `&a`: it snapshots the array aggregate into an
//! `Alloca` and takes the slot address. There is no array to snapshot in
//! `fn f(x: &[T; N]) -> &[T] { x }` — only a pointer the caller already formed —
//! so the place peel bottomed out at a local of type `&[T; N]` and every body
//! below recorded `Slice(non-array operand)` (plus, where the coerced value is a
//! call ARGUMENT, a `Call(unsupported arg)` whose detail reads
//! `[masking: Slice(non-array operand)]`).
//!
//! The lane emits what the MIR-side ORACLE emits for the same coercion:
//! `crates/trust-ir-bridge/src/lower.rs`'s `Rvalue::Cast` arm calls
//! `array_to_slice_pointer_cast` and then
//! `emit_slice_fat_pointer(<target fat ty>, <the source pointer verbatim>,
//! <u64 const len>)` — a `PtrFromParts` over the UNMODIFIED pointer, with no
//! `Alloca` and no `Store`. `PointerCoercion::Unsize` changes no address; it only
//! attaches the length. So the producer now AGREES with the oracle here instead
//! of snapshotting, and the emitted value is strictly more faithful than the
//! place path it sits in front of.
//!
//! THE FENCE, which is the whole soundness argument: the pointer must be in
//! `ref_param_ptrs`. A `&local` / rvalue SNAPSHOT pointer addresses an `Alloca`
//! COPY in the producer's own frame, so a slice minted over one would hand the
//! caller a fat pointer into producer-private memory. Those live in `borrow_ptrs`
//! ONLY, never in `ref_param_ptrs`, and the lane declines them — `let a = [1u8,
//! 2, 3]; let r = &a; let s: &[u8] = r;` still records `Slice(non-array
//! operand)`. Nothing is added to any ledger: the minted fat value is a fresh
//! unledgered id, so no frame-derived address is laundered into
//! `interior_ptrs` / `global_ptrs` / `ref_param_ptrs`.
//!
//! Under `strict`, every body here must be BOTH clean and non-diverging against
//! the MIR re-derived from its own trust-ir. The refusal twins (the `&local`
//! snapshot above, `&mut [T; N]`, a `Vec` operand) cannot live in a strict file
//! at all — a refusal is a hard error here — so they are stated, not fixtured;
//! a non-strict refusal pin is the right home if one is wanted.

/// The corpus body `tests/ui/consts/const-extern-fn/const-extern-fn.rs::unsize`,
/// in its plain-`fn` spelling: the whole body is the coercion.
pub fn unsize_param(x: &[u8; 3]) -> &[u8] {
    x
}

/// The corpus body itself. `const extern "C"` changes nothing about the
/// coercion; it is here because that is the shape that was measured.
#[allow(improper_ctypes_definitions)]
pub const extern "C" fn unsize_const_extern(x: &[u8; 3]) -> &[u8] {
    x
}

/// `tests/ui/coercion/coerce-unsize-subtype.rs::long_to_short`. The element is a
/// generic THIN reference, not a scalar: this lane admits exactly the element set
/// `map_ty` already admits for the `&[T]` TYPE, because it stores nothing and so
/// needs no `is_scalar_ty` round-trip gate.
pub fn long_to_short<'a, 'b, T>(xs: &'b [&'static T; 1]) -> &'b [&'a T] {
    xs
}

/// `associated-types-conditional-dispatch.rs::{impl#1}::eq`'s `other: &[B; 0]`.
/// A ZERO-length array needs no special case: the address is the caller's, the
/// length is 0, and no element is ever read through it.
pub fn zero_len<B>(x: &[B; 0]) -> &[B] {
    x
}

fn lub_short<'a, T>(_: &[&'a T], _: &[&'a T]) {}

/// `coerce-unsize-subtype.rs::long_and_short`: the coerced value is a call
/// ARGUMENT, so the masking `Call(unsupported arg)` retires with the leaf.
pub fn call_arg<'a, T>(xs: &[&'static T; 1], ys: &[&'a T; 1]) {
    lub_short(xs, ys);
}

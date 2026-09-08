//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
//@ forbid-output: CallEdgeSignatureMismatch
//@ dont-check-compiler-stderr

//! Concrete generic instances retain identity through direct and reified uses. The `forget`
//! pair catches DefId-only interning with visibly different signatures; the `pick` pair catches
//! signature-only interning because its const-generic instances have identical signatures but
//! different semantics.

pub fn forget_u32_direct(value: u32) {
    core::mem::forget::<u32>(value);
}

pub fn forget_u32_pointer() {
    let _pointer: fn(u32) = core::mem::forget::<u32>;
}

pub fn forget_u64_pointer() {
    let _pointer: fn(u64) = core::mem::forget::<u64>;
}

pub fn forget_u64_direct(value: u64) {
    core::mem::forget::<u64>(value);
}

#[inline(never)]
pub fn pick<const N: u32>() -> u32 {
    N
}

pub fn pick_one_direct() -> u32 {
    pick::<1>()
}

pub fn pick_one_pointer() {
    let _pointer: fn() -> u32 = pick::<1>;
}

pub fn pick_two_pointer() {
    let _pointer: fn() -> u32 = pick::<2>;
}

pub fn pick_two_direct() -> u32 {
    pick::<2>()
}

// Only one concrete instance is used. Because `T` is computationally irrelevant, the generic
// definition itself can lower and splice under its identity signature; its bodyless `::<u8>`
// instance must nevertheless receive a distinct reserved operational name.
#[inline(never)]
pub fn single_instance<T>(value: u32) -> u32 {
    value + 1
}

pub fn single_instance_direct(value: u32) -> u32 {
    single_instance::<u8>(value)
}

pub fn single_instance_pointer() {
    let _pointer: fn(u32) -> u32 = single_instance::<u8>;
}

#[cfg(runtime)]
fn main() {
    forget_u32_direct(7);
    forget_u64_direct(9);
    assert_eq!(4 * (pick_one_direct() + pick_two_direct()), 12);
    assert_eq!(single_instance_direct(41), 42);
}

//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit (`-Ztrust-verify=off`, `-Zalways-encode-mir`), whose non-generic bodies
//! a caller that DECLARES it (`-Ztrust-bundle-foreign-crate=xcunsafe_dep`)
//! bundles as members. Consumed by `xcrate_declared_member_unsafe_source.rs`.
//!
//! `extend` and `noop_unsafe` ARE THE ASSERTIONS: do not remove their `unsafe`.
#![crate_name = "xcunsafe_dep"]

/// A lifetime-only `transmute`: InstSimplify erases it to a plain copy, so
/// this crate's encoded MIR carries no trace of it. A LOCAL copy is refused by
/// the HIR half of `validity_transmute`; a declaring caller bundled this body
/// from its MIR alone and built rc=0 (stage-1 snapshot at `4e9fe36bf`).
pub fn extend(r: &u32) -> u32 {
    let s: &'static u32 = unsafe { core::mem::transmute::<&u32, &'static u32>(r) };
    *s
}

/// An `unsafe` block around a SAFE expression: no unsafe operation in the MIR
/// at all (the block vanishes), so only the source fact this crate encodes can
/// decline it. No call either: a call to anything outside the declared scope
/// would keep it out of the bundle for an unrelated reason
/// (`foreign_member_has_uncharged_panic_path`).
pub fn noop_unsafe(x: u32) -> u32 {
    #[allow(unused_unsafe)]
    let d = unsafe { 2u32 };
    x / d
}

/// The control: `noop_unsafe` without the `unsafe` block.
pub fn plain(x: u32) -> u32 {
    let d = 2u32;
    x / d
}

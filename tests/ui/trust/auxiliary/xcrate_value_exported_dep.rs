//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! Three bodies with a TRUE `ensures result <= 31`: the mangled control, one
//! exported unmangled, and one whose only difference is an `unsafe` block around
//! a SAFE expression. Consumed by `cross_crate_value_exported_not_reused.rs`
//! (D4 increment A, 2026-09-24): an unmangled symbol can be interposed at link
//! time, so the body re-derived from this MIR need not be the one that runs,
//! and its clause is never reused. The `unsafe`-block twin's MIR carries no
//! unsafe operation, so only the user-`unsafe` SOURCE FACT this crate encodes
//! beside its MIR can decline it (D4-A: re-derivation declines any body whose
//! fact is true). The mangled twin is the control.
#![no_std]
#![crate_name = "xcvalue_exported_dep"]

/// Mangled: re-derivable, its clause reusable by a declaring caller.
pub fn clamp_index(k: u32) -> u32 ensures result <= 31 {
    if k > 31 {
        return 31;
    }
    k
}

/// The same body, exported unmangled. Never credited from this MIR.
#[unsafe(no_mangle)]
pub fn xcvalue_clamp_index_exported(k: u32) -> u32 ensures result <= 31 {
    if k > 31 {
        return 31;
    }
    k
}

/// The same body plus an `unsafe` block around a safe expression. Never
/// credited from this MIR: its source fact is `true`.
pub fn clamp_index_unsafe_src(k: u32) -> u32 ensures result <= 31 {
    #[allow(unused_unsafe)]
    let _n = unsafe { core::mem::size_of::<u8>() };
    if k > 31 {
        return 31;
    }
    k
}

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ build-pass
//! Regression for the trustc "Group A" ICE (10/13 crash dumps): a still-generic
//! body carrying a two-level associated-const projection
//! `<<F as SqrtHelper>::ISet1 as MinInt>::BITS` used to ICE during Trust MIR
//! extraction. `F` is a live type param, so `<F as SqrtHelper>::ISet1` is a
//! rigid projection; `convert_const_operand`'s int/char/uint eval fallbacks
//! forced `try_eval_bits(.., fully_monomorphized())`, routing into
//! `resolve_instance -> normalize_erasing_regions -> NoSolution` (a `bug!` at
//! `rustc_middle/src/ty/normalize_erasing_regions.rs:171`).
//!
//! The fix guards those fallbacks with a `has_non_region_param()` monomorphism
//! check (`try_eval_bits_mono`, mirroring the sibling `const_operand_value`), so
//! a generic const degrades to `OpaqueScalar` instead of forcing codegen-style
//! resolution before monomorphization. This fixture compiles the minimal
//! trigger under the nonfatal lame policy; it must `build-pass` (no ICE).
//!
//! Reproduces the exact shape observed in libm `math::generic::sqrt`.
//! Requires the stage2 `trustc` toolchain (verify runs in the compiler).

pub trait MinInt {
    const BITS: u32;
}

pub trait SqrtHelper {
    type ISet1: MinInt;
}

// Generic body: `<F::ISet1 as MinInt>::BITS` stays a rigid two-level assoc-const
// projection at extraction time. Must extract without ICE (const -> OpaqueScalar).
pub fn generic_assoc_const_bits<F: SqrtHelper>() -> u32 {
    <F::ISet1 as MinInt>::BITS
}

fn main() {}

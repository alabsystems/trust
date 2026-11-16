//@ needs-trust-verify
//@ aux-build:xcrate_value_exported_dep.rs
//@ revisions: mangled exported unsafe_src
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=xcvalue_exported_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[mangled] check-pass
//@[exported] check-fail
//@[unsafe_src] check-fail
//! D4 increment A (2026-09-24), the D4 critique's interposition condition: a
//! foreign `#[no_mangle]`/`#[export_name]`/`#[linkage]` body is never credited
//! from its encoded MIR — not by the shared panic-freedom bar
//! (`xcrate_fmt_dep.rs`, revision `exported`) and not by postcondition reuse
//! (`callee_postconditions_are_reusable_reasoned`: `identity:symbol-exported`).
//! Another object can supply that symbol at link or load time, so the body
//! checked here need not be the body that runs.
//!
//! The callees are TRUE and differ from the control in exactly one thing each:
//! `exported`'s symbol is unmangled; `unsafe_src`'s body wraps a SAFE
//! expression in an `unsafe` block, so its MIR has no unsafe operation and only
//! the user-`unsafe` source fact its crate encoded can decline it
//! (`identity:user-unsafe-source`). `mangled` is the control and must PASS, or
//! the other two prove nothing. `exported` and `unsafe_src` must STAY REFUSED.
//!
//! Measured BEFORE (stage-1 with wave 0, `a8c853de6f`; re-measured on the
//! stage-1 snapshot at `4e9fe36bf` through a compiletest-equivalent harness):
//! EVERY revision refused ("Trust Level 0 safety verification incomplete ... 2
//! obligation(s) were not proved") — the `ExternalDep` bucket kept the callee
//! out of the declared scope entirely, so the clause was never reused.
extern crate xcvalue_exported_dep;

#[cfg(mangled)]
pub fn bump_capped() -> u32 {
    let c = xcvalue_exported_dep::clamp_index(3);
    c + 1
}

#[cfg(exported)]
pub fn bump_capped() -> u32 { //[exported]~ ERROR Trust strict verification failed
    let c = xcvalue_exported_dep::xcvalue_clamp_index_exported(3);
    c + 1
}

#[cfg(unsafe_src)]
pub fn bump_capped() -> u32 { //[unsafe_src]~ ERROR Trust strict verification failed
    let c = xcvalue_exported_dep::clamp_index_unsafe_src(3);
    c + 1
}

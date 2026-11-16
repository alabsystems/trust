//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! FFI-STD-QPATH-1 review, finding 3 (2026-10-26): a qualified-path or generic callee
//! is never itself a foreign item, but its generic arguments can carry a foreign fn
//! that it then calls. Here a SAFE foreign `strlen(*const c_void)` is handed to a std
//! iterator adaptor, to a user generic `apply<F: Fn(..)>`, through a `&dyn Fn` and as
//! a reified `fn` pointer. Before FFI-STD-QPATH-1 each of these callers carried an
//! extra `unmodeled FFI call` row, ONLY because `core::ffi::c_void` appears in the
//! callee's spelling; the exemption dropped it.
//!
//! What must hold, and what this file pins: each is still REFUSED, by the rule for
//! the call that actually reaches the foreign code (the
//! `[trust-absent-callee-assumption]` row on the `Fn*::call` of the foreign fn item,
//! `fn` pointer or `dyn`; for `apply`'s own body, the untypeable indirect call), and
//! with the SAME verdict as its `_twin` — the same program over a foreign
//! `labs(i64)` whose spelling names no `ffi` module, which the name fallback never
//! routed before or after. The twin is the soundness argument made executable: the
//! spelling of a std ffi type was never what refused these calls. (`apply`/`apply_twin`
//! differ only in WHICH rule refuses the generic body: an untypeable indirect call
//! over a raw pointer argument versus the per-instance hypothesis; both are errors.)
//!
//! Measured 2026-10-26 on the stage 1 of `fix/ffi-std-qpath-20261025` with the
//! header's flags plus `-Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata`: every annotation below fires and nothing else is reported.

use core::ffi::c_void;

unsafe extern "Rust" {
    #[link_name = "strlen"]
    safe fn strlen(s: *const c_void) -> usize;
    safe fn labs(x: i64) -> i64;
}

/// `<Map<Copied<Iter<'_, *const c_void>>, fn(*const c_void) -> usize {strlen}> as Iterator>::next`.
pub fn via_iter_map(v: &[*const c_void]) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_iter_map`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_iter_map`: 1 obligation(s) were not fully verified
    let mut n = 0usize;
    for x in v.iter().copied().map(strlen) {
        n = n.wrapping_add(x);
    }
    n
}

pub fn via_iter_map_twin(v: &[i64]) -> i64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_iter_map_twin`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_iter_map_twin`: 1 obligation(s) were not fully verified
    let mut n = 0i64;
    for x in v.iter().copied().map(labs) {
        n = n.wrapping_add(x);
    }
    n
}

#[inline(never)]
fn apply<F: Fn(*const c_void) -> usize>(f: F, p: *const c_void) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::apply`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::apply`: 1 obligation(s) were not fully verified
    f(p)
}

/// `apply::<fn(*const c_void) -> usize {strlen}>`.
pub fn via_generic(p: *const c_void) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_generic`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_generic`: 1 obligation(s) were not fully verified
    apply(strlen, p)
}

#[inline(never)]
fn apply_twin<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    //~^ WARN Trust verification advisory for `ffi_std_qpath_foreign_fn_in_generic_arg::apply_twin`: 1 instance hypothesis row(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::apply_twin`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::apply_twin`: 1 obligation(s) were not fully verified
    f(x)
}

pub fn via_generic_twin(x: i64) -> i64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_generic_twin`: 1 obligation(s) were not proved
    //~^^ ERROR Trust instance discharge not established for `ffi_std_qpath_foreign_fn_in_generic_arg::via_generic_twin`
    //~^^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_generic_twin`: 1 obligation(s) were not fully verified
    apply_twin(labs, x)
}

/// `<dyn Fn(*const c_void) -> usize as Fn<(*const c_void,)>>::call`.
pub fn via_dyn(p: *const c_void) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_dyn`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_dyn`: 1 obligation(s) were not fully verified
    let f: &dyn Fn(*const c_void) -> usize = &strlen;
    f(p)
}

pub fn via_dyn_twin(x: i64) -> i64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_dyn_twin`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_dyn_twin`: 1 obligation(s) were not fully verified
    let f: &dyn Fn(i64) -> i64 = &labs;
    f(x)
}

/// A foreign fn reified to a Rust-ABI `fn` pointer, then handed to `Iterator::map`.
pub fn via_fnptr_map(v: &[*const c_void]) -> usize {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_fnptr_map`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_fnptr_map`: 1 obligation(s) were not fully verified
    let f: fn(*const c_void) -> usize = strlen;
    let mut n = 0usize;
    for x in v.iter().copied().map(f) {
        n = n.wrapping_add(x);
    }
    n
}

pub fn via_fnptr_map_twin(v: &[i64]) -> i64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_foreign_fn_in_generic_arg::via_fnptr_map_twin`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_foreign_fn_in_generic_arg::via_fnptr_map_twin`: 1 obligation(s) were not fully verified
    let f: fn(i64) -> i64 = labs;
    let mut n = 0i64;
    for x in v.iter().copied().map(f) {
        n = n.wrapping_add(x);
    }
    n
}

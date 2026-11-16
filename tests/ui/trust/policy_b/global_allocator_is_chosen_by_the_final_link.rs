//@ needs-trust-verify
//@ revisions: lib_certify lib_default bin_certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on
//@[lib_certify] compile-flags: --crate-type lib -Ztrust-policy=certify
//@[lib_default] compile-flags: --crate-type lib
//@[bin_certify] compile-flags: --crate-type bin -Ztrust-policy=certify
//@[lib_certify] check-fail
//@[lib_default] check-pass
//@[bin_certify] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Which `GlobalAlloc` runs behind `__rust_alloc` is decided by the FINAL LINK,
//! not by the crate that allocates (2026-10-02).
//!
//! An rlib cannot see the `#[global_allocator]` of the binary it is linked into,
//! nor one registered by a sibling dependency of that binary. Its allocations were
//! credited as if std's default `System` chain were behind the shim: MEASURED on
//! stage 1 of origin/main `280ff7c48cd` (m3), this file's four allocating functions
//! built exit 0 under `-Ztrust-policy=certify` (and the default policy) with
//! `functions_verified` 5 of 5 and no premise row — and a verify-off `main` whose
//! `#[global_allocator]` panics in `alloc` (registered in `main` itself, or by a
//! sibling dependency the library never sees) panicked in that allocator inside
//! each of the four (exit 101).
//!
//! Now a body that may reach a global-allocator shim is charged the
//! `contract:global-alloc-dealloc-panic-free` premise when the compilation is not
//! the final link: DISCHARGED vacuously (no allocator is in view), published as a
//! skipped row, so the function is no longer counted verified and is never
//! registered as unconditionally panic-free. A body that reaches no shim keeps its
//! credit (`plain`, `empty_vec`). In a binary (`bin_certify`) the allocator IS
//! decided here, so nothing new is charged.
//!
//! Each function also does one bounds-checked read (`T[i & 1]`), so that it has a
//! proved row and a per-function summary `NOTE` to pin (a function whose only row
//! is the premise prints none). "0 runtime-checked out of" matches only a summary
//! with NO skipped row, so it pins the controls and the binary as uncharged.
//!
//! The capability cost, pinned by `through_local_callee` under `lib_certify`: a
//! charged body is never registered as unconditionally panic-free (the registry
//! gate of the same contract), so a local caller's call to an allocating local
//! function keeps a runtime-checked panic-freedom row, which `certify` refuses —
//! the drop side's existing behaviour, now on the allocation side too.
//!
//! The in-graph case — a dependency of THIS crate registers the allocator — was
//! already refused on every lane (`global_alloc_dealloc_contract_*`,
//! `alloc_charged_callee_does_not_bless_local_caller.rs`).

const T: [u8; 2] = [7, 8];

pub fn box_returned(i: usize) -> Box<u8> {
    //[lib_certify,lib_default]~^ NOTE 0 runtime-checked, 1 skipped out of
    //[bin_certify]~^^ NOTE 0 runtime-checked out of
    Box::new(T[i & 1])
}

pub fn box_into_raw(i: usize) -> bool {
    //[lib_certify,lib_default]~^ NOTE 0 runtime-checked, 1 skipped out of
    //[bin_certify]~^^ NOTE 0 runtime-checked out of
    let p = Box::into_raw(Box::new(T[i & 1]));
    p.is_null()
}

pub fn to_string(i: usize) -> String {
    //[lib_certify,lib_default]~^ NOTE 0 runtime-checked, 1 skipped out of
    //[bin_certify]~^^ NOTE 0 runtime-checked out of
    T[i & 1].to_string()
}

pub fn string_forgotten(i: usize) {
    //[lib_certify,lib_default]~^ NOTE 0 runtime-checked, 1 skipped out of
    //[bin_certify]~^^ NOTE 0 runtime-checked out of
    let s = String::from(T[i & 1] as char);
    std::mem::forget(s);
}

fn make(i: usize) -> Box<u8> {
    //[lib_certify,lib_default]~^ NOTE 0 runtime-checked, 1 skipped out of
    //[bin_certify]~^^ NOTE 0 runtime-checked out of
    Box::new(T[i & 1])
}

/// Allocates only inside a local callee: the walk follows the call, so this body
/// carries the premise too. Its call to `make` is undischarged in an rlib (above).
pub fn through_local_callee(i: usize) -> Box<u8> {
    //[lib_default]~^ NOTE 1 runtime-checked, 1 skipped out of
    //[lib_certify]~^^ ERROR safety verification incomplete
    //[lib_certify]~| ERROR strict verification failed
    //[bin_certify]~^^^^ NOTE 0 runtime-checked out of
    let _ = T[i & 1];
    make(i)
}

/// Controls: no global-allocator shim is reachable, so no premise row.
pub fn plain(i: usize) -> u8 {
    //~^ NOTE 0 runtime-checked out of
    T[i & 1] / 2
}

pub fn empty_vec(i: usize) -> Vec<u8> {
    //~^ NOTE 0 runtime-checked out of
    let _ = T[i & 1];
    Vec::new()
}

/// Each function is called (a binary verifies only what it reaches), and each
/// result is forgotten so `main` itself drops nothing.
#[cfg(bin_certify)]
fn main() {
    //[bin_certify]~^ NOTE 0 runtime-checked out of
    std::mem::forget(box_returned(1));
    let _ = box_into_raw(1);
    std::mem::forget(to_string(1));
    string_forgotten(1);
    std::mem::forget(through_local_callee(1));
    let _ = plain(1);
    std::mem::forget(empty_vec(1));
}

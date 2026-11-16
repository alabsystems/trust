//@ needs-trust-verify
//@ edition: 2021
//@ only-unix
//@ aux-build:symbol_interposition_dep.rs
//@ revisions: malloc_box calloc_vec export_name_free certify dep_import static_import advisory
//@ revisions: ffi_export panic_handler_local
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[malloc_box] check-fail
//@[calloc_vec] check-fail
//@[export_name_free] check-fail
//@[certify] check-fail
//@[dep_import] check-fail
//@[static_import] check-fail
//@[advisory] check-pass
//@[ffi_export] check-pass
//@[panic_handler_local] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
#![cfg_attr(panic_handler_local, no_std)]
//! Trust (2026-09-30): A LOCAL DEFINITION OF A SYMBOL A LINKED CRATE IMPORTS
//! REPLACES THAT CRATE'S CALLEE, AND NO LANE CHECKS THE REPLACEMENT
//! (`compiler/rustc_mir_transform/src/trust_verify/symbol_interposition.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-30 — a local `#[no_mangle]` definition
//! of a symbol std imports (`malloc`) was believed by the std code that calls it").
//!
//! `malloc_box` is the witness: `malloc` is safe code that returns a dangling
//! "allocation"; std's `Global` allocator reaches it through `libc::malloc`, and
//! `f` boxes a value. On main `0.10.0+g07091c92c` it built rc=0 under the default
//! policy (and under `certify` and the advisory survey), and a driver built
//! verify-off against the rlib died of SIGSEGV (exit 139). `calloc_vec`
//! (`vec![0u8; n]` allocates zeroed, through `calloc`) and `export_name_free`
//! (the symbol given by `#[export_name]`) are the same class; `certify` is
//! `malloc_box` under `-Ztrust-policy=certify`. `dep_import` replaces a symbol
//! a verify-off DEPENDENCY imports (`auxiliary/symbol_interposition_dep.rs`).
//! `static_import` is a STATIC under a symbol `libc` imports as a foreign static
//! (`in6addr_any`): the rule is about the symbol, whatever kind of item owns it.
//! Measured on main `0.10.0+g07091c92c` with this file: every check-fail revision
//! built rc=0 except `dep_import`, which main already refused through the
//! fail-closed call into the verify-off dependency; there the new error pins the
//! rule's non-sysroot arm (the importer is the dependency).
//!
//! `advisory` keeps the explicit survey's contract (a warning, rc=0);
//! `ffi_export` is the control that a C-ABI export under a symbol no linked
//! crate imports is untouched (rc=0 on main, and still check-pass).
//!
//! `panic_handler_local` is the control for the one designed import: `core`
//! imports the `panic_impl` weak lang item (`rust_begin_unwind`) for the
//! program's `#[panic_handler]` to define, and that contract is the handler's
//! type-checked signature. The first version of this rule
//! (`0.10.0+g2a7366482`) refused it, so every `#![no_std]` crate with its own
//! handler was refused (`no_std_panic_handler_owner_keeps_core_credit.rs`
//! `#local_handler` went red); the lang-item table now exempts it (rc=0 on main
//! `0.10.0+g07091c92c`, refused by `0.10.0+g2a7366482`, check-pass again).
//!
//! BESIDE MAIN'S GRAPH-WIDE ALLOCATOR CHARGE (2026-10-08). Since 2026-10-03 main
//! charges a crate graph in which any crate defines a libc allocator link name
//! as one with a user allocator
//! (`crate_graph_system_allocator_interposer`; its own pins are
//! `policy_b/system_allocator_symbol_is_a_user_allocator.rs`). Both mechanisms
//! are kept and the allocator revisions draw both: this rule's error on the
//! definition (with a note naming the charge), and main's refused
//! `contract:global-alloc-dealloc-panic-free` row on the allocating body (`f`,
//! `g`). Measured on main `0.10.0+gde6288ddd` with this file: `malloc_box`,
//! `calloc_vec` and `certify` are refused there by that row alone;
//! `export_name_free` (no body of the crate reaches the allocator) and
//! `static_import` (not an allocator name) build rc=0 there, and `dep_import`
//! is refused as before. So on that main this rule alone refuses
//! `export_name_free` and `static_import`.

#[cfg(dep_import)]
extern crate symbol_interposition_dep;

#[cfg(any(malloc_box, certify, advisory))]
#[no_mangle]
pub extern "C" fn malloc(_n: usize) -> *mut u8 {
    //[malloc_box,certify]~^ ERROR Trust verification cannot accept a definition of the symbol `malloc`
    //[malloc_box,certify]~| NOTE this crate graph is also charged as one with a user allocator
    //[advisory]~^^^ WARN Trust verification cannot accept a definition of the symbol `malloc`
    16 as *mut u8
}

#[cfg(any(malloc_box, certify, advisory))]
pub fn f(x: u64) -> u64 {
    //[malloc_box,certify]~^ ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
    let b = Box::new(x);
    *b
}

#[cfg(calloc_vec)]
#[no_mangle]
pub extern "C" fn calloc(_count: usize, _size: usize) -> *mut u8 {
    //[calloc_vec]~^ ERROR Trust verification cannot accept a definition of the symbol `calloc`
    16 as *mut u8
}

#[cfg(calloc_vec)]
pub fn g(n: u8) -> usize {
    //[calloc_vec]~^ ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
    let v = vec![0u8; n as usize + 1];
    v.len()
}

#[cfg(export_name_free)]
#[export_name = "free"]
pub extern "C" fn my_free(_p: *mut u8) {
    //[export_name_free]~^ ERROR Trust verification cannot accept a definition of the symbol `free`
}

#[cfg(dep_import)]
#[no_mangle]
pub extern "C" fn trust_interposition_dep_hook(x: u32) -> u32 {
    //[dep_import]~^ ERROR Trust verification cannot accept a definition of the symbol `trust_interposition_dep_hook`
    x.wrapping_add(1)
}

#[cfg(dep_import)]
pub fn h(x: u32) -> u32 {
    symbol_interposition_dep::call_hook(x)
}

#[cfg(static_import)]
#[no_mangle]
pub static in6addr_any: [u8; 16] = [0; 16];
//[static_import]~^ ERROR Trust verification cannot accept a definition of the symbol `in6addr_any`

#[cfg(static_import)]
pub fn s() -> u8 {
    in6addr_any[0]
}

#[cfg(ffi_export)]
#[no_mangle]
pub extern "C" fn trust_ffi_add_wrapping(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

#[cfg(ffi_export)]
#[export_name = "trust_ffi_is_even"]
pub extern "C" fn is_even(a: u32) -> bool {
    a % 2 == 0
}

// The handler diverges by re-entering itself: a `loop {}` body is refused on its
// own row (its panic-freedom does not lower), which would hide what this
// revision pins.
#[cfg(panic_handler_local)]
#[panic_handler]
#[allow(unconditional_recursion)]
fn on_panic(info: &core::panic::PanicInfo<'_>) -> ! {
    on_panic(info)
}

#[cfg(panic_handler_local)]
pub fn halve(x: u32) -> u32 {
    x / 2
}

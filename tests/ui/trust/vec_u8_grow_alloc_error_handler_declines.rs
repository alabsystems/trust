//@ edition: 2021
//@ needs-trust-verify
//@ revisions: plain handler
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[plain] check-pass
//@[handler] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **The `Vec<u8>` grow summary's oom gate also declines on a user
//! `#[alloc_error_handler]`** (std-call-summaries P2 review, item 4).
//!
//! A `#![no_std]` crate's `#[alloc_error_handler]` replaces the abort route of a
//! failed allocation and may panic, so "allocation failure aborts" is no longer
//! known and `crate_graph_may_install_alloc_error_hook` answers `true` for any crate
//! of the graph but the real `std` that defines one. `plain`: the same crate without
//! the handler proves `grow` under certify. `handler`: the grow row stays
//! runtime-checked (and, as before this change, the global-allocator contract is
//! refused and the handler's `__rust_alloc_error_handler` shim is refused as a
//! symbol definition `alloc` imports).

#![no_std]
#![cfg_attr(handler, feature(alloc_error_handler))]
extern crate alloc;
use alloc::vec::Vec;

#[cfg(handler)]
#[alloc_error_handler]
fn on_oom(_: core::alloc::Layout) -> ! {
    //[handler]~^ ERROR Trust Level 0 safety verification incomplete for `vec_u8_grow_alloc_error_handler_declines::on_oom`
    //[handler]~| ERROR Trust strict verification failed for `vec_u8_grow_alloc_error_handler_declines::on_oom`
    //[handler]~| ERROR Trust Level 0 safety verification incomplete for `vec_u8_grow_alloc_error_handler_declines::_::__rust_alloc_error_handler`
    //[handler]~| ERROR Trust strict verification failed for `vec_u8_grow_alloc_error_handler_declines::_::__rust_alloc_error_handler`
    //[handler]~| ERROR Trust verification cannot accept a definition of the symbol
    panic!("oom")
}

pub fn grow(v: &mut Vec<u8>, s: &[u8]) {
    //[plain]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2
    //[handler]~^^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2
    //[handler]~| ERROR Trust Level 0 safety verification incomplete
    //[handler]~| ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
    //[handler]~| ERROR Trust strict verification failed
    v.extend_from_slice(s)
}

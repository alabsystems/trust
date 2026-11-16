//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency that installs an allocation-error hook, with the same
//! closure rustc's own `tests/ui/panics/alloc_error_hook-unwind.rs` installs in its
//! `main`. Nothing in its public API says so; only its metadata fact
//! (`trust_crate_references_alloc_error_hook`) tells a downstream compilation.
#![feature(alloc_error_hook)]

pub fn install() {
    std::alloc::set_alloc_error_hook(|_| panic!());
}

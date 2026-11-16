//@ needs-trust-verify
//@ needs-asm-support
//@ only-apple
//@ revisions: local dep dep_island
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type bin
//@[dep] aux-build: system_allocator_global_asm_dep.rs
//@[dep_island] aux-build: clean_island_only_dep.rs
//@[local] check-fail
//@[dep] check-fail
//@[dep_island] check-pass
//@ dont-check-compiler-stderr
//@[local] dont-require-annotations: ERROR
//@[dep] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Global assembly that DEFINES a libc allocator symbol std's `System` allocator
//! calls makes its crate a user allocator, as a `#[no_mangle]` definition does
//! (review of 2026-10-03).
//!
//! `tests/ui/trust/policy_b/system_allocator_symbol_is_a_user_allocator.rs` pins the
//! Rust ITEMS that carry such a link name. Assembly needs no item: the `global_asm!`
//! below defines `_malloc` (the Mach-O spelling of C's `malloc`, hence `only-apple`)
//! as a tail branch to a Rust function that forwards unchanged to the platform
//! allocator (the malloc zone API). What is tested is that the definition is SEEN,
//! not what it does.
//!
//! MEASURED on stage 1 of `5da8338798b` (the change that charged Rust items; m3), in
//! probes of this kind: a verify-off dependency whose `global_asm!` defines `_malloc`
//! entirely in assembly over the malloc zone API — `nm` showed the executable's own
//! `_malloc`, the program ran, and `make_box` was credited (`bounds: proved`, no
//! premise row) under the default policy, in a full build and in a check build. Now a
//! `DefKind::GlobalAsm` def that is not a Clean island refuses the allocating
//! functions, naming its crate. With that arm switched off (a mutant), `local` and
//! `dep` of this file fail (no refusal reported); without the island exemption,
//! `dep_island` fails.
//!
//! `dep_island` is the control: a Clean island shares `DefKind::GlobalAsm` and lowers
//! no machine code; a dependency holding one keeps every credit
//! (`trust_def_is_clean_island`, read from the dependency's metadata).
#[cfg(dep_island)]
extern crate clean_island_only_dep;
#[cfg(dep)]
extern crate system_allocator_global_asm_dep;

use std::mem::forget;

/// The same assembly the auxiliary crate holds, in the binary itself.
#[cfg(local)]
mod interposer {
    use std::ffi::c_void;

    // <malloc/malloc.h>
    unsafe extern "C" {
        fn malloc_default_zone() -> *mut c_void;
        fn malloc_zone_malloc(zone: *mut c_void, size: usize) -> *mut c_void;
    }

    extern "C" fn forward_malloc(size: usize) -> *mut c_void {
        unsafe { malloc_zone_malloc(malloc_default_zone(), size) }
    }

    #[cfg(target_arch = "aarch64")]
    std::arch::global_asm!(
        ".globl _malloc",
        ".p2align 2",
        "_malloc:",
        "b {forward}",
        forward = sym forward_malloc,
    );

    #[cfg(target_arch = "x86_64")]
    std::arch::global_asm!(
        ".globl _malloc",
        "_malloc:",
        "jmp {forward}",
        forward = sym forward_malloc,
    );
}

const T: [u8; 2] = [7, 8];

pub fn make_box(i: usize) -> Box<u8> {
    //[local,dep]~^ ERROR holds global assembly (`global_asm!`), which can define a libc allocator symbol
    //[dep_island]~^^ NOTE 0 runtime-checked out of
    Box::new(T[i & 1])
}

pub fn make_string(i: usize) -> String {
    //[local,dep]~^ ERROR holds global assembly (`global_asm!`), which can define a libc allocator symbol
    //[dep_island]~^^ NOTE 0 runtime-checked out of
    String::from(T[i & 1] as char)
}

pub fn plain(i: usize) -> u8 {
    //~^ NOTE 0 runtime-checked out of
    T[i & 1] / 2
}

fn main() {
    forget(make_box(1));
    forget(make_string(1));
    let _ = plain(1);
}

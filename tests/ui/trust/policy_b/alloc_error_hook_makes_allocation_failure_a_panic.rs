//@ needs-trust-verify
//@ revisions: local local_certify dep no_hook drop_only
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type bin
//@[local_certify] compile-flags: -Ztrust-policy=certify
//@[dep] aux-build: alloc_error_hook_dep.rs
//@[drop_only] aux-build: alloc_error_hook_dep.rs
//@[local] check-fail
//@[local_certify] check-fail
//@[dep] check-fail
//@[no_hook] check-fail
//@[drop_only] check-pass
//@ dont-check-compiler-stderr
//@[local] dont-require-annotations: ERROR
//@[local_certify] dont-require-annotations: ERROR
//@[dep] dont-require-annotations: ERROR
//@[no_hook] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! An installed allocation-error hook makes allocation failure a PANIC (2026-10-03).
//!
//! `handle_alloc_error` in a binary that links `std` runs std's `rust_oom`, which calls
//! the hook installed with `std::alloc::set_alloc_error_hook` and aborts only if the
//! hook returns. The hook "may choose to panic", and the unwind is catchable: `main`
//! below opens with the body of rustc's own `tests/ui/panics/alloc_error_hook-unwind.rs`,
//! verbatim (the same hook closure, oversized `vec!` and `catch_unwind`). The
//! global-allocator contract (`contract:global-alloc-dealloc-panic-free`) treated
//! allocation failure as an abort, so in a binary — which chooses its allocator — an
//! allocating function carried no premise row at all.
//!
//! MEASURED on stage 1 of origin/main `57121fb6713` (m3), in probes of this shape: with
//! the hook installed in `main` or by a dependency's `install()`, `make_box` was
//! credited (`bounds: proved`) under the default policy and `certify`, and `huge_box`
//! was credited `no_obligations: proved` under the default policy; at runtime
//! `huge_box` unwound out of the hook into a `catch_unwind`. This file itself, on that
//! stage 1: `local`, `local_certify` and `dep` fail (none of the three refusals below is
//! reported); `no_hook` and `drop_only` pass. Now a crate that names
//! `set_alloc_error_hook` carries the metadata fact
//! `trust_crate_references_alloc_error_hook`, and with that fact anywhere in the graph a
//! body that can reach a FAILING allocation is charged the REFUSED premise.
//!
//! What is pinned, per function:
//!  * `make_box`, `huge_box`: an allocating global-allocator shim is reachable;
//!  * `system_box`: allocates through `System` directly (no global-allocator shim) and
//!    reaches `handle_alloc_error` — the handler entry itself is what the walk stops at;
//!  * `consume`: only FREES (an allocation-owning drop). Freeing cannot fail, so the
//!    hook never runs there: it keeps the vacuous discharge, never the refusal. Pinned by
//!    `drop_only`, which must BUILD with the dependency's hook in the graph (a refusal
//!    is a strict abort);
//!  * `plain`: allocates nothing and keeps its credit.
//! `no_hook` enables the same feature gates but never names `set_alloc_error_hook`:
//! nothing is refused.
#![feature(alloc_error_hook)]
#![feature(allocator_api)]

#[cfg(any(dep, drop_only))]
extern crate alloc_error_hook_dep;

#[cfg(not(drop_only))]
use std::hint::black_box;
#[cfg(not(drop_only))]
use std::mem::{MaybeUninit, forget};
#[cfg(not(drop_only))]
use std::panic::catch_unwind;

const T: [u8; 2] = [7, 8];

#[cfg(not(drop_only))]
pub fn make_box(i: usize) -> Box<u8> {
    //[local,local_certify,dep]~^ ERROR a crate in the graph references `std::alloc::set_alloc_error_hook`
    //[no_hook]~^^ NOTE 0 runtime-checked out of
    Box::new(T[i & 1])
}

#[cfg(not(drop_only))]
pub fn huge_box() -> Box<MaybeUninit<[u8; 1 << 60]>> {
    //[local,local_certify,dep]~^ ERROR a crate in the graph references `std::alloc::set_alloc_error_hook`
    Box::new_uninit()
}

#[cfg(not(drop_only))]
pub fn system_box(i: usize) -> Box<u8, std::alloc::System> {
    //[local,local_certify,dep]~^ ERROR a crate in the graph references `std::alloc::set_alloc_error_hook`
    Box::new_in(T[i & 1], std::alloc::System)
}

/// Drops `v` at the end of its scope: the `Vec`'s drop glue frees through
/// `__rust_dealloc`, and allocates nothing.
pub fn consume(v: Vec<u8>, i: usize) -> u8 {
    //~^ NOTE 0 runtime-checked, 1 skipped out of
    let _keep = v;
    T[i & 1]
}

pub fn plain(i: usize) -> u8 {
    //~^ NOTE 0 runtime-checked out of
    T[i & 1] / 2
}

#[cfg(not(drop_only))]
fn main() {
    #[cfg(any(local, local_certify))]
    std::alloc::set_alloc_error_hook(|_| panic!());
    #[cfg(dep)]
    alloc_error_hook_dep::install();

    let panic = catch_unwind(|| {
        // This is guaranteed to exceed even the size of the address space
        for _ in 0..16 {
            // Truncates to a suitable value for both 32-bit and 64-bit targets.
            let alloc_size = 0x1000_0000_1000_0000u64 as usize;
            forget(black_box(vec![0u8; alloc_size]));
        }
    });
    assert!(panic.is_err());

    forget(make_box(1));
    forget(huge_box());
    forget(system_box(1));
    let _ = consume(Vec::new(), 1);
    let _ = plain(1);
}

/// The dependency that may install the hook is in the graph (`extern crate` above);
/// only the function that frees and the one that allocates nothing are compiled.
#[cfg(drop_only)]
fn main() {
    let _ = consume(Vec::new(), 1);
    let _ = plain(1);
}

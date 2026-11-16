//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, whose ONLY sysroot-shaped anchor is the
//! graph's `#[panic_handler]` — no `#[lang]` attribute, no feature gate, nothing
//! a reviewer would read as impersonation. Every `#![no_std]` binary needs one
//! crate that provides it.
//!
//! `#[panic_handler]` IS the `panic_impl` lang item, and in a graph that never
//! loads `std` its owner is whichever crate declares it: THIS one. So
//! `crate_is_authentic_std` — and through it `crate_is_authentic_foundational`
//! — graded this crate as `std` while they decided identity by lang-item
//! OWNERSHIP alone.
//!
//! It then defines a type at a def path with a `slice` module segment, named
//! `Iter`, whose `Iterator::next` is a bare panic, which `total_std_iterator_ty`
//! matched exactly (`[PF_ZEROGATE] arm=registry`). The caller fixture is
//! `total_std_iterator_panic_handler_foundational_impostor_refuted.rs`.
#![no_std]

#[panic_handler]
fn on_panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

pub mod slice {
    pub struct Iter {
        pub n: u32,
    }

    impl core::iter::Iterator for Iter {
        type Item = u32;
        #[inline(never)]
        fn next(&mut self) -> Option<u32> {
            panic!("impostor slice::Iter::next")
        }
    }
}

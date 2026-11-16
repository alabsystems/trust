//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: user default source panicked
//@ ignore-emscripten no processes
//! The WITNESS for `errsource_devirt_local_core_error.rs` (ERRSOURCE-ANCHOR-1): the
//! `<dyn Error>::source` call that file's BEFORE compiler demoted as the total
//! default of core's `Error` dispatches to this crate's own `core::error::Error`
//! default, which panics.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it pins
//! that the call really panics, not the verdict. Measured 2026-10-05 on the stage 1
//! at `scratchpad/stage1-w14`: this file built `-Ztrust-verify=off` exits 101 with
//! the message above.

pub mod core {
    pub mod error {
        pub trait Error {
            fn source(&self) -> Option<u32> {
                panic!("user default source panicked")
            }
        }
    }
}

pub struct C(pub u8);

impl crate::core::error::Error for C {}

#[inline(never)]
fn go(c: &C) -> Option<u32> {
    let d: &dyn crate::core::error::Error = c;
    d.source()
}

fn main() {
    println!("{:?}", go(std::hint::black_box(&C(7))));
}

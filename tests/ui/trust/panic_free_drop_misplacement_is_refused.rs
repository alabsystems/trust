//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ check-fail
//! Verified-sysroot plan §5 step 6: every placement of
//! `#[trust::panic_free_drop]` other than a trait definition this crate owns
//! is refused, each with its own named reason and fix (D3):
//!
//!   * an impl of a FOREIGN trait — ownership: only the crate that owns a
//!     trait definition can make every downstream impl inherit the obligation,
//!     because the declaration must ride the trait's own metadata;
//!   * an impl of a LOCAL trait — an implementation-site opt-in cannot support
//!     reliance (the call site would have to enumerate every impl to know they
//!     all opted in); the fix is to move it to the definition;
//!   * a trait METHOD — the contract governs the drop glue of a `dyn Trait`
//!     object, not a method; per-method panic-freedom is `#[trust::panic_free]`;
//!   * a free function — same reason, nothing dispatches.
//!
//! Refusing loudly matters: an annotation that silently did nothing would read
//! to its author exactly like one that was being enforced.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

use std::fmt;

pub struct Wrapper(u32);

#[trust::panic_free_drop]
impl fmt::Display for Wrapper {
    //~^ ERROR must be declared on a trait DEFINITION
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

pub trait Local {
    fn go(&self) -> u32;
}

#[trust::panic_free_drop]
impl Local for Wrapper {
    //~^ ERROR must be declared on a trait DEFINITION
    fn go(&self) -> u32 {
        self.0 / 4
    }
}

pub trait Own {
    #[trust::panic_free_drop]
    fn m(&self) -> u32;
    //~^ ERROR must be declared on a trait definition
}

#[trust::panic_free_drop]
pub fn free_function(x: u32) -> u32 {
    //~^ ERROR must be declared on a trait definition
    x / 4
}

fn main() {
    let w = Wrapper(8);
    let _ = w.go();
    let _ = free_function(9);
}

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of `foundational_member_qualified_path.rs`.
//!
//! A user type implementing a core trait is spelled exactly like core's own
//! impl of that trait — `<SELF as core::ops::Add>::add`. The tolerance that
//! accepts the core one rests entirely on the body being core's: Trust does not
//! verify core, and core's internal runtime checks are retained as vanilla Rust.
//! Neither claim reaches a body the user wrote, which may `panic!` for reasons
//! of its own.
//!
//! So the recogniser requires BOTH halves to be foundational, and this file pins
//! that the user half is still refused. An addition that can overflow stays a
//! build error rather than being waved through on the strength of the trait's
//! name.

pub struct W(pub u8);

impl core::ops::Add for W {
    type Output = W;
    fn add(self, other: W) -> W {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
        W(self.0 + other.0)
    }
}

pub fn add_them(a: W, b: W) -> u8 {
    (a + b).0
}

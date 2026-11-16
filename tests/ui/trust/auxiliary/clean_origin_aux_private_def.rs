//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off

//! **The Lean `private def` aux (Trust, 2026-09-28).**
//!
//! `pub mod api` is PUBLIC, and its island declares one ordinary `def` and one
//! `private def`. The consumer is `clean_origin_cross_crate_private_def.rs`.
//! Inside this crate, a `private def` is callable from Rust and from another
//! module's island, because Clean gives it that reach. Both are exercised here.

#![crate_type = "rlib"]

pub mod api {
    clean {
        private def secret (a : UInt64) : UInt64 := a * 2
        def open_ (a : UInt64) : UInt64 := secret a
    }
}

clean {
    def other (a : UInt64) : UInt64 := secret a
}

pub fn via_owner(a: u64) -> u64 {
    api::secret(a) + other(a)
}

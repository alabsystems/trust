//@ needs-trust-verify
//@ aux-build:clean_origin_aux_private_def.rs
//@ compile-flags: -Z trust-verify=off

//! **A Lean `private def` is not callable from another crate (Trust, 2026-09-28).**
//!
//! The design of record (spec surface §4.1.1) has the CALL capability obey the
//! declaring language's own visibility: "Rust privacy regions; Clean
//! `private`/`protected`". The mint planted EVERY island declaration at `pub`,
//! so a `private def` in a public module was callable from a downstream crate.
//! Measured on stage 1: `privlib::api::secret(21)` built and printed `42`.
//!
//! A `private def` is now planted at `pub(crate)`. That is the reach Clean gives
//! it: any island in the owning crate may call it (the aux does, from another
//! module), so the Rust spelling and the Clean spelling still name the same
//! entity everywhere in the owning crate. The refusal is the one ordinary Rust
//! gives a `pub(crate)` item. The ordinary `def` beside it stays public.

extern crate clean_origin_aux_private_def;

fn main() {
    let _ = clean_origin_aux_private_def::api::open_(1);
    let _ = clean_origin_aux_private_def::via_owner(1);
    let _ = clean_origin_aux_private_def::api::secret(21);
    //~^ ERROR function `secret` is private
}

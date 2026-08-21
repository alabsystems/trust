//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//! **I5 CONTROL 1 (c) — THE PARITY FIXTURE, NON-COLLISION CONTROL.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! The acceptance criterion this half owns:
//!
//! > a different-module one must not [collide]
//!
//! THIS IS THE CONTROL ON `clean_origin_parity_collision.rs`, AND IT IS THE
//! REASON THAT ONE IS NOT SUFFICIENT ALONE. A trivially "correct" way to make a
//! same-module Rust `fn f` collide with a Clean `def f` is to plant island names
//! too broadly — into the crate root, into every module, or into a namespace
//! they do not belong in. That would produce the required `E0428` while being
//! badly wrong, and this fixture is what catches it: `other::f` is a different
//! module and must remain perfectly legal.
//!
//! ============================================================================
//! THIS FIXTURE IS GREEN TODAY, BUT **VACUOUSLY** — AND THAT IS RECORDED HERE
//! SO NOBODY LATER MISTAKES IT FOR EVIDENCE.
//!
//! It passes because the island declares no names at all, so of course nothing
//! collides with anything. It becomes a real control the moment I5 mints
//! children, and it must STAY green through that change. Its value is entirely
//! in the future: it constrains where the minted names may be planted.
//!
//! Do not "strengthen" it by moving `other` inside `m` — that converts it into a
//! second copy of the collision half and destroys the only thing it measures.
//! ============================================================================

mod m {
    clean {
        def f (a : UInt64) : UInt64 := a
    }
}

mod other {
    // Different module: MUST NOT collide, before or after I5.
    pub fn f(a: u64) -> u64 { a }
}

fn main() {
    let _ = other::f(1);
}

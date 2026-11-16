//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// Upstream 1.101: `box` patterns were removed; `deref_patterns` is the
// replacement spelling for binding through a `Box`.
#![feature(deref_patterns)]
//! Trust (wave-UPB): an enum payload binding that is PROVABLY UNREAD is
//! SKIPPED, not read. Both arms are pure skips — no bind pushed, no
//! instruction emitted, no pointer minted, no bytes read — so every attack
//! that needs an address to get wrong or a value to lose has nothing to act on.
//!
//! The deadness certificate is a linear scan of the WHOLE expression arena for
//! the two node kinds that can carry a `LocalVarId` USE. That is exhaustive
//! over the node set rather than a deny-list over use FORMS: rustc's THIR has
//! exactly three carriers, and the third is the definition. Closure captures
//! are therefore covered — a captured upvar is a `VarRef` in the PARENT arena.
//!
//! `live_bind_still_read` is the fence: the same shapes with the variable
//! actually READ must keep binding it, which `run-pass` checks by value.

pub enum E {
    V(Box<u32>),
    W(u32),
}

/// Dead `box` bindings in every spelling, plus a dead `ref mut`.
pub fn dead_binds(e: &mut E) -> u32 {
    match e {
        E::V(deref!(_)) => 1,
        E::W(ref mut _q) => 2,
    }
}

/// The fence: the identical shape with the binding READ must still bind it.
pub fn live_bind_still_read(e: E) -> u32 {
    match e {
        E::V(deref!(b)) => b + 10,
        E::W(w) => w + 20,
    }
}

fn main() {
    let mut a = E::V(Box::new(3));
    let mut b = E::W(4);
    assert_eq!(dead_binds(&mut a), 1);
    assert_eq!(dead_binds(&mut b), 2);
    assert_eq!(live_bind_still_read(E::V(Box::new(3))), 13);
    assert_eq!(live_bind_still_read(E::W(4)), 24);
}

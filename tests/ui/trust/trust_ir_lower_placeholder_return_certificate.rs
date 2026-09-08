//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-PRC): the wave-DRC divergence certificate sharpens from "zero
//! `Inst::Return`" to "zero CONTRADICTING `Inst::Return`" — a Return of the
//! producer's own minted information-free placeholder (`Const { Unit,
//! PhantomData }` as the value's defining instruction) is well-typed against
//! the signed `returns: [Unit]` and contradicts nothing. The
//! derive(Clone)-on-Copy `*self` bodies over register_enum-declined enums are
//! the population; a Return whose value comes from a CALL (the pinned
//! transmute attack) keeps the refusal verbatim.

#[derive(Clone, Copy)]
pub enum Void {}

#[derive(Clone, Copy)]
pub enum Never {}

/// An inhabited pass-through over a fn-ptr-payload enum (register-declined):
/// the placeholder-return shape with a value that actually flows at runtime.
#[derive(Clone, Copy)]
pub enum It {
    F(fn() -> u32),
}

fn forty() -> u32 {
    40
}

pub fn pass(r: &It) -> It {
    *r
}

fn main() {
    let x = It::F(forty);
    let y = pass(&x).clone();
    let It::F(g) = y;
    assert_eq!(g(), 40);
}

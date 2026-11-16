//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-require-annotations: NOTE
//! **THE CLOSE NEGATIVE TWIN of `clean_origin_bitvec_widths.rs`: a `BitVec`
//! whose width is not a literal is still refused, and refused BY NAME.**
//!
//! Widening `recognize` to accept the elaborator's numeral wrapper
//! `@OfNat.ofNat Nat n (instOfNatNat n)` is one shape's worth of new
//! acceptance, and the failure mode it could have had is not "too few types
//! carry" — it is a width read off a term that does not denote one. A carrier
//! decision that produces a value is a WRONG BINARY when it is wrong, so the
//! twin matters more than the positive.
//!
//! Both defs below are `BitVec <something that is not a literal>`:
//!
//! * `bvdef` is the sharp one. `w` is a `def` whose value IS `64`, so the type
//!   is DEFINITIONALLY `BitVec 64` and the kernel is perfectly happy with it.
//!   It is refused anyway, and that is the carrier map's stated contract:
//!   matching is syntactic and shallow, it does not reduce, it does not unfold.
//!   Reduction is what turns `UInt64.ofNat (2^64)` into `0`; a carrier map that
//!   reduces is one that can be argued into the wrong answer by a clever
//!   definition.
//! * `bvexpr` is the ordinary one: an arithmetic width.
//!
//! Neither is an `OfNat`-headed term, so each also pins that the new arm did
//! not widen into "anything applied to `BitVec`".
//!
//! The refusal must NAME the type (`BitVec ..`) and carry options (ruling
//! v7/D3) — an `E0425` that only says "not found" is a lie by omission about a
//! declaration the user can see three lines up.
//!
//! And it must be a DIFFERENT refusal from the one a literal width now gets.
//! `clean_origin_bitvec_widths.rs` pins that `BitVec 64` reaches
//! `carries TOTALLY`; this file pins that `BitVec w` still reaches
//! `no Rust carrier is modeled`. Before the fix both said the second thing,
//! which is exactly why the compiler was telling users to write a spelling it
//! then refused.

mod m {
    clean {
        def w : Nat := 64
        def bvdef  (x : BitVec w)         : BitVec w         := x
        def bvexpr (x : BitVec (32 + 32)) : BitVec (32 + 32) := x
    }
}

fn use_bvdef(x: u64) -> u64 {
    crate::m::bvdef(x)
    //~^ ERROR cannot find function `bvdef` in module `crate::m`
    //~| NOTE no Rust carrier is modeled for the Clean type `BitVec ..`
}

fn use_bvexpr(x: u64) -> u64 {
    crate::m::bvexpr(x)
    //~^ ERROR cannot find function `bvexpr` in module `crate::m`
    //~| NOTE no Rust carrier is modeled for the Clean type `BitVec ..`
}

fn main() {
    let _ = use_bvdef(1);
    let _ = use_bvexpr(1);
}

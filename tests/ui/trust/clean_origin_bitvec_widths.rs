//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-require-annotations: NOTE
//! **`BitVec 8/16/32/64` NOW CARRIES — and the refusal in front of it now says
//! the true thing.**
//!
//! # What was broken
//!
//! `BitVec 8/16/32/64` has been in the carrier map since I4, and the carrier's
//! own refusal text offers it by name as one of "the modeled value types". It
//! was nevertheless unreachable from an island: `recognize` accepted the width
//! only as a bare `Lit(Nat)`, and the elaborator never records one — an
//! authored `BitVec 64` is stored as `@OfNat.ofNat Nat 64 (instOfNatNat 64)`.
//! So every island-authored `BitVec` signature refused with
//! `UnmodeledCleanType { rendered: "BitVec .." }`, and the `E0425` note told
//! the user to use a spelling the compiler then refused. Measured over the
//! whole in-tree island corpus before the fix, that one shape was 6 of the 10
//! `NoTotalCarrier` refusals, and after it the corpus has none.
//!
//! # What these declarations do NOW, and why this file is not `run-pass`
//!
//! The carrier is granted — exactly, at `u8`/`u16`/`u32`/`u64`, per position,
//! which `crates/trust-clean-origin/tests/control_22_bitvec_elaborated_width.rs`
//! pins against the real elaborator. Calling one from Rust is a SECOND
//! capability and it is still absent, for a reason that has nothing to do with
//! the carrier: the faithfulness gate reflects the EMITTED MIR back into Clean
//! using only that body's own local types — deliberately, so an emitter that
//! typed a local wrongly is caught — and the Clean domain it reads off `u64` is
//! `UInt64`. `UInt64` is a STRUCTURE whose single field is a `BitVec 64`, not
//! the `BitVec 64` itself, so the reflected term is not definitionally equal to
//! a `BitVec`-typed declaration and the gate refuses.
//!
//! That refusal is raised on SIDE A (`plan_clean_origin_body`), which is what
//! this fixture measures. Without it the mint grants a `DefId`, the program
//! resolves and typechecks, and the build then dies at code generation with
//! `error: internal: refusing to emit code for Clean declaration `bv64``
//! — measured on this tree. Raising it at the mint turns that into the
//! call-site diagnostic below, which is the whole point of the mint's fourth
//! condition.
//!
//! # What each line here distinguishes
//!
//! The note must say `carries TOTALLY` — i.e. it must NOT be the
//! "no Rust carrier is modeled for the Clean type `BitVec ..`" note, which is
//! what every one of these produced before the fix and which is still the right
//! note for a width that is not a literal (`clean_origin_bitvec_nonliteral_width.rs`,
//! the close negative twin). Two different refusals for two different reasons
//! is the measurement; one refusal for both was the defect.
//!
//! `bvmix` is here because its two arguments carry at DIFFERENT widths, so a
//! reader that decided one width for a whole signature would not reach this
//! refusal by the same route.
//!
//! # The return direction is an OPEN OWNER DECISION, not a TODO
//!
//! What would make these `run-pass` is written up, with four costed options and
//! a recommendation, in `docs/design/2026-09-14-bitvec-return-direction.md`.
//! The short version: the reflection picks its Clean domain from the EMITTED
//! local's Rust type alone — pinned by
//! `trust-clean-origin/tests/table_controls.rs::h_i_the_reflector_never_sees_the_plan`
//! and rested on by `docs/TCB.md` as the double fault — so nothing may tell it
//! that a `u64` here stands for `BitVec 64` rather than `UInt64`. Every route
//! past that either retires the double fault, changes what `BitVec n` carries,
//! or changes what `Faithful` means. None of them is a widening.
//!
//! The note text below is pinned BYTE-FOR-BYTE against the renderer by
//! `trust-clean-origin/tests/control_25_refusal_note_fixture_parity.rs`, which
//! runs in the fast `crates/` lane — no pre-push lane runs this `ui` suite, so
//! that control is what keeps this file from going stale invisibly.

mod m {
    clean {
        def bv8  (x : BitVec 8)  : BitVec 8  := x
        def bv16 (x : BitVec 16) : BitVec 16 := x
        def bv32 (x : BitVec 32) : BitVec 32 := x
        def bv64 (x : BitVec 64) : BitVec 64 := x
        def bvmix (a : BitVec 64) (b : BitVec 8) : BitVec 8 := b
    }
}

fn main() {
    let _ = crate::m::bv8(1u8);
    //~^ ERROR cannot find function `bv8` in module `crate::m`
    //~| NOTE carries TOTALLY
    let _ = crate::m::bv16(1u16);
    //~^ ERROR cannot find function `bv16` in module `crate::m`
    //~| NOTE carries TOTALLY
    let _ = crate::m::bv32(1u32);
    //~^ ERROR cannot find function `bv32` in module `crate::m`
    //~| NOTE carries TOTALLY
    let _ = crate::m::bv64(1u64);
    //~^ ERROR cannot find function `bv64` in module `crate::m`
    //~| NOTE carries TOTALLY
    let _ = crate::m::bvmix(1u64, 2u8);
    //~^ ERROR cannot find function `bvmix` in module `crate::m`
    //~| NOTE carries TOTALLY
}

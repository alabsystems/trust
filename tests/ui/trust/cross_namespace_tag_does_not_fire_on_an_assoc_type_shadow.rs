//@ ignore-test (RED ON PURPOSE — pins the spelling the seam OUGHT to produce; see below)
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The second lost-recovery direction of the cross-namespace tag
//! (`cross_namespace_tag_does_not_fire_on_a_macro_shadow.rs` pins the first,
//! `cross_namespace_key_alias_stays_closed.rs` pins the direction the tag exists
//! for). `trait T { type A; fn A(..); }` is legal, idiomatic Rust with NO
//! ambiguity in the def-path identity space: an associated TYPE never reaches
//! `trust_mir_extract`'s rendering seam in any probe run so far, so the method's
//! path should be spelled exactly as it would be with the associated type named
//! anything else.
//!
//! It is not. The associated type and the method are siblings under the SAME
//! parent — the `impl` — so `def_path_data_namespace` files them as a `t`/`v`
//! pair, the pair enters the collision index, and the METHOD (the non-`TypeNs`
//! half) is tagged. MEASURED, both states, on the stage2 `trustc` built from
//! `ddb545d35b`, one identifier apart (the second state is this file with the
//! associated type renamed `B`), with this file's own crate name:
//!
//! ```text
//! type A + fn A:  <…_assoc_type_shadow::X as …_assoc_type_shadow::T>::A#ns1v
//! type B + fn A:  <…_assoc_type_shadow::X as …_assoc_type_shadow::T>::A
//! ```
//!
//! It is not free. The method is EXPORTED, so the move drops it into the
//! crate-boundary asymmetry recorded as §RESIDUAL 7a on
//! `trust_mir_extract::apply_cross_namespace_tag`: MEASURED with a two-crate
//! probe, compiling the defining crate renders
//! `<assocdep::X as assocdep::T>::A#ns1v` while compiling a consumer that calls
//! it renders the SAME `DefId` as `<assocdep::X as assocdep::T>::A`. One
//! `DefId`, two keys, and nothing in the source was ever ambiguous.
//!
//! WHY IGNORED, and what un-ignores it. Unlike the macro-shadow file next to it,
//! this one is NOT waiting on a compiled narrowing — the narrowing has not been
//! WRITTEN, deliberately. Dropping `DefKind::AssocTy` from
//! `local_cross_namespace_collisions` is a two-line change, but it needs a
//! premise nobody has established: that no associated type ever reaches
//! `safe_def_path_str`/`safe_def_path_str_with_args`. `MacroNs` and
//! `DefKind::ExternCrate` had that premise structurally, and measurably — a
//! `macro_rules!` is not a type and has no body, and with `extern crate alloc as
//! A;` the seam was watched rendering `alloc::vec::Vec`, never `A::vec::Vec`, so
//! both are now out of the index. An associated
//! type IS a type, the argument does not transfer, and one probe in which rustc
//! normalized `P::Assoc` away is not evidence about ~100 call sites, several of
//! which take their `DefId` from an attribute or allocation scan. Removing the
//! index entry on that evidence would trade a lost recovery for a fail-OPEN
//! alias (both halves rendering `<X as T>::A`), which is the wrong direction to
//! get wrong. So the over-decline is RECORDED — on `def_path_data_namespace` —
//! and this file states the spelling that would settle it.
//!
//! Delete the `ignore-test` lines in the same commit that drops `AssocTy` from
//! the index, and not before. If it is red after that commit, the narrowing did
//! not take.
//!
//! DO NOT READ THAT COMMIT AS CLOSING THE CLASS. `DefKind::TyAlias` sits in the
//! same `DefPathData::TypeNs` arm and is still in the index — measured,
//! `pub type S = u32; pub fn S(v: S) -> S` renders `k::S#ns0v` against the
//! one-identifier control `pub type Q = u32;` -> `k::S` — and it is left standing
//! for exactly this file's reason: a type alias IS a type. `ExternCrate`,
//! `TyAlias` and `AssocTy` are the three names that were PROBED, not an
//! enumeration of that arm.
#![no_std]
#![allow(dead_code, non_snake_case)]

pub trait T {
    type A;
    fn A(v: u32) -> u32;
}

pub struct X;

impl T for X {
    type A = u32;
    fn A(v: u32) -> u32 {
        //~^ ERROR incomplete for `<cross_namespace_tag_does_not_fire_on_an_assoc_type_shadow::X as cross_namespace_tag_does_not_fire_on_an_assoc_type_shadow::T>::A`:
        v + 1
    }
}

//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An ORDINARY dependency crate, compiled exactly the way `targo` compiles every
//! dependency unit: `-Ztrust-verify=off`, so NOTHING in this file is verified and
//! the compiler says so (`compiled WITHOUT Trust verification — 0 obligations
//! checked`).
//!
//! Its only unusual property is that its author WROTE `#[automatically_derived]`
//! by hand. That is not a privileged spelling: it is a **stable, ungated,
//! user-writable** attribute (`rustc_feature/src/builtin_attrs.rs`, "Stable
//! attributes") that is encoded cross-crate
//! (`rustc_hir/src/attrs/encode_cross_crate.rs`). Any crates.io author may write
//! it on any impl, and rustc accepts it silently — no lint, no warning.
//!
//! The four shapes below are the discriminating matrix for what WAS
//! `trust_verify::callee_is_automatically_derived_method`, whose whole predicate
//! was `def_kind == AssocFn && parent is Impl && tcx.is_automatically_derived(impl)`.
//! **That helper was DELETED on 2026-08-27** and cross-crate admission on this
//! lane is now `resolved_def_id.as_local().is_none() { continue; }` — so the
//! answer column is uniform, and the matrix's job is now to prove the gate is
//! blind to the attribute rather than keyed on it:
//!
//! | item        | attribute      | `#[inline]` | impl kind | admitted BEFORE | admitted NOW |
//! |-------------|----------------|-------------|-----------|-----------------|--------------|
//! | `Marked`    | hand-written   | yes         | trait     | **yes — the bug** | no |
//! | `Inherent`  | hand-written   | yes         | inherent  | **yes — the bug**, and no `derive` can ever emit this shape | no |
//! | `Plain`     | none           | yes         | trait     | no (the baseline that already refused) | no |
//! | `Real`      | genuine derive | n/a         | trait     | yes | no — the DISCLOSED COST, see arm 2 |
//!
//! `Real` is retained deliberately. It is no longer a "must keep working" case;
//! it is the measurable price of containment, and deleting it would delete the
//! evidence of what was given up.
//!
//! `Marked` and `Plain` differ by exactly one token. `Inherent` is the shape that
//! proves the predicate is not testing what its name says: `#[derive(..)]`
//! expands to `impl Trait for T`, never to an inherent `impl T`, so an
//! `#[automatically_derived]` inherent impl cannot have been produced by any
//! derive macro that has ever existed.
//!
//! Every `get` below indexes an unchecked caller-supplied index into a
//! caller-supplied slice. Each one panics for `i >= xs.len()`; none of them has
//! been verified by anything.
#![crate_name = "user_ad_dep"]
#![allow(dead_code)]

pub trait Idx {
    fn get(xs: &[u32], i: usize) -> u32;
}

/// ARM 1a — hand-written `#[automatically_derived]` on a TRAIT impl.
pub struct Marked;

#[automatically_derived]
impl Idx for Marked {
    // `#[inline]` is what makes the MIR cross-crate available; it is ordinary,
    // ubiquitous, and carries no proof meaning whatever.
    #[inline]
    fn get(xs: &[u32], i: usize) -> u32 {
        xs[i]
    }
}

/// ARM 1b — hand-written `#[automatically_derived]` on an INHERENT impl.
/// No `#[derive]` macro can produce an inherent impl, so nothing about this item
/// is "compiler-generated" under any reading.
pub struct Inherent;

#[automatically_derived]
impl Inherent {
    #[inline]
    pub fn get(xs: &[u32], i: usize) -> u32 {
        xs[i]
    }
}

/// ARM 3 — byte-identical to `Marked` but for the missing attribute. This is the
/// control that shows the attribute is the whole difference.
pub struct Plain;

impl Idx for Plain {
    #[inline]
    fn get(xs: &[u32], i: usize) -> u32 {
        xs[i]
    }
}

/// ARM 2 — a GENUINE derive. `#[automatically_derived]` here was emitted by the
/// expansion, not typed by a human, and the bodies really are compiler-generated.
/// Bundling these is the completeness the admission exists to buy, and it must
/// survive any narrowing of the gate.
#[derive(Clone, Copy, PartialEq, Default)]
pub struct Real(pub u32);

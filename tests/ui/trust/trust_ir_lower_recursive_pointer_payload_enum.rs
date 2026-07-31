//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (plan 2026-07-29 T1): a RECURSIVE POINTER-PAYLOAD enum — the
//! clean-kernel `Level` shape (first-party/clean
//! crates/clean-kernel/src/level/mod.rs), the binding constraint of the
//! measured clean-kernel census (64,067 `Ty(enum-def)` rejects on the
//! 2026-07-13 seed vintage; `Level`, `ExprKind`, `TypeError` all
//! unregistrable there).
//!
//! The registration wall the plan cites fell on 2026-07-26, AFTER that census
//! was measured: #174 (03bb3862c4) admits sized struct payloads and wave-EP
//! (45a42806bf) thin-pointer payloads. What makes the RECURSIVE shape admit
//! is that the type-level walk never cycles: `Level`'s recursive edges ride
//! `LevelArc(Option<Arc<Level>>)`, and `map_ty` bottoms out at `NonNull`'s
//! raw pointer (the RawPtr arm does not recurse into pointees), so
//! `Arc<Level>` registers as a struct whose deep field is `Ty::Ptr` and the
//! `adt_visit_stack` guard never fires — a by-value ADT cycle is already
//! impossible in Rust (infinite size), so every legal recursive enum routes
//! through indirection the walk terminates at.
//!
//! check-pass pins exactly that TERMINATION property (the hazard class the
//! `enum_declined` negative cache exists for — tests/ui/enum/issue-42747.rs
//! once hung the compiler). Registration/lowering CONTENT for this shape is
//! pinned at crate level (differential.rs `level_shape_*` tests over the
//! exact def DAG); the end-to-end census step-change is measured by the next
//! trustc stage rebuild, not by this fixture.

use std::sync::Arc;

pub struct LevelArc(Option<Arc<Level>>);

// clean-kernel's LevelArc carries a manual stack-safe Drop; keep the shape.
impl Drop for LevelArc {
    fn drop(&mut self) {
        let _ = self.0.take();
    }
}

pub struct Name {
    pub inner: NameInner,
    pub cached_hash: u64,
}

// The nested recursive enum behind `Level::Param` — `Arc<Name>` recursive
// edges plus an `Arc<str>` (a fat NonNull lane the producer currently spells
// thin; values over it stay fail-closed — see `register_enum`'s doc).
pub enum NameInner {
    Anon,
    Str(Arc<Name>, Arc<str>),
    Num(Arc<Name>, u64),
}

pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

impl Level {
    // The SHAPE of the crystal's target body (plan §3 A0): a &self match
    // over the recursive enum (the real `Level::is_zero` recurses through
    // Deref; A0 probes the real crate). Its residual after registration is
    // the T2 shared-ref Load comparison, not a registration reject.
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.0.is_none() && l2.0.is_none(),
            Level::IMax(_, l2) => l2.0.is_none(),
        }
    }
}

// A DIRECT Box<Self> recursive edge — the `ExprKind`/`TypeError` class the
// census names alongside `Level`.
pub enum Tree {
    Leaf(i64),
    Node(Box<Tree>, Box<Tree>),
}

pub fn depth_hint(t: &Tree) -> i64 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::Node(_, _) => -1,
    }
}

// Construction over the recursive shape (the seed path materializes
// variant 0 — `Level::Zero` — and `InsertField` overwrites the rest).
pub fn zero() -> Level {
    Level::Zero
}

pub fn succ_of_zero() -> Level {
    Level::Succ(LevelArc(Some(Arc::new(Level::Zero))))
}

fn main() {}

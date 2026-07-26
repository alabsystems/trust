// trust-types/formula/sort: SMT sorts for formula variables
//
// `Sort` now lives in `trust-ir-contract`; re-exported here so
// `trust_types::Sort` / `formula::Sort` are unchanged. `Sort::from_ty(&Ty)`
// couples Sort to the Trust MIR `Ty` (which stays in trust-types), so it can no
// longer be an inherent method on the (now foreign) `Sort`. It is provided as
// the `SortFromTy` extension trait, which preserves the exact `Sort::from_ty(ty)`
// call spelling at every existing call site once the trait is in scope.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub use trust_ir_contract::{RoundingMode, Sort};

use crate::model::Ty;

/// Extension trait providing `Sort::from_ty(&Ty)` — the Ty->Sort lowering that
/// keeps `Sort` decoupled from the Trust MIR `Ty`. Bring into scope (`use
/// trust_types::SortFromTy;`) to call `Sort::from_ty(ty)`.
pub trait SortFromTy {
    /// Convert a trust-types Ty to an SMT sort.
    fn from_ty(ty: &Ty) -> Sort;
}

impl SortFromTy for Sort {
    fn from_ty(ty: &Ty) -> Self {
        match ty {
            Ty::Bool => Sort::Bool,
            Ty::Int { width, .. } => Sort::BitVec(*width),
            Ty::Float { width } => Sort::BitVec(*width),
            // Raw pointers map to Sort::Int (same as Ref, pointers are
            // mathematical integers at the SMT level).
            Ty::RawPtr { .. } => Sort::Int,
            // Lever A: a recursive ADT lowers to a real SMT datatype sort instead
            // of the opaque `Sort::Int` fallback (the bug this fixes — that
            // opacity is exactly why every projection/match through `Expr`/`Level`/
            // `Name` went Unknown). The datatype's constructor/field structure is
            // built by `datatype_sort_from_ty`, which cuts recursion by name.
            Ty::Datatype { .. } => datatype_sort_from_ty(ty),
            _ => Sort::Int, // fallback for non-scalar values that are not SMT-modeled directly
        }
    }
}

/// Build a `Sort::Datatype` (full constructor/field structure) from a
/// `Ty::Datatype`. Recursion through datatype fields is cut BY NAME: a field
/// whose type is itself a datatype becomes a by-name `Sort::Datatype { name,
/// constructors: vec![] }` reference, so the resulting `Sort` is FINITE even for
/// a self-recursive type (`Expr` with an `Expr` field). The definitional
/// occurrence (the top-level call) carries the full constructor list.
///
/// SOUNDNESS: this is a pure structural transcription of the already-lowered
/// type — it introduces no facts. Field sorts use the normal `Sort::from_ty`
/// mapping so a scalar field keeps its exact bitvector/Int/Bool sort; only the
/// datatype back-edges are abstracted to by-name references (the standard,
/// natively-recursive SMT-LIB datatype encoding).
fn datatype_sort_from_ty(ty: &Ty) -> Sort {
    let Ty::Datatype { name, variants } = ty else {
        return Sort::Int;
    };
    // A by-name reference (no variants) stays a by-name reference.
    if variants.is_empty() {
        return Sort::Datatype { name: name.clone(), constructors: Vec::new() };
    }
    let constructors = variants
        .iter()
        .map(|(ctor, fields)| {
            let field_sorts = fields
                .iter()
                .map(|(fname, fty)| {
                    let fsort = match fty {
                        // Cut the recursion: a nested datatype field becomes a
                        // by-name reference (empty constructors), never an
                        // infinitely-expanded definition.
                        Ty::Datatype { name: ref_name, .. } => {
                            Sort::Datatype { name: ref_name.clone(), constructors: Vec::new() }
                        }
                        other => Sort::from_ty(other),
                    };
                    (fname.clone(), fsort)
                })
                .collect();
            (ctor.clone(), field_sorts)
        })
        .collect();
    Sort::Datatype { name: name.clone(), constructors }
}

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

use crate::model::{DatatypeDefs, Ty, datatype_marker_definition};

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
    datatype_sort_from_ty_with_defs(ty, &DatatypeDefs::new())
}

/// [`Sort::from_ty`], additively widened by an explicit datatype table (R0).
///
/// Same lowering as `Sort::from_ty` on every input it already handled; the ONLY
/// difference is that a bare `Ty::Datatype { variants: [] }` marker the table
/// explicitly defines now lowers to the FULL constructor list instead of an
/// empty by-name reference.
///
/// This is what keeps `(declare-datatype …)` being emitted under
/// markers-everywhere. The downstream declaration collectors
/// (`trust-ir-contract`'s `collect_datatype_decls`, and the in-process ay lane
/// in [`crate::ay_bridge`]) both read "empty constructors" as "this reference
/// carries no definition" and skip it — while `declare-fun` still references the
/// sort by name. With no root definition left to carry the structure, the sort
/// would be referenced but never declared. Resolving through the table restores
/// the definitional occurrence.
///
/// SOUNDNESS is unchanged from the by-name case: declaring a datatype sort
/// asserts NO fact, and a fresh datatype-sorted constant is unconstrained (SAT),
/// so a richer declaration can only let an obligation report its honest outcome.
#[must_use]
pub fn sort_from_ty_with_defs(ty: &Ty, defs: &DatatypeDefs) -> Sort {
    match ty {
        Ty::Datatype { .. } => datatype_sort_from_ty_with_defs(ty, defs),
        other => Sort::from_ty(other),
    }
}

fn datatype_sort_from_ty_with_defs(ty: &Ty, defs: &DatatypeDefs) -> Sort {
    let Ty::Datatype { name, variants } = ty else {
        return Sort::Int;
    };
    // Additive order: an INLINE definition is used as-is. Only a bare by-name
    // reference consults the table, and only under its own name — never a search
    // for a same-name definitional occurrence elsewhere.
    if variants.is_empty() {
        // R0 (WIDENED CARRIER). A marker's sort is THE SORT OF THE TYPE IT
        // NAMES — computed by lowering the recorded definition itself, which is
        // the only rule that keeps a marker and the definition it stands for
        // agreeing:
        //
        //   * a `Ty::Datatype` definition (the Lever A `Level`/`Expr`/`ExprKind`
        //     cluster) lowers to the FULL constructor list, byte-identical to
        //     what its inline spelling produced. This is what keeps
        //     `(declare-datatype …)` being emitted under markers-everywhere:
        //     both `trust_ir_contract::collect_datatype_decls` and the
        //     in-process ay lane read "empty constructors" as "this reference
        //     carries no definition" and skip it, while `declare-fun` still
        //     names the sort.
        //   * a `Ty::Adt` definition — which is what a canonical cut point
        //     almost always is — lowers through the ORDINARY `Sort::from_ty`
        //     path, i.e. `Sort::Int`, EXACTLY as the inline `Ty::Adt` occurrence
        //     at the pre-flip walk root did. It must not become a
        //     `Sort::Datatype`: a flattened `Ty::Adt` enum's fields are read as
        //     `Select(base, Int(k))` all through vcgen, and giving the base a
        //     datatype sort would make every one of those reads ill-sorted.
        //
        // Not a pure decline→answer widening for the ADT case (the pre-table
        // answer was the undeclared by-name `Sort::Datatype { constructors: [] }`),
        // and deliberately so — the by-name spelling names a sort no
        // `declare-datatype` ever emits. It cannot change any audited answer:
        // no shipped body carries a non-empty table.
        return match datatype_marker_definition(defs, ty) {
            Some(def @ Ty::Datatype { .. }) => datatype_sort_from_ty(def),
            Some(def) => Sort::from_ty(def),
            // A by-name reference the table does not define stays a by-name
            // reference, exactly as before.
            None => Sort::Datatype { name: name.clone(), constructors: Vec::new() },
        };
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Trust (R0 consumer): a bare marker must lower to a DECLARED datatype sort
    /// once — and only once — the body's table says what it means.
    ///
    /// This is the family the markers-everywhere restructure would otherwise
    /// break silently rather than loudly. Both `trust-ir-contract`'s
    /// `collect_datatype_decls` and the in-process ay lane in
    /// `crate::ay_bridge` read "empty constructors" as "this reference carries no
    /// definition" and emit nothing, while `declare-fun` still names the sort —
    /// so with no root definition left to carry the structure, the sort would be
    /// referenced by a declaration that never exists.
    ///
    /// SOUNDNESS is not at stake in either direction: declaring a datatype sort
    /// asserts no fact and a fresh datatype-sorted constant is unconstrained, so
    /// the failure mode is a lost proof, not a false one. That is exactly why it
    /// needs a test — it degrades quietly.
    #[test]
    fn a_bare_marker_lowers_to_a_declared_sort_only_through_the_table() {
        let marker = |name: &str| Ty::Datatype { name: name.into(), variants: vec![] };
        let variants: crate::model::DatatypeVariants = vec![
            ("Leaf".to_string(), vec![("0".to_string(), Ty::Int { width: 64, signed: true })]),
            ("One".to_string(), vec![("0".to_string(), marker("Tree"))]),
        ];
        let inline = Ty::Datatype { name: "Tree".to_string(), variants: variants.clone() };
        let defs = DatatypeDefs::from([("Tree".to_string(), inline.clone())]);
        let by_name = Sort::Datatype { name: "Tree".to_string(), constructors: Vec::new() };

        // Unchanged without a table: a by-name reference stays by-name. This is
        // the pre-carrier behaviour every existing caller of `Sort::from_ty`
        // still gets, since `from_ty` lowers against an empty table.
        assert_eq!(Sort::from_ty(&marker("Tree")), by_name);
        assert_eq!(sort_from_ty_with_defs(&marker("Tree"), &DatatypeDefs::new()), by_name);
        // ...and a table that defines some OTHER datatype changes nothing.
        assert_eq!(
            sort_from_ty_with_defs(
                &marker("Tree"),
                &DatatypeDefs::from([(
                    "Other".to_string(),
                    Ty::Datatype { name: "Other".to_string(), variants: variants.clone() },
                )])
            ),
            by_name,
        );

        // WITH its own entry it becomes a full declaration — byte-identical to
        // what the inline definition lowers to, so a `declare-datatype` built
        // from either spelling is the same declaration.
        let resolved = sort_from_ty_with_defs(&marker("Tree"), &defs);
        assert_eq!(resolved, Sort::from_ty(&inline));
        let Sort::Datatype { constructors, .. } = &resolved else { panic!("datatype sort") };
        assert_eq!(constructors.len(), 2);
        // The recursive FIELD stays a by-name reference: that is the standard
        // natively-recursive SMT-LIB encoding, and inlining it would not
        // terminate. Resolution is one level, at the definitional occurrence.
        assert_eq!(constructors[1].1[0].1, by_name);

        // An inline definition is unaffected by the table (additive order).
        assert_eq!(sort_from_ty_with_defs(&inline, &defs), Sort::from_ty(&inline));
        // Non-datatype lowering is untouched.
        assert_eq!(sort_from_ty_with_defs(&Ty::Bool, &defs), Sort::from_ty(&Ty::Bool));
    }

    /// Trust (R0, WIDENED CARRIER): a marker whose recorded definition is a
    /// `Ty::Adt` must lower to the sort THAT ADT lowers to — `Sort::Int` — and
    /// NOT to a `Sort::Datatype`.
    ///
    /// This is the sharpest consequence of widening the carrier, and it is a
    /// correctness requirement rather than a preference. A canonical cut point
    /// almost always lowers to a flattened `Ty::Adt` (`__tag` + `__v{v}_{f}`),
    /// and every consumer that reads such a value reads it as
    /// `Select(base, Int(k))` over an `Int`-sorted base. Handing the base a
    /// datatype sort instead would make each of those reads ill-sorted, so the
    /// obligation would not merely lose precision — it would not translate.
    ///
    /// The pre-flip walk ROOT already spelled this type inline as `Ty::Adt` and
    /// already got `Sort::Int`; markers-everywhere must not change that answer,
    /// or the flip would move R0 into the sort domain instead of removing it.
    #[test]
    fn a_marker_backed_by_an_adt_definition_keeps_the_adts_own_sort() {
        use crate::model::{VariantDef, insert_datatype_def};
        let marker = |name: &str| Ty::Datatype { name: name.into(), variants: vec![] };
        let i64_ty = || Ty::Int { width: 64, signed: true };
        let tree_adt = Ty::Adt {
            name: "Tree".into(),
            fields: vec![("__tag".into(), i64_ty()), ("__v1_0".into(), i64_ty())],
            variants: vec![
                VariantDef { name: "Leaf".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "One".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), i64_ty())],
                },
            ],
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
        };
        let mut defs = DatatypeDefs::new();
        assert!(insert_datatype_def(&mut defs, tree_adt.clone()));

        assert_eq!(
            sort_from_ty_with_defs(&marker("Tree"), &defs),
            Sort::from_ty(&tree_adt),
            "the marker's sort must be the sort of the type it NAMES",
        );
        assert_eq!(
            sort_from_ty_with_defs(&marker("Tree"), &defs),
            Sort::Int,
            "…which for a flattened enum ADT is Int, the sort its `Select`-based \
             field reads are typed against",
        );
        // Without the entry it is still the undeclared by-name reference — the
        // decline is unchanged, only the ANSWER is new.
        assert_eq!(
            sort_from_ty_with_defs(&marker("Tree"), &DatatypeDefs::new()),
            Sort::Datatype { name: "Tree".to_string(), constructors: Vec::new() },
        );
    }
}

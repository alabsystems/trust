//! An `Opaque` terminator disqualifies EVERY local in the body from
//! `is_single_static_assignment`, which silently deletes the dest-keyed half of
//! the enum tag-range fact and leaves an exhaustive `match`'s shared
//! `otherwise -> Unreachable` block satisfiable — i.e. REFUTED.
//!
//! THE DEFECT, measured on the ay-dpll test graph at seal 30 (ba1b42178dfc):
//! 2962 of 4734 refuted rows were `[unreachable] unreachable code reached
//! FAILED`, and every one of them came from a `#[ntest::timeout]` test. That
//! attribute expands to
//!
//! ```ignore (illustrative)
//! match receiver.recv_timeout(..) {
//!     Ok(Ok(t)) => return t,
//!     Ok(Err(payload)) => std::panic::resume_unwind(payload),
//!     Err(Timeout) => panic!(..),
//!     Err(Disconnected) => panic!(..),
//! }
//! ```
//!
//! whose nested `match` lowers to three `SwitchInt`s sharing ONE `otherwise ->
//! Unreachable` block. `std::panic::resume_unwind` is typed `-> !`, so rustc
//! lowers it with `target: None`; it matches none of `convert.rs`'s
//! panic / UB-if-reached / bulk-alloc recognizers, so it used to become
//! `Terminator::Opaque`. `Terminator::Opaque` carries no destination `Place`, so
//! `Terminator::local_write` answers `LocalWrite::Unlocatable` for EVERY local —
//! and one such terminator anywhere in the body disqualifies every local from
//! `local_defs::is_single_static_assignment`. The dest-keyed membership
//! (`build_discriminant_variant_range_facts` emits `d in {tags}` over a
//! `Discriminant` read's destination ONLY when that destination is
//! single-assignment) therefore vanished for all three switch selectors, every
//! selector was a free variable, and the shared unreachable block was trivially
//! SAT. The counterexample rustc printed names the mechanism exactly:
//! `_10#s8_0 = -1` — the INNER `Result`'s discriminant, outside its own
//! `{0, 1}` tag set.
//!
//! The fix is in `trust-mir-extract`'s `convert.rs`: a DIRECT call whose callee
//! rustc types `-> !` (`direct_callee_returns_never`, a `TyCtxt` query, not a
//! name) lowers to the faithful `Terminator::Call { target: None }` instead of
//! `Opaque`. This file pins the MECHANISM from the trust-vcgen side, where the
//! fact is actually lost, so a future change that reintroduces an `Opaque` on
//! this path fails here rather than 2962 rows later.
//!
//! The load-bearing half is the DECLINE: the tag facts are the only thing added,
//! they are the enum's own type invariant, and a genuinely reachable
//! `Unreachable` (a PARTIAL match, whose `otherwise` really is live) must keep
//! its satisfiable path condition. `a_partial_match_keeps_its_live_otherwise_arm`
//! is that row.
use trust_types::{
    AdtKind, BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VariantDef, VerifiableBody,
    VerifiableFunction,
};

/// An enum EXACTLY as `trust-mir-extract`'s `lower_enum_adt` spells it: the
/// per-variant payloads FLATTENED into `__tag` + `__v{variant}_{field}` beside
/// the `variants` table, with `disc_index_safe` set. Building it any other way
/// makes `place_ty_cow` resolve `((_1 as Ok).0)` to the `__tag` field and the
/// whole fixture stops reproducing the shape it exists to pin.
fn enum_of(name: &str, variants: Vec<VariantDef>) -> Ty {
    let mut fields: Vec<(String, Ty)> = vec![("__tag".into(), Ty::Int { width: 64, signed: true })];
    for (v, variant) in variants.iter().enumerate() {
        for (f, (_, field_ty)) in variant.fields.iter().enumerate() {
            fields.push((format!("__v{v}_{f}"), field_ty.clone()));
        }
    }
    Ty::Adt {
        name: name.into(),
        fields: fields.into(),
        variants: variants.into(),
        disc_index_safe: true,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn result_of(ok: Ty, err: Ty) -> Ty {
    enum_of(
        "core::result::Result",
        vec![
            VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), ok)] },
            VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), err)] },
        ],
    )
}

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}

fn isize_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

/// Which terminator the never-typed diverging call site carries.
#[derive(Clone, Copy, PartialEq, Eq)]
enum DivergingShape {
    /// Pre-fix: the unmodeled-construct sentinel, with no destination `Place`.
    Opaque,
    /// Post-fix: the faithful no-normal-successor call rustc's `-> !` typing licenses.
    NeverTypedCall,
}

/// The `#[ntest::timeout]` shape, reduced to what matters:
///
/// ```ignore (illustrative)
/// bb0: _1 = recv() -> bb1                      // Call dest: the outer Result
/// bb1: _2 = Discriminant(_1);   switch _2 [0->bb2, 1->bb5] otherwise bb4
/// bb2: _3 = Discriminant((_1 as Ok).0); switch _3 [0->bb3, 1->bb6] otherwise bb4
/// bb4: unreachable                             // SHARED otherwise of both switches
/// bb6: <the `-> !` diverging call>             // resume_unwind(payload)
/// ```
///
/// Both switches are exhaustive over their own enum's full tag set, so bb4 is
/// dead — provided each selector carries its type's `d in {0, 1}`.
fn ntest_timeout_shape(shape: DivergingShape) -> VerifiableFunction {
    let inner = result_of(Ty::Unit, u8_ty());
    let outer = result_of(inner.clone(), u8_ty());
    let diverging = match shape {
        DivergingShape::Opaque => Terminator::Opaque {
            kind: "Call::std::panic::resume_unwind".into(),
            targets: vec![],
            span: SourceSpan::default(),
        },
        DivergingShape::NeverTypedCall => Terminator::Call {
            func: "std::panic::resume_unwind".into(),
            args: vec![],
            dest: Place::local(0),
            // The never type IS the evidence that there is no continuation.
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
            callee_identity: None,
            callee_key: None,
        },
    };
    VerifiableFunction {
        name: "ntest_timeout_shape".into(),
        def_path: "t::ntest_timeout_shape".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: outer, name: None },
                LocalDecl { index: 2, ty: isize_ty(), name: None },
                LocalDecl { index: 3, ty: isize_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "t::recv".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Unreachable,
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(2)), (1, BlockId(5))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        // THE NESTED READ: `((_1 as Ok).0)`, a PROJECTED source.
                        rvalue: Rvalue::Discriminant(Place {
                            local: 1,
                            projections: vec![Projection::Downcast(0), Projection::Field(0)],
                        }),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(3)), (1, BlockId(6))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                // The SHARED `otherwise` of both switches — the refuted row.
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Unreachable },
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(6), stmts: vec![], terminator: diverging },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: trust_types::DatatypeDefs::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: trust_types::FunctionSpec::default(),
        tuple_layouts: Default::default(),
    }
}

/// Every variable name the tag-range facts are published OVER.
fn fact_subjects(func: &VerifiableFunction) -> Vec<String> {
    let mut out: Vec<String> = super::value_facts::build_discriminant_variant_range_facts(func)
        .iter()
        .flat_map(|f: &Formula| f.free_variables().into_iter().map(|v| v.to_string()))
        .collect();
    out.sort();
    out.dedup();
    out
}

// ── THE DEFECT ──────────────────────────────────────────────────────────────

/// One `Opaque` terminator, anywhere in the body, deletes the dest-keyed
/// membership for EVERY `Discriminant` read — including reads in blocks the
/// `Opaque` neither dominates nor reaches.
#[test]
fn an_opaque_terminator_disqualifies_every_local_in_the_body() {
    let func = ntest_timeout_shape(DivergingShape::Opaque);
    for local in [2usize, 3] {
        assert!(
            !crate::local_defs::is_single_static_assignment(&func, local),
            "PRE-FIX BASELINE: `_{local}` is written exactly once, yet the `Opaque` \
             terminator in bb6 makes `Terminator::local_write` answer `Unlocatable` \
             for it. If this assertion starts failing, the `Opaque` write model has \
             changed and this file's premise must be re-derived."
        );
    }
    let subjects = fact_subjects(&func);
    for selector in ["_2", "_3"] {
        assert!(
            !subjects.contains(&selector.to_string()),
            "THE DEFECT: the switch selector `{selector}` carries no `d in {{0, 1}}` \
             membership, so the shared `otherwise -> Unreachable` block is satisfiable \
             and the exhaustive match's unreachable row is REFUTED. published: \
             {subjects:?}"
        );
    }
}

// ── THE FIX ─────────────────────────────────────────────────────────────────

/// With the never-typed call lowered faithfully, every selector regains its own
/// type invariant — the nested, PROJECTED read (`((_1 as Ok).0)`) included.
#[test]
fn a_never_typed_diverging_call_leaves_every_selector_bounded() {
    let func = ntest_timeout_shape(DivergingShape::NeverTypedCall);
    for local in [2usize, 3] {
        assert!(
            crate::local_defs::is_single_static_assignment(&func, local),
            "`_{local}` is written exactly once and nothing in the body can have \
             replaced it: a `Call` with `target: None` writes no reachable \
             destination and names the one place it could."
        );
    }
    let subjects = fact_subjects(&func);
    for selector in ["_2", "_3"] {
        assert!(
            subjects.contains(&selector.to_string()),
            "the switch selector `{selector}` must carry its enum's own tag-set \
             membership; without it the shared `otherwise -> Unreachable` block \
             stays satisfiable. published: {subjects:?}"
        );
    }
    // The carrier-keyed half is published either way (it needs no SSA gate — it
    // names `src`'s discriminant, which inhabits the same enum however often
    // `src` is reseated). Pin it so a future change cannot "fix" this file by
    // deleting the dest-keyed half and leaving only an unreachable carrier.
    assert!(
        subjects.iter().any(|s| s == "__trust_mir__discr__1"),
        "the outer read's carrier membership must still be published: {subjects:?}"
    );
    assert!(
        subjects.iter().any(|s| s == "__trust_mir__discr__1@0.0"),
        "the NESTED read's carrier is keyed on the projected place `((_1 as Ok).0)`; \
         its membership must be published too: {subjects:?}"
    );
}

/// The facts the fix restores are ONLY the enum's own tag set. Both shapes agree
/// on the tags, so nothing about the fix widens what may be concluded about a
/// value — it only restores which NAME the true fact is attached to.
#[test]
fn the_restored_fact_is_the_declared_tag_set_and_nothing_more() {
    fn tags(f: &Formula, out: &mut Vec<i128>) {
        match f {
            Formula::Or(cases) => cases.iter().for_each(|c| tags(c, out)),
            Formula::Eq(_, rhs) => {
                if let Formula::Int(t) = rhs.as_ref() {
                    out.push(*t);
                }
            }
            _ => {}
        }
    }
    let func = ntest_timeout_shape(DivergingShape::NeverTypedCall);
    for f in super::value_facts::build_discriminant_variant_range_facts(&func) {
        let mut found = Vec::new();
        tags(&f, &mut found);
        found.sort_unstable();
        assert_eq!(
            found,
            vec![0, 1],
            "every published membership must be exactly `Result`'s own `{{Ok = 0, \
             Err = 1}}`; a wider set proves nothing and a narrower one is a false \
             proof"
        );
    }
}

// ── THE DIRECTION: a genuinely LIVE `otherwise` must stay live ───────────────

/// The same body, but the inner switch covers only tag 0 — a PARTIAL match, whose
/// `otherwise` arm is genuinely reachable at tag 1. Restoring the selector's
/// membership must NOT make that arm's path condition unsatisfiable: `_3 in {0, 1}`
/// and `_3 != 0` are satisfiable together at `_3 == 1`, so the `Unreachable` block
/// keeps a real counterexample and stays refuted.
#[test]
fn a_partial_match_keeps_its_live_otherwise_arm() {
    let mut func = ntest_timeout_shape(DivergingShape::NeverTypedCall);
    let Terminator::SwitchInt { targets, exhaustive_enum_unreachable, .. } =
        &mut func.body.blocks[2].terminator
    else {
        panic!("bb2 is the nested switch");
    };
    // Drop the `Err` arm: now only tag 0 is covered and tag 1 falls through.
    targets.retain(|(v, _)| *v == 0);
    // rustc would not certify this switch exhaustive, and neither do we.
    *exhaustive_enum_unreachable = false;

    let subjects = fact_subjects(&func);
    assert!(
        subjects.contains(&"_3".to_string()),
        "the membership is a fact about the READ, not about the switch: it is \
         published for a partial match too. published: {subjects:?}"
    );
    // The fact is `_3 == 0 || _3 == 1`. The otherwise arm's guard is `_3 != 0`.
    // Those are satisfiable together — the arm is live and must stay refutable.
    let facts = super::value_facts::build_discriminant_variant_range_facts(&func);
    let dest_fact = facts
        .iter()
        .find(|f| f.free_variables().iter().any(|v| v == "_3"))
        .expect("the selector's membership is published");
    let Formula::Or(cases) = dest_fact else {
        panic!("a two-variant membership is a disjunction, got {dest_fact:?}");
    };
    assert_eq!(
        cases.len(),
        2,
        "the membership must still ADMIT tag 1 — the value the live `otherwise` arm \
         is taken at. A membership that pinned `_3 == 0` would vacuously discharge a \
         reachable arm, which is the false proof this direction exists to exclude."
    );
}

/// The decline that keeps the fix honest at its own boundary: an `Opaque` that is
/// NOT a never-typed call (inline asm, unmodeled control flow) keeps the
/// fail-closed write model. Nothing here widens `Opaque` itself.
#[test]
fn a_non_call_opaque_still_disqualifies_the_body() {
    let mut func = ntest_timeout_shape(DivergingShape::Opaque);
    func.body.blocks[6].terminator = Terminator::Opaque {
        kind: "InlineAsm".into(),
        targets: vec![],
        span: SourceSpan::default(),
    };
    assert!(
        !crate::local_defs::is_single_static_assignment(&func, 2),
        "an unmodeled construct may write anything; `Unlocatable` is the correct \
         answer for it and this change must not touch that"
    );
}

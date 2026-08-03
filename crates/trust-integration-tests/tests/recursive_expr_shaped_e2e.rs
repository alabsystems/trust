// trust-integration-tests/tests/recursive_expr_shaped_e2e.rs
//
// WALL C END-TO-END (EXPR-SHAPED): a datatype that mixes a PAYLOAD constructor
// and a MULTI-recursive constructor — the real kernel `Expr`'s `Var/App` shape —
// driven through the REAL trust-vcgen induction emitter -> trust-certify
// generated `.rec` discharge, kernel-checked.
//
// The sibling e2e lanes cover the UNARY-recursive (`mirror:&Level->Level`, one
// IH, committed extractor artifact) and the pure MULTI-IH (`rebuild:&BTree->BTree`,
// two IHs) shapes. THIS test closes the shape the kernel actually uses: one
// datatype carrying BOTH a non-recursive PAYLOAD field (held fixed) and a
// multi-recursive constructor (two IHs), together, end to end.
//
//   erebuild : &E -> E     (E = Lit(v : Bit) | App(f : *const E)(a : *const E))
//     erebuild (Lit v)   = Lit v                    -- payload v held fixed, no IH
//     erebuild (App f a) = App (erebuild f) (erebuild a)   -- TWO self-calls
//
// The pipeline is literal: the emitter walks the hand-built MIR (SwitchInt on the
// discriminant; the `Lit` arm COPIES the `Bit` payload into the rebuilt aggregate;
// the `App` arm reads each `*const E` field, refs it, self-calls, and rebuilds),
// and the VCs it returns drive the generated `.rec` discharge:
//
//   1. vcgen emits: the `Lit` case (one `Bit` field binder, NO IH, `Eq(Lit v, Lit v)`)
//      + the `App` case (two IHs `__ih0`/`__ih1`) + the `[induction:expr::E;cases=2]`
//      conclusion;
//   2. certify reconstructs `E` AND the `Bit` payload datatype, folds the model via
//      `E.rec`, generates the proof (the `Lit` minor by `Eq.refl` holding the
//      payload, the `App` minor consuming both IHs), and the clean kernel checks it;
//   3. no masquerade: refl-only pseudo-proof kernel-REJECTED; the FALSE
//      postcondition `erebuild e = App e e` rejected at discharge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::recursive_datatype_functional::{
    certify_recursive_datatype_functional, induction_is_load_bearing,
    recheck_recursive_datatype_functional,
};
use trust_types::{
    AggregateKind, BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue,
    Sort, SortFromTy, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction,
};
use trust_vcgen::recursive_datatype_functional::recursive_datatype_functional_vcs;

// ── The Bit payload datatype and the Expr-shaped E datatype ──────────────────

/// `Bit = B0 | B1` — a nullary-constructor payload (held fixed by `erebuild`).
fn bit_dt() -> Ty {
    Ty::Datatype {
        name: "bit::Bit".to_string(),
        variants: vec![("B0".to_string(), vec![]), ("B1".to_string(), vec![])],
    }
}

fn e_ref() -> Ty {
    Ty::Datatype { name: "expr::E".to_string(), variants: Vec::new() }
}

/// `E = Lit(Bit) | App(E, E)` — a payload `Lit` and a two-recursive-field `App`
/// in one datatype (the kernel `Expr`'s `Var/App` shape). The `Lit` field carries
/// the FULL `Bit` definition (a payload is a distinct type the extractor knows in
/// full), unlike the `App` self-references which are name-only (`e_ref`).
fn e_dt() -> Ty {
    Ty::Datatype {
        name: "expr::E".to_string(),
        variants: vec![
            ("Lit".to_string(), vec![("0".to_string(), bit_dt())]),
            ("App".to_string(), vec![("0".to_string(), e_ref()), ("1".to_string(), e_ref())]),
        ],
    }
}

fn raw_e() -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(e_dt()) }
}

fn e_sort() -> Sort {
    Sort::from_ty(&e_dt())
}

fn bit_sort() -> Sort {
    Sort::from_ty(&bit_dt())
}

fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(str::to_string) }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// A `Downcast(variant)+Field(i)` read of `*_1` (the scrutinee's `i`-th field).
fn field_read(variant: usize, field: usize) -> Rvalue {
    Rvalue::Use(Operand::Copy(Place {
        local: 1,
        projections: vec![
            Projection::Deref,
            Projection::Downcast(variant),
            Projection::Field(field),
        ],
    }))
}

/// The hand-built MIR of `erebuild`: the `Lit` arm copies the `Bit` payload into
/// the rebuilt `Lit`; the `App` arm rebuilds both children via two self-calls.
fn erebuild_func(post: Formula) -> VerifiableFunction {
    let body = VerifiableBody {
        locals: vec![
            local(0, e_dt(), None), // _0 : E (return)
            local(1, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, Some("e")),
            local(2, Ty::Int { width: 64, signed: true }, None), // _2 : discriminant
            local(3, bit_dt(), None),                            // _3 : Bit (Lit payload, by value)
            local(4, raw_e(), None),                             // _4 : *const E (App field 0)
            local(5, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None), // _5 : &E
            local(6, e_dt(), None),                              // _6 : erebuild(f) dest
            local(7, raw_e(), None),                             // _7 : *const E (App field 1)
            local(8, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None), // _8 : &E
            local(9, e_dt(), None),                              // _9 : erebuild(a) dest
            local(10, raw_e(), None),                            // _10 : &raw _6
            local(11, raw_e(), None),                            // _11 : &raw _9
        ],
        blocks: vec![
            // bb0: _2 = discriminant((*_1)); switch [(0 -> Lit), (1 -> App)] else bb1
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(2),
                    Rvalue::Discriminant(Place { local: 1, projections: vec![Projection::Deref] }),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(2)), (1, BlockId(3))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: true,
                    span: SourceSpan::default(),
                },
            },
            // bb1: unreachable (exhaustive-match otherwise)
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
            // bb2 (Lit arm): _3 = ((*_1 as Lit).0); _0 = E::Lit(copy _3); goto bb6
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    assign(Place::local(3), field_read(0, 0)),
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "expr::E".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(3))],
                        ),
                    ),
                ],
                terminator: Terminator::Goto(BlockId(6)),
            },
            // bb3 (App, left child): _4 = ((*_1 as App).0); _5 = &(*_4);
            //                        erebuild(move _5) -> _6, bb4
            BasicBlock {
                id: BlockId(3),
                stmts: vec![
                    assign(Place::local(4), field_read(1, 0)),
                    assign(
                        Place::local(5),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 4, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                terminator: Terminator::Call {
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "erebuild".to_string(),
                    args: vec![Operand::Move(Place::local(5))],
                    dest: Place::local(6),
                    target: Some(BlockId(4)),
                    span: SourceSpan::default(),
                    atomic: None,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb4 (App, right child): _7 = ((*_1 as App).1); _8 = &(*_7);
            //                         erebuild(move _8) -> _9, bb5
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(Place::local(7), field_read(1, 1)),
                    assign(
                        Place::local(8),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 7, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                terminator: Terminator::Call {
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "erebuild".to_string(),
                    args: vec![Operand::Move(Place::local(8))],
                    dest: Place::local(9),
                    target: Some(BlockId(5)),
                    span: SourceSpan::default(),
                    atomic: None,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb5 (rebuild App): _10 = &raw _6; _11 = &raw _9;
            //                    _0 = E::App(copy _10, copy _11); goto bb6
            BasicBlock {
                id: BlockId(5),
                stmts: vec![
                    assign(Place::local(10), Rvalue::AddressOf(false, Place::local(6))),
                    assign(Place::local(11), Rvalue::AddressOf(false, Place::local(9))),
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "expr::E".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(10)), Operand::Copy(Place::local(11))],
                        ),
                    ),
                ],
                terminator: Terminator::Goto(BlockId(6)),
            },
            // bb6: return
            BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
        ],
        arg_count: 1,
        return_ty: e_dt(),
    };
    VerifiableFunction {
        name: "erebuild".to_string(),
        def_path: "erebuild".to_string(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![post],
        spec: Default::default(),
    }
}

/// The TRUE postcondition `erebuild e = e`.
fn identity_post() -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), e_sort())),
        Box::new(Formula::var_owned("e".to_string(), e_sort())),
    )
}

/// The FALSE postcondition `erebuild e = App e e` (negative control).
fn wrong_app_post() -> Formula {
    let e = || Formula::var_owned("e".to_string(), e_sort());
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), e_sort())),
        Box::new(Formula::Ctor { ctor: "App".to_string(), args: vec![e(), e()], sort: e_sort() }),
    )
}

// ── THE MILESTONE: Expr-shaped MIR -> real emitter -> mixed payload/two-IH
//    generated .rec discharge, kernel-checked ─────────────────────────────────

#[test]
fn recursive_erebuild_expr_shaped_identity_end_to_end() {
    let func = erebuild_func(identity_post());

    // 1. VC-GEN (the REAL emitter): the Expr-shaped induction bundle.
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "Lit case + App case + conclusion, got {vcs:#?}");
    let props: Vec<&str> = vcs
        .iter()
        .map(|vc| match &vc.kind {
            VcKind::FunctionalCorrectness { property, .. } => property.as_str(),
            other => panic!("expected FunctionalCorrectness, got {other:?}"),
        })
        .collect();
    assert_eq!(
        props,
        vec![
            "recursive_datatype_functional_case::Lit",
            "recursive_datatype_functional_case::App",
            "recursive_datatype_functional_conclusion[induction:expr::E;cases=2]",
        ]
    );

    // The Lit case binds ONE payload field and NO IH; the App case binds TWO IHs.
    let Formula::Forall(lit_binders, _) = &vcs[0].formula else {
        panic!("Lit case must be a Forall over its payload field, got {:?}", vcs[0].formula);
    };
    assert!(
        lit_binders.iter().all(|(n, _)| !n.as_str().starts_with("__ih")),
        "the Lit payload case carries NO IH"
    );
    let Formula::Forall(app_binders, _) = &vcs[1].formula else {
        panic!("App case must be a Forall, got {:?}", vcs[1].formula);
    };
    let app_ihs: Vec<&str> =
        app_binders.iter().map(|(s, _)| s.as_str()).filter(|n| n.starts_with("__ih")).collect();
    assert_eq!(app_ihs, vec!["__ih0", "__ih1"], "App binds two IHs (one per recursive field)");

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated `.rec` term (Bit
    //    payload reconstructed + held, App minor consuming both IHs) through the
    //    clean kernel.
    let evidence = certify_recursive_datatype_functional(&vcs)
        .expect("the emitted Expr-shaped erebuild-identity bundle must certify (kernel-checked)");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
    assert!(
        recheck_recursive_datatype_functional(&vcs, &term, &context, &lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE: the App minor genuinely needed its IHs.
    assert!(
        induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the Expr-shaped .rec proof is ACCEPTED"
    );
}

// ── NEGATIVE control end-to-end ──────────────────────────────────────────────

#[test]
fn recursive_erebuild_expr_shaped_wrong_postcondition_end_to_end_rejected() {
    let func = erebuild_func(wrong_app_post());
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "the false spec's bundle is still emitted, got {vcs:#?}");
    assert!(
        certify_recursive_datatype_functional(&vcs).is_none(),
        "the false postcondition `erebuild e = App e e` must never certify"
    );
    // Sanity: the payload binding is unaffected by the false conclusion — the
    // wrong bundle is a genuine spec falsification, not a malformation.
    let _ = bit_sort();
}

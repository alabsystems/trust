// trust-integration-tests/tests/recursive_multi_ih_e2e.rs
//
// WALL C END-TO-END (MULTI-IH): a MULTI-recursive datatype function driven
// through the REAL trust-vcgen induction emitter -> trust-certify generated
// `.rec` discharge, kernel-checked.
//
// The sibling `recursive_datatype_functional_e2e` proves the pipeline on the
// UNARY-recursive `mirror : &Level -> Level` (one self-call, one IH) loaded from
// a committed extractor artifact. THIS test complements it on the MULTI-IH shape
// (a constructor with TWO recursive fields => the `.rec` minor binds TWO IHs),
// the `Max`/`IMax`-shaped case the `infer_type <-> whnf <-> is_def_eq` cluster
// needs. Its `VerifiableFunction` is hand-built MIR (the same shape the emitter's
// own unit fixtures use — SwitchInt on the discriminant, `Downcast`+`Field`
// payload reads, a self-`Call` per recursive field, an `Aggregate` rebuild),
// NOT a committed extractor artifact: the point here is that the REAL emitter and
// the generated-`.rec` discharge AGREE on the multi-IH bundle end to end, not to
// re-pin the extractor (that is the sibling artifact test's job).
//
//   rebuild : &BTree -> BTree     (BTree = Leaf | Node(*const BTree, *const BTree))
//     rebuild Leaf       = Leaf
//     rebuild (Node l r) = Node (rebuild l) (rebuild r)     -- TWO self-calls
//
//   1. vcgen emits the induction bundle for the declared postcondition
//      `rebuild t = t`: the `Leaf` case + the `Node` case carrying BOTH IHs
//      (`__ih0` for the left child, `__ih1` for the right) in place of the two
//      recursive calls + the `[induction:btree::BTree;cases=2]` conclusion;
//   2. certify parses it, reconstructs `BTree`, builds the model as a `BTree.rec`
//      fold, GENERATES the two-IH `.rec` induction proof (two `congrArg`s joined
//      by `Eq.trans`), and the clean kernel checks it (Certified tier);
//   3. no masquerade: the refl-only pseudo-proof is kernel-REJECTED (the IHs are
//      load-bearing), and the FALSE postcondition `rebuild t = Node t t` — pushed
//      through the SAME two lanes — is kernel-rejected at discharge.
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

// ── The BTree datatype (mirrors the emitter unit fixtures' `level_dt` shape) ──

/// Name-only reference (a recursive field carries the datatype by name; the raw
/// pointer indirection is peeled by the emitter's `sort_for_ty`).
fn btree_ref() -> Ty {
    Ty::Datatype { name: "btree::BTree".to_string(), variants: Vec::new() }
}

/// `BTree = Leaf | Node(BTree, BTree)` — two recursive fields on `Node`.
fn btree_dt() -> Ty {
    Ty::Datatype {
        name: "btree::BTree".to_string(),
        variants: vec![
            ("Leaf".to_string(), vec![]),
            (
                "Node".to_string(),
                vec![("0".to_string(), btree_ref()), ("1".to_string(), btree_ref())],
            ),
        ],
    }
}

fn raw_btree() -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(btree_dt()) }
}

fn btree_sort() -> Sort {
    Sort::from_ty(&btree_dt())
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

/// The hand-built MIR of the two-recursive-field `rebuild`, with `post` attached
/// as the declared spec (the fixture carries no `#[ensures]`).
fn rebuild_func(post: Formula) -> VerifiableFunction {
    let body = VerifiableBody {
        locals: vec![
            local(0, btree_dt(), None), // _0 : BTree (return)
            local(1, Ty::Ref { mutable: false, inner: Box::new(btree_dt()) }, Some("t")),
            local(2, Ty::Int { width: 64, signed: true }, None), // _2 : discriminant
            local(3, raw_btree(), None),                         // _3 : *const BTree (field 0)
            local(4, Ty::Ref { mutable: false, inner: Box::new(btree_dt()) }, None), // _4 : &BTree
            local(5, btree_dt(), None),                          // _5 : rebuild(left) dest
            local(6, raw_btree(), None),                         // _6 : *const BTree (field 1)
            local(7, Ty::Ref { mutable: false, inner: Box::new(btree_dt()) }, None), // _7 : &BTree
            local(8, btree_dt(), None),                          // _8 : rebuild(right) dest
            local(9, raw_btree(), None),                         // _9 : &raw _5
            local(10, raw_btree(), None),                        // _10 : &raw _8
        ],
        blocks: vec![
            // bb0: _2 = discriminant((*_1)); switch [(0 -> Leaf), (1 -> Node)] else bb1
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
            // bb2 (Leaf arm): _0 = BTree::Leaf; goto bb6
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "btree::BTree".to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![],
                    ),
                )],
                terminator: Terminator::Goto(BlockId(6)),
            },
            // bb3 (Node, left child): _3 = ((*_1 as Node).0); _4 = &(*_3);
            //                         rebuild(move _4) -> _5, bb4
            BasicBlock {
                id: BlockId(3),
                stmts: vec![
                    assign(Place::local(3), field_read(1, 0)),
                    assign(
                        Place::local(4),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 3, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                terminator: Terminator::Call {
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "rebuild".to_string(),
                    args: vec![Operand::Move(Place::local(4))],
                    dest: Place::local(5),
                    target: Some(BlockId(4)),
                    span: SourceSpan::default(),
                    atomic: None,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb4 (Node, right child): _6 = ((*_1 as Node).1); _7 = &(*_6);
            //                          rebuild(move _7) -> _8, bb5
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(Place::local(6), field_read(1, 1)),
                    assign(
                        Place::local(7),
                        Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 6, projections: vec![Projection::Deref] },
                        },
                    ),
                ],
                terminator: Terminator::Call {
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "rebuild".to_string(),
                    args: vec![Operand::Move(Place::local(7))],
                    dest: Place::local(8),
                    target: Some(BlockId(5)),
                    span: SourceSpan::default(),
                    atomic: None,
                    unwind: trust_types::UnwindEdge::Unreachable,
                },
            },
            // bb5 (rebuild Node): _9 = &raw _5; _10 = &raw _8;
            //                     _0 = BTree::Node(copy _9, copy _10); goto bb6
            BasicBlock {
                id: BlockId(5),
                stmts: vec![
                    assign(Place::local(9), Rvalue::AddressOf(false, Place::local(5))),
                    assign(Place::local(10), Rvalue::AddressOf(false, Place::local(8))),
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "btree::BTree".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Copy(Place::local(9)), Operand::Copy(Place::local(10))],
                        ),
                    ),
                ],
                terminator: Terminator::Goto(BlockId(6)),
            },
            // bb6: return
            BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
        ],
        arg_count: 1,
        return_ty: btree_dt(),
    };
    VerifiableFunction {
        name: "rebuild".to_string(),
        def_path: "rebuild".to_string(),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![post],
        spec: Default::default(),
    }
}

/// The TRUE postcondition `rebuild t = t`.
fn identity_post() -> Formula {
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), btree_sort())),
        Box::new(Formula::var_owned("t".to_string(), btree_sort())),
    )
}

/// The FALSE postcondition `rebuild t = Node t t` (negative control).
fn wrong_node_post() -> Formula {
    let t = || Formula::var_owned("t".to_string(), btree_sort());
    Formula::Eq(
        Box::new(Formula::var_owned("_0".to_string(), btree_sort())),
        Box::new(Formula::Ctor {
            ctor: "Node".to_string(),
            args: vec![t(), t()],
            sort: btree_sort(),
        }),
    )
}

// ── THE MILESTONE: hand-built multi-recursive MIR -> real emitter -> two-IH
//    generated .rec discharge, kernel-checked ─────────────────────────────────

#[test]
fn recursive_rebuild_multi_ih_identity_end_to_end() {
    let func = rebuild_func(identity_post());

    // 1. VC-GEN (the REAL emitter): the multi-IH induction bundle.
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "Leaf case + Node case + conclusion, got {vcs:#?}");
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
            "recursive_datatype_functional_case::Leaf",
            "recursive_datatype_functional_case::Node",
            "recursive_datatype_functional_conclusion[induction:btree::BTree;cases=2]",
        ]
    );

    // The Node case must carry BOTH IHs (`__ih0` and `__ih1`) — the multi-IH
    // shape that distinguishes this from the unary mirror lane.
    let Formula::Forall(binders, _) = &vcs[1].formula else {
        panic!("Node case must be a Forall, got {:?}", vcs[1].formula);
    };
    let ih_binders: Vec<&str> =
        binders.iter().map(|(s, _)| s.as_str()).filter(|n| n.starts_with("__ih")).collect();
    assert_eq!(ih_binders, vec!["__ih0", "__ih1"], "Node binds two IHs (one per recursive field)");

    // 2. DISCHARGE: the LITERAL emitted VCs drive the generated two-IH `.rec`
    //    induction term through the clean kernel.
    let evidence = certify_recursive_datatype_functional(&vcs)
        .expect("the emitted multi-IH rebuild-identity bundle must certify (kernel-checked .rec)");
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("expected CleanCic evidence");
    };
    assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
    assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
    assert!(
        recheck_recursive_datatype_functional(&vcs, &term, &context, &lineage),
        "the serialized certificate must independently re-check via the clean kernel"
    );

    // 3. NO MASQUERADE: the discharge genuinely needed the IHs — the refl-only
    //    pseudo-proof of the same goal is kernel-rejected.
    assert!(
        induction_is_load_bearing(&vcs),
        "the refl-only pseudo-proof must be REJECTED while the two-IH .rec proof is ACCEPTED"
    );
}

// ── NEGATIVE control end-to-end: a FALSE postcondition on the SAME multi-
//    recursive body rides the same two lanes and dies at the kernel ────────────

#[test]
fn recursive_rebuild_multi_ih_wrong_postcondition_end_to_end_rejected() {
    let func = rebuild_func(wrong_node_post());
    let vcs = recursive_datatype_functional_vcs(&func);
    assert_eq!(vcs.len(), 3, "the false spec's bundle is still emitted, got {vcs:#?}");
    assert!(
        certify_recursive_datatype_functional(&vcs).is_none(),
        "the false postcondition `rebuild t = Node t t` must never certify"
    );
}

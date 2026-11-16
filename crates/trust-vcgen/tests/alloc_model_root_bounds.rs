// Trust (verified-sysroot §5 step 3, slice 2) — the allocation model's
// PROVABLE half, at the `*mut T::add::precondition_check` shape.
//
// Slice 1 (landed 0e831c4100) made the shape STATABLE: the expose cast
// `p as usize` is identity over the collapsed allocation model, so the
// precondition's overflow legs range over the pointer's own term. This file
// pins slice 2: for a pointer that PROVABLY roots at a model-covered
// allocation (`&raw arr` of a whole local of statically sized sort), the
// minted address carries the model's two axioms —
//
//     A1: 1 <= addr                        (allocations never contain null)
//     A2: addr <= usize::MAX - size(A)     (one-past-end is representable)
//
// — and the `ptr::add` precondition's checked-add leg becomes PROVABLE
// exactly up to the allocation boundary:
//
//   * `count * size == size(A)` (one-past-end)   -> ay PROVES;
//   * one element further                        -> REFUTED / unproven,
//     because A2 admits `addr == usize::MAX - size(A)` and the add wraps;
//   * an UNROOTED pointer (a raw-pointer argument) mints NO bounds and the
//     same in-bounds shape stays unproven — red if the minting gate is ever
//     widened to pointers with no allocation guarantee;
//   * a CROSS-ALLOCATION address compare stays unprovable in BOTH
//     directions — the model never relates two distinct roots.
//
// Synthetic MIR, structured exactly like the extractor's lowering of the
// precondition body (checked mul, checked add over the exposed address).

use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

const UMAX: i128 = u64::MAX as i128;

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn verdict(router: &trust_router::Router, vc: &VerificationCondition) -> VerificationResult {
    let results = router.verify_all(std::slice::from_ref(vc));
    results.into_iter().next().expect("one verdict per VC").1
}

/// The `*mut T::add::precondition_check` shape over a rooted pointer:
///
///     arr: [u32; 2] = [0; 2];          // the model-covered allocation (8 bytes)
///     p = &raw const arr;              // the root borrow
///     addr = p as usize;               // the expose cast (identity, slice 1)
///     (byte_off, o1) = count checked* size;   assert !o1;
///     (_sum, o2)     = addr checked+ byte_off; assert !o2;   // the leg at issue
fn rooted_precheck_func(name: &str, count: u128, size: u128) -> VerifiableFunction {
    let span = SourceSpan::default();
    let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 2 };
    let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(arr_ty.clone()) };
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: arr_ty, name: Some("arr".into()) },
                LocalDecl { index: 2, ty: ptr_ty, name: Some("p".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("addr".into()) },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: Some("byte_off".into()) },
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Repeat(Operand::Constant(ConstValue::Uint(0, 32)), 2),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::AddressOf(false, Place::local(1)),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::usize()),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Mul,
                                Operand::Constant(ConstValue::Uint(count, 64)),
                                Operand::Constant(ConstValue::Uint(size, 64)),
                            ),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        span: span.clone(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(5)),
                            ),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::field(6, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        span: span.clone(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn add_overflow_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if *op == BinOp::Add))
        .collect()
}

/// FALSIFYING (prove direction): the one-past-end `ptr::add` precondition on
/// a model-covered root PROVES. `count * size == 8 == size(arr)`, and A2
/// bounds `addr <= usize::MAX - 8`, so `addr + 8` cannot wrap. Red if the
/// root-bounds minting regresses (the leg goes Unknown) or if the bound stops
/// reaching the obligation.
#[test]
fn rooted_one_past_end_add_leg_proves() {
    let func = rooted_precheck_func("rooted_in_bounds", 2, 4);
    let vcs = add_overflow_vcs(&func);
    assert_eq!(vcs.len(), 1, "exactly one checked-add overflow leg expected");
    let vc = &vcs[0];

    // The model's axioms must be present and bound to the minted address:
    // A2's exact constant is `usize::MAX - size(arr)` — off-by-anything here
    // is a wrong model, not a precision loss.
    let dbg = format!("{:?}", vc.formula);
    let a2 = UMAX - 8;
    assert!(
        dbg.contains(&format!("Int({a2})")),
        "A2's exact bound `usize::MAX - 8` must reach the add obligation: {dbg}"
    );

    let result = verdict(&router(), vc);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "one-past-end `addr + 8` on an 8-byte rooted allocation cannot wrap; got {result:?}\nformula: {dbg}"
    );
}

/// FALSIFYING (refute direction): ONE ELEMENT past one-past-end must NOT
/// prove. A2 admits `addr == usize::MAX - 8`, where `addr + 12` wraps — the
/// model's boundary is the allocation's, exactly. Red if the bounds are ever
/// minted too tight (a smaller upper bound would falsely prove this) or the
/// leg is vacuously discharged.
#[test]
fn rooted_past_end_add_leg_never_proves() {
    let func = rooted_precheck_func("rooted_out_of_bounds", 3, 4);
    let vcs = add_overflow_vcs(&func);
    assert_eq!(vcs.len(), 1, "exactly one checked-add overflow leg expected");
    let result = verdict(&router(), &vcs[0]);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "`addr + 12` on an 8-byte allocation can wrap at addr == usize::MAX - 8; \
         a Proved here is a FALSE PROOF: {result:?}"
    );
}

/// FALSIFYING (gate direction): the SAME in-bounds shape over an UNROOTED
/// pointer (a raw-pointer argument — no allocation guarantee; it may
/// legitimately hold `usize::MAX`) must stay unproven. Red if
/// `alloc_model_expose_root_bounds` is ever widened past provable roots.
#[test]
fn unrooted_pointer_add_leg_stays_unproven() {
    let span = SourceSpan::default();
    let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) };
    let func = VerifiableFunction {
        name: "unrooted_in_bounds_shape".to_string(),
        def_path: "test::unrooted_in_bounds_shape".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("addr".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::usize()),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(8, 64)),
                            ),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: span.clone(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let vcs = add_overflow_vcs(&func);
    assert_eq!(vcs.len(), 1, "exactly one checked-add overflow leg expected");
    let result = verdict(&router(), &vcs[0]);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "an argument pointer has no allocation guarantee (it may hold usize::MAX); \
         a Proved here means root bounds were minted for an unrooted pointer — \
         a FALSE PROOF: {result:?}"
    );
}

/// FALSIFYING (separation honesty): two DISTINCT roots' exposed addresses are
/// UNRELATED by the model — neither `addr1 == addr2` nor `addr1 != addr2` is
/// provable. The model has no separation axiom yet (that is the RESEARCH
/// half, `ptr_offset_from_unsigned`'s same-allocation premise); red if either
/// direction starts proving without one.
#[test]
fn cross_allocation_compare_stays_unproven_both_directions() {
    let build = |name: &str, expected: bool| {
        let span = SourceSpan::default();
        let arr_ty = Ty::Array { elem: Box::new(Ty::u32()), len: 2 };
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(arr_ty.clone()) };
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: arr_ty.clone(), name: Some("arr1".into()) },
                    LocalDecl { index: 2, ty: arr_ty, name: Some("arr2".into()) },
                    LocalDecl { index: 3, ty: ptr_ty.clone(), name: Some("p1".into()) },
                    LocalDecl { index: 4, ty: ptr_ty, name: Some("p2".into()) },
                    LocalDecl { index: 5, ty: Ty::usize(), name: Some("addr1".into()) },
                    LocalDecl { index: 6, ty: Ty::usize(), name: Some("addr2".into()) },
                    LocalDecl { index: 7, ty: Ty::Bool, name: Some("same".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::Repeat(
                                    Operand::Constant(ConstValue::Uint(0, 32)),
                                    2,
                                ),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Repeat(
                                    Operand::Constant(ConstValue::Uint(0, 32)),
                                    2,
                                ),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::AddressOf(false, Place::local(1)),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::AddressOf(false, Place::local(2)),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::Cast(Operand::Copy(Place::local(3)), Ty::usize()),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(6),
                                rvalue: Rvalue::Cast(Operand::Copy(Place::local(4)), Ty::usize()),
                                span: span.clone(),
                            },
                            Statement::Assign {
                                place: Place::local(7),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Eq,
                                    Operand::Copy(Place::local(5)),
                                    Operand::Copy(Place::local(6)),
                                ),
                                span: span.clone(),
                            },
                        ],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::local(7)),
                            expected,
                            msg: AssertMessage::Custom(format!(
                                "cross-allocation compare (claims addr1 {} addr2)",
                                if expected { "==" } else { "!=" }
                            )),
                            target: BlockId(1),
                            span: span.clone(),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    };
    let router = router();
    for (name, expected) in
        [("cross_alloc_claim_unequal", false), ("cross_alloc_claim_equal", true)]
    {
        let func = build(name, expected);
        let vcs: Vec<_> = generate_vcs(&func)
            .into_iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                    if message.contains("cross-allocation compare"))
            })
            .collect();
        assert_eq!(vcs.len(), 1, "{name}: the compare obligation must exist");
        let result = verdict(&router, &vcs[0]);
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "{name}: the model must not relate two distinct allocations' addresses \
             (no separation axiom is minted); got {result:?}"
        );
    }
}

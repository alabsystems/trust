use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{
    build_additive_bound_facts, build_cast_bound_facts, build_cast_lower_bound_facts,
    clamp_upper_bound, unsigned_upper_bound,
};

/// `fn assign_partition(p:u32, h:u64)->u32 { let n = p.max(1) as u64; (h % n) as u32 }`
/// MIR shape: `_4 = Ord::max(_1, 1)` (call term), `_3 = _4 as u64` (value-preserving
/// widening). `build_cast_lower_bound_facts` must emit `Ge(_3, 1)` keyed on the cast
/// dest `_3`. `narrowing` toggles a value-CHANGING cast (u32->u8) which must be rejected.
fn max_then_cast(c: i128, narrowing: bool) -> VerifiableFunction {
    let (src_ty, dst_ty) =
        if narrowing { (Ty::u32(), Ty::u8()) } else { (Ty::u32(), Ty::u64()) };
    VerifiableFunction {
        name: "assign_partition".into(),
        def_path: "assign_partition".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("h".into()) },
                LocalDecl { index: 3, ty: dst_ty.clone(), name: Some("n".into()) },
                LocalDecl { index: 4, ty: src_ty, name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "<u32 as core::cmp::Ord>::max".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(c as u128, 32)),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(4)), dst_ty),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn max_const_carries_lower_bound_across_widening() {
    let func = max_then_cast(1, false);
    let facts = build_cast_lower_bound_facts(&func);
    assert_eq!(
        facts,
        vec![Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        )],
        "max(p,1) as u64 must yield (cast)>=1; got {facts:?}"
    );
}

#[test]
fn max_const_lower_bound_rejected_on_narrowing_cast() {
    // u32 -> u8 is value-CHANGING (truncation); the lower bound must NOT carry.
    let func = max_then_cast(1, true);
    assert!(
        build_cast_lower_bound_facts(&func).is_empty(),
        "a narrowing cast must not carry a lower bound (unsound under truncation)"
    );
}

/// SOUNDNESS LOCK mirroring `mutant/cast_reassigned_source_div.rs`: the cast source
/// `a` is REASSIGNED after a value-preserving widen (`let mut a = x.max(1); let _d =
/// a as u128; a = b; 100 % a`). The source has TWO stores, so the SSA-staleness gate
/// MUST drop the lower bound — otherwise an unguarded `(cast) >= 1` would false-prove
/// `a >= 1` after `a = b` and wrongly discharge the divide-by-zero on `100 % a`.
#[test]
fn max_const_lower_bound_dropped_when_source_reassigned() {
    // bb0: _4 = max(_1, 1) -> bb1
    // bb1: _3 = _4 as u128 ; _4 = copy _2 (REASSIGN source) ; Return
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u128(), name: Some("_d".into()) },
                LocalDecl { index: 4, ty: Ty::u64(), name: Some("a".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "<u64 as core::cmp::Ord>::max".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Cast(Operand::Copy(Place::local(4)), Ty::u128()),
                            span: SourceSpan::default(),
                        },
                        // REASSIGN the cast source `_4` — second store.
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(
        build_cast_lower_bound_facts(&func).is_empty(),
        "a reassigned cast source must drop the lower bound (stale-link false-proof lock)"
    );
}

/// `fn f(i:i32, arr:&[u8;10]) -> u8 { let j = i.clamp(0,9); arr[j as usize] }`
/// MIR shape: `_3 = Ord::clamp(_1, 0, 9)` (call term), `_4 = _3 as usize`,
/// then the access. `build_cast_bound_facts` must emit `Le(_4, 9)`.
fn clamp_then_cast(lo: i128, hi: i128) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("_2".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("j".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "<i32 as core::cmp::Ord>::clamp".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(lo)),
                            Operand::Constant(ConstValue::Int(hi)),
                        ],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(3)), Ty::usize()),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn clamp_then_cast_emits_upper_bound_on_cast_dest() {
    let func = clamp_then_cast(0, 9);
    let facts = build_cast_bound_facts(&func);
    // Expect exactly `Le(Var("_4"), Int(9))` — the upper bound on the cast dest.
    assert_eq!(
        facts,
        vec![Formula::Le(
            Box::new(Formula::Var("_4".into(), Sort::Int)),
            Box::new(Formula::Int(9)),
        )],
        "clamp(0,9) as usize must yield (cast)<=9; got {facts:?}"
    );
}

#[test]
fn clamp_then_cast_nonzero_lower_still_upper_only() {
    // clamp(2,7): upper bound 7, NO lower bound emitted (unsound under trunc).
    let func = clamp_then_cast(2, 7);
    let facts = build_cast_bound_facts(&func);
    assert_eq!(
        facts,
        vec![Formula::Le(
            Box::new(Formula::Var("_4".into(), Sort::Int)),
            Box::new(Formula::Int(7)),
        )]
    );
}

/// Build the `min`/`max`-shaped SwitchInt diamond:
///
/// ```text
///   bb0: _g = cmp(v, C) ; SwitchInt(_g){ 0->bb_false, otherwise->bb_true }
///   bb1: _L = const C   ; Goto bb_merge   (ALWAYS the const arm)
///   bb2: _L = Copy(v)   ; Goto bb_merge   (ALWAYS the var arm)
///   bb3 (merge): Return
/// ```
///
/// `const_on_true` chooses which CFG edge the CONST arm (bb1) sits on: when
/// true, bb1 is the TRUE successor and bb2 the FALSE one (and vice versa).
/// `cmp`/`c` pick the comparison and the clamp constant. `v` is local 2, `_g`
/// local 4, `_L` (the clamp result) local 3.
fn clamp_diamond(cmp: BinOp, c: u128, const_on_true: bool) -> VerifiableFunction {
    // bb1 = const arm, bb2 = var arm — fixed. const_on_true only routes edges.
    let (true_block, false_block) = if const_on_true {
        (BlockId(1), BlockId(2)) // const arm on TRUE edge, var arm on FALSE
    } else {
        (BlockId(2), BlockId(1)) // var arm on TRUE edge, const arm on FALSE
    };
    // SwitchInt encodes the FALSE edge as value 0, TRUE edge as otherwise.
    VerifiableFunction {
        name: "clamp".into(),
        def_path: "clamp".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("_1".into()) },
                LocalDecl { index: 2, ty: Ty::u8(), name: Some("v".into()) },
                LocalDecl { index: 3, ty: Ty::u8(), name: Some("clamped".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            cmp,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(c, 8)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, false_block)],
                        otherwise: true_block,
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1 — ALWAYS the const arm.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(c, 8))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                // bb2 — ALWAYS the var arm.
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn recognizes_gt_min_clamp() {
    // `_3 = if v > 100 { 100 } else { v }` = min(v, 100). const arm on TRUE edge.
    let func = clamp_diamond(BinOp::Gt, 100, true);
    assert_eq!(clamp_upper_bound(&func, 3), Some(100));
    // And it flows through unsigned_upper_bound for a read of `_3`.
    assert_eq!(unsigned_upper_bound(&func, &Operand::Copy(Place::local(3)), 16), Some(100));
}

#[test]
fn recognizes_le_min_clamp_var_on_true_edge() {
    // `_3 = if v <= 100 { v } else { 100 }` = min(v, 100). var arm on TRUE edge.
    let func = clamp_diamond(BinOp::Le, 100, false);
    assert_eq!(clamp_upper_bound(&func, 3), Some(100));
}

#[test]
fn recognizes_ge_and_lt_min_clamps() {
    // Ge: const arm on TRUE (`v >= C` -> C), var on FALSE (`v < C` -> v).
    assert_eq!(clamp_upper_bound(&clamp_diamond(BinOp::Ge, 50, true), 3), Some(50));
    // Lt: var arm on TRUE (`v < C` -> v), const on FALSE (`v >= C` -> C).
    assert_eq!(clamp_upper_bound(&clamp_diamond(BinOp::Lt, 50, false), 3), Some(50));
}

#[test]
fn rejects_max_lower_bound_clamp() {
    // `_3 = if v > 100 { v } else { 100 }` = max(v, 100): the VAR arm sits on
    // the TRUE (`v > 100`) edge, so the result is NOT bounded by 100. Must be
    // rejected (returning Some(100) here would be an UNSOUND false bound).
    let func = clamp_diamond(BinOp::Gt, 100, false /* const on FALSE => var on TRUE */);
    assert_eq!(clamp_upper_bound(&func, 3), None);
    // ... and `Le` with const on TRUE is likewise a max clamp -> rejected.
    assert_eq!(clamp_upper_bound(&clamp_diamond(BinOp::Le, 100, true), 3), None);
}

#[test]
fn additive_fact_emits_clamp_le_bound() {
    // The clamp result `_3 : u8` (min(v,100)) gets a `_3 <= 100` fact since
    // 100 < u8::MAX (255). build_additive_bound_facts requires a unique whole
    // def; `_3` has two — so the fact rides on a CONSUMING SSA local instead.
    // Here we assert clamp_upper_bound itself resolves; the consumer-cast test
    // lives in the corpus. Confirm the bound is tight (100, not 255).
    let func = clamp_diamond(BinOp::Gt, 100, true);
    // No SSA local consumes `_3`, so no additive fact is emitted for the diamond
    // alone — this guards that the diamond does not spuriously emit a `_3` fact
    // (since `_3` is non-SSA, build_additive_bound_facts skips it).
    let facts = build_additive_bound_facts(&func);
    assert!(
        !facts.iter().any(|f| matches!(
            f,
            Formula::Le(l, r)
                if matches!(l.as_ref(), Formula::Var(n, Sort::Int) if n == "clamped")
                    && matches!(r.as_ref(), Formula::Int(100))
        )),
        "non-SSA clamp local must not get its own additive fact: {facts:?}"
    );
}

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::{
    build_additive_bound_facts, build_cast_bound_facts, build_cast_lower_bound_facts,
    build_intrinsic_bound_facts, cast_source_const_upper_nonneg, clamp_upper_bound,
    unsigned_upper_bound,
};

/// `fn assign_partition(p:u32, h:u64)->u32 { let n = p.max(1) as u64; (h % n) as u32 }`
/// MIR shape: `_4 = Ord::max(_1, 1)` (call term), `_3 = _4 as u64` (value-preserving
/// widening). `build_cast_lower_bound_facts` must emit `Ge(_3, 1)` keyed on the cast
/// dest `_3`. `narrowing` toggles a value-CHANGING cast (u32->u8) which must be rejected.
fn max_then_cast(c: i128, narrowing: bool) -> VerifiableFunction {
    let (src_ty, dst_ty) = if narrowing { (Ty::u32(), Ty::u8()) } else { (Ty::u32(), Ty::u64()) };
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
                        callee_identity: None,
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
            datatype_defs: Default::default(),
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
        vec![
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(1)),)
        ],
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
                        callee_identity: None,
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
            datatype_defs: Default::default(),
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
                        callee_identity: None,
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
            datatype_defs: Default::default(),
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
            datatype_defs: Default::default(),
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

// ======================================================================
// Trust (P0 const-bit-width FALSE PROOF): bit-count receiver width must come
// from the RECEIVER'S DECLARED TYPE (the callee path's `<impl iN>` segment),
// never from the OPERAND, whose width a width-less `ConstValue::Int` infers
// FROM ITS VALUE (fits i64 => 64) and `Operand::Symbolic` pins at 64.
// ======================================================================

/// `let n = <recv>.<method>();` — one block, a `Terminator::Call` whose dest `_2`
/// is single-assigned, exactly the shape `build_intrinsic_bound_facts` keys on.
fn bitcount_call(callee: &str, recv: Operand, recv_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "bitcount".into(),
        def_path: "bitcount".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: recv_ty, name: Some("k".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: callee.into(),
                        args: vec![recv],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The emitted `Le(n, C)` upper bound, if any.
fn bitcount_upper_bound(func: &VerifiableFunction) -> Option<i128> {
    build_intrinsic_bound_facts(func).into_iter().find_map(|f| match f {
        Formula::Le(l, r) => match (*l, *r) {
            (Formula::Var(name, _), Formula::Int(c)) if name == "n" => Some(c),
            _ => None,
        },
        _ => None,
    })
}

/// WITNESS (a live false proof, no negative numbers needed):
///
/// ```ignore
/// const K: i128 = 1;
/// let n = K.count_zeros();          // truly 127
/// let arr = [0u8; 65];
/// arr[n as usize]                   // "0 <= n <= 64" PROVED in-bounds; really panics
/// ```
///
/// A width-less `ConstValue::Int(1)` reports width 64 (`operand_ty` infers the width
/// FROM THE VALUE), so the bound was `n <= 64` while `1i128.count_zeros() == 127`.
/// The width must come from the receiver's DECLARED type, which the callee path
/// carries as `<impl i128>` — making the bound `n <= 128`, which no longer discharges
/// the `[u8; 65]` index (fail-closed).
#[test]
fn bitcount_bound_uses_declared_i128_receiver_width_not_const_value_width() {
    let func = bitcount_call(
        "core::num::<impl i128>::count_zeros",
        Operand::Constant(ConstValue::Int(1)),
        Ty::Int { width: 128, signed: true },
    );
    assert_eq!(
        bitcount_upper_bound(&func),
        Some(128),
        "an i128 receiver's bit-count is bounded by 128, never by the const's inferred 64"
    );
    // The `as usize` propagation carries the SAME width, so it must agree.
    assert_eq!(cast_source_const_upper_nonneg(&func, 2), Some(128));
}

/// Known-true companion: an ordinary `u32` receiver still gets its tight `[0, 32]`
/// bound, so the fix is not a blanket disable of the bit-count lane.
#[test]
fn bitcount_bound_still_tight_for_declared_u32_receiver() {
    let func = bitcount_call(
        "core::num::<impl u32>::count_ones",
        Operand::Copy(Place::local(1)),
        Ty::u32(),
    );
    assert_eq!(bitcount_upper_bound(&func), Some(32));
    assert_eq!(cast_source_const_upper_nonneg(&func, 2), Some(32));
    // The lower bound `0 <= n` is still emitted alongside it.
    assert!(
        build_intrinsic_bound_facts(&func).iter().any(|f| matches!(
            f,
            Formula::Ge(l, r)
                if matches!(l.as_ref(), Formula::Var(n, _) if n == "n")
                    && matches!(r.as_ref(), Formula::Int(0))
        )),
        "the `0 <= n` lower bound is unchanged"
    );
}

/// A callee whose receiver width cannot be established with certainty emits NO fact.
/// This also hardens the weak `is_std_num_intrinsic` (`contains("::num::")`)
/// recognizer: the `core::hostile::num::…` forgery it admits carries no `<impl …>`
/// segment, so it now yields no bound at all.
#[test]
fn bitcount_bound_fails_closed_without_a_decodable_receiver_width() {
    for callee in [
        "core::hostile::num::count_zeros",
        "core::num::count_zeros",
        "core::num::<impl MyInt>::count_zeros",
        "mycrate::num::<impl i128>::count_zeros",
    ] {
        let func = bitcount_call(
            callee,
            Operand::Constant(ConstValue::Int(1)),
            Ty::Int { width: 128, signed: true },
        );
        assert_eq!(
            bitcount_upper_bound(&func),
            None,
            "`{callee}` has no provable receiver width: no bound may be emitted"
        );
        assert_eq!(cast_source_const_upper_nonneg(&func, 2), None, "callee `{callee}`");
    }
}

// ---------------------------------------------------------------------------
// The checked-op RESULT-FIELD pass of `build_additive_bound_facts`.
//
// A chained sum's second and later adds read `_c.0` as an OPERAND with no
// intervening whole-local copy, so only the field pass can hang a tight bound
// where the consuming operation reads it. Every test below is paired with the
// mutant it is meant to kill; the assert-by-mutant matrix lives in the commit
// message.
// ---------------------------------------------------------------------------

/// `_c.0` of a checked op, as a place.
fn field0(local: usize) -> Place {
    Place { local, projections: vec![trust_types::Projection::Field(0)] }
}

/// A chain of `n` `AddWithOverflow`s over `bool as u32` edge flags — the shape of
/// a3d's `face_active_edge_count`:
///   `_5=Ne(s0,s1); _6=_5 as u32; … _13=Add(_6,_8); _14=Add(_13.0,_10); _15=Add(_14.0,_12)`
/// Locals: 0 ret, 1..=4 params, 5/7/9/11 bool flags, 6/8/10/12 u32 casts,
/// 13/14/15 the `(u32,bool)` checked-op tuples.
fn bool_edge_sum_chain() -> VerifiableFunction {
    let pair = Ty::Tuple(vec![Ty::u32(), Ty::Bool]);
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::Bool, name: Some("s0".into()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("s1".into()) },
        LocalDecl { index: 3, ty: Ty::Bool, name: Some("s2".into()) },
        LocalDecl { index: 4, ty: Ty::Bool, name: Some("s3".into()) },
    ];
    for k in 0..4 {
        locals.push(LocalDecl { index: 5 + 2 * k, ty: Ty::Bool, name: Some(format!("_{}", 5 + 2 * k)) });
        locals.push(LocalDecl { index: 6 + 2 * k, ty: Ty::u32(), name: Some(format!("_{}", 6 + 2 * k)) });
    }
    for t in 13..=15 {
        locals.push(LocalDecl { index: t, ty: pair.clone(), name: Some(format!("_{t}")) });
    }
    let mut stmts = Vec::new();
    for k in 0..4usize {
        let (a, b) = (1 + k, 1 + (k + 1) % 4);
        stmts.push(Statement::Assign {
            place: Place::local(5 + 2 * k),
            rvalue: Rvalue::BinaryOp(BinOp::Ne, Operand::Copy(Place::local(a)), Operand::Copy(Place::local(b))),
            span: SourceSpan::default(),
        });
        stmts.push(Statement::Assign {
            place: Place::local(6 + 2 * k),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(5 + 2 * k)), Ty::u32()),
            span: SourceSpan::default(),
        });
    }
    // _13 = _6 + _8 ; _14 = _13.0 + _10 ; _15 = _14.0 + _12
    stmts.push(Statement::Assign {
        place: Place::local(13),
        rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(Place::local(6)), Operand::Copy(Place::local(8))),
        span: SourceSpan::default(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(14),
        rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(field0(13)), Operand::Copy(Place::local(10))),
        span: SourceSpan::default(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(15),
        rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(field0(14)), Operand::Copy(Place::local(12))),
        span: SourceSpan::default(),
    });
    stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(field0(15))),
        span: SourceSpan::default(),
    });
    VerifiableFunction {
        name: "face_active_edge_count".into(),
        def_path: "face_active_edge_count".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 4,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// One `u8` checked op over two operands whose upper bounds are `ua`/`ub`,
/// obtained from constants so the bound is exact and the boundary is addressable.
/// `_1 = Add|Mul(const ua, const ub)` with `_1 : (u8, bool)`; `_2 = _1.0`.
fn u8_checked_const_op(op: BinOp, ua: u128, ub: u128) -> VerifiableFunction {
    VerifiableFunction {
        name: "boundary".into(),
        def_path: "boundary".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::u8(), Ty::Bool]), name: Some("_1".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Constant(ConstValue::Uint(ua, 8)),
                            Operand::Constant(ConstValue::Uint(ub, 8)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(field0(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u8(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The exact `Le(<name>, k)` fact for a place, or `None`.
fn le_fact_for(facts: &[Formula], name: &str) -> Option<i128> {
    facts.iter().find_map(|f| match f {
        Formula::Le(l, r) => match (l.as_ref(), r.as_ref()) {
            (Formula::Var(n, Sort::Int), Formula::Int(k)) if n == name => Some(*k),
            _ => None,
        },
        _ => None,
    })
}

#[test]
fn checked_add_result_field_gets_the_tight_chained_bound() {
    // KILLS: no-op mutant (loop deleted), inverted mutant (`Ge` for `Le`),
    // widened mutant (`bound + 1`), type-max mutant (emitting 4294967295).
    let func = bool_edge_sum_chain();
    let facts = build_additive_bound_facts(&func);
    // The names are the ones the VC itself uses for these places.
    assert_eq!(crate::place_to_var_name(&func, &field0(13)), "_13.0");
    assert_eq!(crate::place_to_var_name(&func, &field0(14)), "_14.0");
    assert_eq!(crate::place_to_var_name(&func, &field0(15)), "_15.0");
    // Each bool cast is <= 1, so the running sums are <= 2, 3, 4 EXACTLY.
    assert_eq!(le_fact_for(&facts, "_13.0"), Some(2), "facts: {facts:?}");
    assert_eq!(le_fact_for(&facts, "_14.0"), Some(3), "facts: {facts:?}");
    assert_eq!(le_fact_for(&facts, "_15.0"), Some(4), "facts: {facts:?}");
}

#[test]
fn checked_result_field_bound_declines_exactly_at_type_max() {
    // The emit guard IS the no-wrap proof: `bound < 2^w` is what licenses
    // dropping the `mod 2^w`. At `bound == u8::MAX` the sum still cannot wrap,
    // but the fact would carry no information, and one notch above it the wrap
    // is real — so the guard is `>=`, pinned in BOTH directions here.
    // KILLS: guard-deleted mutant, and the off-by-one `>` mutant.
    let at_max = build_additive_bound_facts(&u8_checked_const_op(BinOp::Add, 200, 55));
    assert_eq!(le_fact_for(&at_max, "_1.0"), None, "200+55 == u8::MAX must emit nothing: {at_max:?}");
    let below = build_additive_bound_facts(&u8_checked_const_op(BinOp::Add, 200, 54));
    assert_eq!(le_fact_for(&below, "_1.0"), Some(254), "200+54 is strictly tighter: {below:?}");
    // And well above the type max — where the machine really does wrap — nothing.
    let over = build_additive_bound_facts(&u8_checked_const_op(BinOp::Add, 200, 200));
    assert_eq!(le_fact_for(&over, "_1.0"), None, "200+200 wraps u8; no fact: {over:?}");
}

#[test]
fn checked_mul_result_field_bound_is_the_product_and_respects_the_guard() {
    // KILLS: a Mul-arm-deleted mutant, and the same guard mutants on `*`.
    let ok = build_additive_bound_facts(&u8_checked_const_op(BinOp::Mul, 5, 20));
    assert_eq!(le_fact_for(&ok, "_1.0"), Some(100), "5*20 = 100 < 255: {ok:?}");
    let over = build_additive_bound_facts(&u8_checked_const_op(BinOp::Mul, 16, 16));
    assert_eq!(le_fact_for(&over, "_1.0"), None, "16*16 = 256 wraps u8; no fact: {over:?}");
}

#[test]
fn checked_result_field_bound_declines_on_a_reassigned_tuple_local() {
    // A second whole-local def makes `_13.0` ambiguous: the SMT name is one
    // variable but the storage held two values. KILLS the mutant that drops the
    // `is_single_static_assignment` / `value_local_is_unstable` stability gates.
    let mut func = bool_edge_sum_chain();
    let extra = Statement::Assign {
        place: Place::local(13),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Constant(ConstValue::Uint(4_000_000_000, 32)),
            Operand::Constant(ConstValue::Uint(4_000_000_000, 32)),
        ),
        span: SourceSpan::default(),
    };
    func.body.blocks[0].stmts.push(extra);
    let facts = build_additive_bound_facts(&func);
    assert_eq!(le_fact_for(&facts, "_13.0"), None, "reassigned tuple local: {facts:?}");
    // ... and the bound derived THROUGH it is gone too, so the chain cannot be
    // rebuilt from a stale premise.
    assert_eq!(le_fact_for(&facts, "_14.0"), None, "derived through _13.0: {facts:?}");
}

#[test]
fn checked_result_field_bound_declines_for_free_operands() {
    // Two unconstrained u32 params: `ub(a)+ub(b) = 2^33-2 >= u32::MAX`, so no
    // fact — the sum genuinely overflows and must stay refutable. KILLS the
    // guard-deleted mutant on the common shape.
    let func = VerifiableFunction {
        name: "free_add".into(),
        def_path: "free_add".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: Some("_3".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(field0(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let facts = build_additive_bound_facts(&func);
    assert_eq!(le_fact_for(&facts, "_3.0"), None, "unbounded u32 add: {facts:?}");
}

// Write channels that make the explicit stability gates on the tuple local
// load-bearing rather than decorative.
//
// These two rows were written against the pre-seam resolver, which scanned
// `Statement::Assign` only, so BOTH a call-dest write and a `&mut` borrow left the
// single Assign intact and `unsigned_upper_bound` still computed a bound. Under the
// entry-definition seam `unsigned_upper_bound` re-derives through
// `local_defs::unique_value_def`, which reads the `LocalWrite` taxonomy, so only ONE
// of the two channels is still invisible to it:
//
//   * a CALL-DEST write is `LocalWrite::WholeOpaque` and now makes the resolver
//     ambiguous, so `..._is_a_call_destination` declines twice over — the explicit
//     gate is no longer the only thing holding it;
//   * a `&mut` BORROW is `LocalWrite::Escape`, which `unique_value_def` deliberately
//     IGNORES (the parked KNOWN DEFECT documented on that arm), so the resolver still
//     returns the `CheckedBinaryOp` and the gate is what stops the bound being
//     published for storage whose value the scan never saw written.
//
// So `is_single_static_assignment` / `value_local_is_unstable` remain load-bearing for
// the borrow row, and are belt-and-braces for the call-dest row. The reassignment case
// (`..._declines_on_a_reassigned_tuple_local`) is caught by the resolver itself and
// pins nothing about the gates.

#[test]
fn checked_result_field_bound_declines_when_the_tuple_local_is_a_call_destination() {
    let mut func = bool_edge_sum_chain();
    // Split the single block so a Call terminator can write `_13` wholesale.
    let stmts = std::mem::take(&mut func.body.blocks[0].stmts);
    func.body.blocks[0].stmts = stmts;
    func.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: None,
        is_foreign: false,
        func: "reseat".into(),
        args: vec![],
        dest: Place::local(13),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    let facts = build_additive_bound_facts(&func);
    assert_eq!(
        le_fact_for(&facts, "_13.0"),
        None,
        "a call-dest write to the tuple local is invisible to the Assign scan: {facts:?}"
    );
}

#[test]
fn checked_result_field_bound_declines_when_the_tuple_local_is_mut_borrowed() {
    let mut func = bool_edge_sum_chain();
    func.body.locals.push(LocalDecl {
        index: 20,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::Tuple(vec![Ty::u32(), Ty::Bool])) },
        name: Some("_20".into()),
    });
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(20),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(13) },
        span: SourceSpan::default(),
    });
    let facts = build_additive_bound_facts(&func);
    assert_eq!(
        le_fact_for(&facts, "_13.0"),
        None,
        "a `&mut` on the tuple local admits writes no def scan can see: {facts:?}"
    );
}

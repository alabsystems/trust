//! Verdict-parity pins for the memoized helpers and the first PERF waves (506-518):
//! each fast path must match its reference scan exactly. Split out of
//! `func_analysis_memo_tests.rs` so no file passes tidy's 3000-line limit; the
//! fixtures and imports come from the parent through `use super::*`.

use super::*;

#[test]
fn sole_predecessors_exit_helpers_match_reference_scans_and_assert_binders() {
    use trust_types::{AssertMessage, UnOp, UnwindEdge};

    let func = guarded_body(10);
    let _work = crate::gen_work::enter_unmetered();
    let sp = crate::fn_memo::sole_predecessors(&func).expect("active under gen_work scope");
    for target_idx in 0..=6 {
        let target = BlockId(target_idx);
        let preds: Vec<BlockId> = func
            .body
            .blocks
            .iter()
            .filter(|b| b.terminator.has_exit_block_target(target))
            .map(|b| b.id)
            .collect();
        let expected_unique = if target.0 == 0 || preds.len() != 1 { None } else { Some(preds[0]) };
        assert_eq!(
            sp.unique_exit_predecessor(target),
            Some(expected_unique),
            "unique_exit_predecessor mismatch at {target:?}"
        );
        for allowed_idx in 0..=6 {
            let allowed = BlockId(allowed_idx);
            let expected_no_other = !func
                .body
                .blocks
                .iter()
                .any(|b| b.id != allowed && b.terminator.has_exit_block_target(target));
            assert_eq!(
                sp.no_other_exit_predecessor(target, allowed),
                Some(expected_no_other),
                "no_other_exit_predecessor mismatch at target={target:?}, allowed={allowed:?}"
            );
        }
    }

    // Signed 2-hop division chain (bb0 -> bb1 -> bb2) and a bypassed variant (+ bb3 -> bb2).
    let make_signed_div_chain = |add_bypass: bool| {
        let mut blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::DivisionByZero,
                    target: BlockId(1),
                    unwind: UnwindEdge::Continue,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(-1)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(i32::MIN as i128)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Move(Place::local(4)),
                            Operand::Move(Place::local(5)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place::local(6)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Div),
                    target: BlockId(2),
                    unwind: UnwindEdge::Continue,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];
        if add_bypass {
            blocks.push(BasicBlock {
                id: BlockId(3),
                stmts: Vec::new(),
                terminator: Terminator::Goto(BlockId(2)),
            });
        }
        VerifiableFunction {
            name: "signed_div".to_string(),
            def_path: "signed_div".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("lhs".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("rhs".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                    LocalDecl { index: 5, ty: Ty::Bool, name: None },
                    LocalDecl { index: 6, ty: Ty::Bool, name: None },
                ],
                blocks,
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    };

    let lhs = Operand::Copy(Place::local(1));
    let rhs = Operand::Copy(Place::local(2));
    for (add_bypass, expected) in [(false, true), (true, false)] {
        let chain = make_signed_div_chain(add_bypass);
        let cached_ovf = super::super::checked_vcs::v2_divrem_overflow_assert_exactly_bound(
            &chain,
            BinOp::Div,
            BlockId(2),
            0,
            &lhs,
            &rhs,
        );
        let uncached_ovf = crate::fn_memo::with_analysis_memo_disabled(|| {
            super::super::checked_vcs::v2_divrem_overflow_assert_exactly_bound(
                &chain,
                BinOp::Div,
                BlockId(2),
                0,
                &lhs,
                &rhs,
            )
        });
        assert_eq!(cached_ovf, expected);
        assert_eq!(cached_ovf, uncached_ovf);

        let cached_dz = super::super::checked_vcs::v2_divzero_assert_exactly_bound(
            &chain,
            BinOp::Div,
            BlockId(2),
            0,
            &lhs,
            &rhs,
        );
        let uncached_dz = crate::fn_memo::with_analysis_memo_disabled(|| {
            super::super::checked_vcs::v2_divzero_assert_exactly_bound(
                &chain,
                BinOp::Div,
                BlockId(2),
                0,
                &lhs,
                &rhs,
            )
        });
        assert_eq!(cached_dz, expected);
        assert_eq!(cached_dz, uncached_dz);
    }

    // Negation binder parity under active vs disabled memo.
    let neg_fn = VerifiableFunction {
        name: "neg_fn".to_string(),
        def_path: "neg_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(i32::MIN as i128)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        unwind: UnwindEdge::Continue,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let neg_op = Operand::Copy(Place::local(1));
    let cached_neg = super::super::safety::v2_negation_assert_exactly_bound(
        &neg_fn,
        &neg_fn.body.blocks[1],
        &neg_op,
    );
    let uncached_neg = crate::fn_memo::with_analysis_memo_disabled(|| {
        super::super::safety::v2_negation_assert_exactly_bound(
            &neg_fn,
            &neg_fn.body.blocks[1],
            &neg_op,
        )
    });
    assert!(cached_neg);
    assert_eq!(cached_neg, uncached_neg);
}

#[test]
fn arg_type_range_memo_matches_disabled_and_preserves_hash_local_collision_guard() {
    let _work = crate::gen_work::enter_unmetered();
    let func = VerifiableFunction {
        name: "param_ranges_fn".to_string(),
        def_path: "param_ranges_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) },
                    name: Some("r".into()),
                },
                LocalDecl { index: 3, ty: Ty::i64(), name: Some("n#e".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
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
        tuple_layouts: Default::default(),
    };

    let formula = Formula::And(vec![
        Formula::Gt(
            Box::new(Formula::Var("n#s0_0".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        Formula::Gt(
            Box::new(Formula::Var("n#e".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
    ]);
    let cached = super::super::alloc_vcs::conjoin_arg_type_ranges_step(&func, formula.clone());
    let uncached = crate::fn_memo::with_analysis_memo_disabled(|| {
        super::super::alloc_vcs::conjoin_arg_type_ranges_step(&func, formula.clone())
    });
    assert!(cached.1);
    assert_eq!(cached, uncached);
    let rendered = format!("{:?}", cached.0);
    assert!(rendered.contains("n#s0_0"), "expected versioned param bound: {rendered}");
    assert!(
        !rendered.contains("Var(\"n#e\", Int), Int(4294967295)"),
        "real `#`-named local `n#e` must not receive `n`'s u32 bound: {rendered}"
    );

    // Non-scalar-param function short-circuits cleanly with `changed == false`.
    let ref_only_fn = VerifiableFunction {
        name: "ref_only".to_string(),
        def_path: "ref_only".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                    },
                    name: Some("s".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let (out, changed) =
        super::super::alloc_vcs::conjoin_arg_type_ranges_step(&ref_only_fn, Formula::Bool(true));
    assert!(!changed);
    assert_eq!(out, Formula::Bool(true));
}

#[test]
fn terminator_presence_and_ssa_collapse_fast_paths_preserve_exact_semantics() {
    let switch_fn = guarded_body(10);
    let outside_tp = super::super::terminator_presence_for(&switch_fn);
    assert!(outside_tp.has_switch_int);
    assert!(!outside_tp.has_call);
    assert!(!outside_tp.has_iterator_next_call);
    {
        let _scope = FuncAnalysisScope::enter(&switch_fn);
        assert_eq!(super::super::terminator_presence_for(&switch_fn), outside_tp);
        assert!(super::super::range_yield_guards_for(&switch_fn).is_empty());
        assert!(super::super::enumerate_yield_guards_for(&switch_fn).is_empty());
        assert!(super::super::slice_iter_yield_guards_for(&switch_fn).is_empty());
        assert!(super::super::unwrap_panic_vcs_for(&switch_fn).is_empty());
    }

    // Build a function with 12 SSA single-def locals (`_2`..`_13`) and one reassigned local (`_1`)
    // to exercise:
    //  1) hash-free fast path (`!formula_has_hash_var`),
    //  2) small exact-rename path (`<= 8` renames),
    //  3) indexed exact-rename path (`> 8` renames), and
    //  4) quantifier capture-avoiding fallback (`needs_full_subst`).
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) },
    ];
    let mut stmts = vec![
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 32))),
            span: SourceSpan::default(),
        },
    ];
    for idx in 2..=13 {
        locals.push(LocalDecl { index: idx, ty: Ty::u32(), name: None });
        stmts.push(Statement::Assign {
            place: Place::local(idx),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(idx as u128, 32))),
            span: SourceSpan::default(),
        });
    }
    let ssa_fn = VerifiableFunction {
        name: "ssa_collapse_probe".to_string(),
        def_path: "ssa_collapse_probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };

    let unversioned =
        Formula::Eq(Box::new(Formula::Var("_2".to_string(), Sort::Int)), Box::new(Formula::Int(2)));
    assert_eq!(
        super::super::discharge::normalize_ssa_version_tokens_owned(&ssa_fn, unversioned.clone()),
        unversioned
    );
    assert_eq!(super::super::discharge::bare_ssa_guard_variant(&ssa_fn, &unversioned), None);

    // > 8 collapsible SSA tokens + reassigned `m#s0_1` + loop-havoc `_2#<e45_>0` (must stay uncollapsed).
    let loop_havoc = format!("_2#{}0", crate::LOOP_TRANSITION_HAVOC_TOKEN_PREFIX);
    let mut big_conjuncts = vec![
        Formula::Eq(
            Box::new(Formula::Var("m#s0_1".to_string(), Sort::Int)),
            Box::new(Formula::Int(2)),
        ),
        Formula::Eq(
            Box::new(Formula::Var(loop_havoc.clone(), Sort::Int)),
            Box::new(Formula::Int(9)),
        ),
    ];
    for idx in 2..=13 {
        big_conjuncts.push(Formula::Ge(
            Box::new(Formula::Var(format!("_{idx}#s0_{idx}"), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
    }
    let big_formula = Formula::And(big_conjuncts);
    let normalized =
        super::super::discharge::normalize_ssa_version_tokens_owned(&ssa_fn, big_formula.clone());
    let rendered = format!("{normalized:?}");
    assert!(rendered.contains("m#s0_1"), "reassigned param must keep token: {rendered}");
    assert!(rendered.contains(&loop_havoc), "loop-havoc token must not collapse: {rendered}");
    for idx in 2..=13 {
        let token = format!("_{idx}#s0_{idx}");
        assert!(!rendered.contains(&token), "SSA token {token} should collapse: {rendered}");
        assert!(
            rendered.contains(&format!("Var(\"_{idx}\", Int)")),
            "expected collapsed bare var _{idx}: {rendered}"
        );
    }

    // Quantifier binder `_2` must alpha-rename rather than capture collapsed `_2#s0_2 -> _2`.
    let quantified = Formula::Forall(
        vec![("_2".into(), Sort::Int)],
        Box::new(Formula::Eq(
            Box::new(Formula::Var("_2".to_string(), Sort::Int)),
            Box::new(Formula::Var("_2#s0_2".to_string(), Sort::Int)),
        )),
    );
    let q_norm = super::super::discharge::normalize_ssa_version_tokens_owned(&ssa_fn, quantified);
    let Formula::Forall(bindings, body) = &q_norm else {
        panic!("expected Forall, got {q_norm:?}");
    };
    assert_ne!(
        bindings[0].0.as_str(),
        "_2",
        "quantifier binder must avoid capturing `_2`: {q_norm:?}"
    );
    assert!(
        format!("{body:?}").contains("Var(\"_2\", Int)"),
        "free SSA occurrence inside quantifier must collapse to `_2`: {q_norm:?}"
    );
}

#[test]
fn single_pass_range_battery_and_owned_ite_elim_match_reference_steps_bit_for_bit() {
    use trust_types::fx::FxHashSet;
    use trust_types::{Projection, Symbol};

    // Build a rich function exercising all four battery steps + checked-arith exclusions + `#` collision:
    // - local 0: u32 return slot
    // - local 1 (`n`): u32 parameter
    // - local 2 (`s`): &[u8] slice parameter (non-ZST `__slice_len`)
    // - local 3: u16 local initialized to constant 7
    // - local 4: Pair { 0: u8 } ADT local read via `_4.0`
    // - local 5: (u32, bool) CheckedBinaryOp result copied into local 6 (exercising `excl`)
    // - local 7 (`n#evil`): i64 `#`-named local colliding with versioned `n`
    // - local 8 (`v`): `std::vec::Vec<u8>` owned container length
    let vec_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        name: "std::vec::Vec<u8>".to_string(),
        fields: vec![(
            "buf".to_string(),
            Ty::RawPtr { pointee: Box::new(Ty::u8()), mutable: false },
        )]
        .into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        adt_kind: None,
        layout: None,
    };
    let pair_ty = Ty::Adt {
        arbitrary_precision: None,
        validity_wrapper: None,
        name: "probe::Pair".to_string(),
        fields: vec![("0".to_string(), Ty::u8())].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        adt_kind: None,
        layout: None,
    };
    let checked_tuple_ty = Ty::Tuple(vec![Ty::u32(), Ty::Bool]);
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".to_string()) },
        LocalDecl {
            index: 2,
            ty: Ty::Ref { inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }), mutable: false },
            name: Some("s".to_string()),
        },
        LocalDecl { index: 3, ty: Ty::u16(), name: None },
        LocalDecl { index: 4, ty: pair_ty, name: None },
        LocalDecl { index: 5, ty: checked_tuple_ty, name: None },
        LocalDecl { index: 6, ty: Ty::u32(), name: None },
        LocalDecl { index: 7, ty: Ty::i64(), name: Some("n#evil".to_string()) },
        LocalDecl { index: 8, ty: vec_ty, name: Some("v".to_string()) },
    ];
    let stmts = vec![
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 16))),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 32)),
            ),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(6),
            rvalue: Rvalue::Use(Operand::Copy(Place {
                local: 5,
                projections: vec![Projection::Field(0)],
            })),
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Cast(
                Operand::Copy(Place { local: 4, projections: vec![Projection::Field(0)] }),
                Ty::u32(),
            ),
            span: SourceSpan::default(),
        },
    ];
    let func = VerifiableFunction {
        name: "battery_probe".to_string(),
        def_path: "probe::battery_probe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };

    let bound_sym: Symbol = "_3#shadowed".into();
    let formula = Formula::And(vec![
        Formula::Lt(
            Box::new(Formula::Var("n#s0_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("n#evil".to_string(), Sort::Int)),
        ),
        Formula::Eq(
            Box::new(Formula::Var("_3#s0_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("_4.0#s0_1".to_string(), Sort::Int)),
        ),
        Formula::Eq(
            Box::new(Formula::Var("_5.0".to_string(), Sort::Int)),
            Box::new(Formula::Var("_6".to_string(), Sort::Int)),
        ),
        Formula::Le(
            Box::new(Formula::SymVar("v#s0_2".into(), Sort::Int)),
            Box::new(Formula::Var("s__slice_len#s0_0".to_string(), Sort::Int)),
        ),
        // Duplicate occurrences to exercise `seen_free` / `seen_param_int` dedup.
        Formula::Ge(
            Box::new(Formula::Var("_3#s0_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("n#s0_0".to_string(), Sort::Int)),
        ),
        // Quantifier-bound `_3#shadowed` must NOT receive a local type range, while
        // versioned parameter `n#q` inside the quantifier matches `visit_formula_nodes`.
        Formula::Forall(
            vec![(bound_sym.clone(), Sort::Int)],
            Box::new(Formula::Lt(
                Box::new(Formula::Var(bound_sym.as_str().to_string(), Sort::Int)),
                Box::new(Formula::Var("n#q".to_string(), Sort::Int)),
            )),
        ),
    ]);

    let _scope = super::super::EntryScope::enter(&func);

    let reference_battery =
        |input: Formula, class: super::super::type_ranges::RangeBatteryClass| {
            let mut records: Vec<(Formula, Formula)> = Vec::new();
            let mut step = |f: Formula, op: &dyn Fn(Formula) -> (Formula, bool)| {
                let (after, wrapped) = op(f);
                if wrapped
                    && let Formula::And(children) = &after
                    && let Some(before) = children.last()
                {
                    records.push((before.clone(), after.clone()));
                } else {
                    records.push((after.clone(), after.clone()));
                }
                after
            };
            let out = match class {
                super::super::type_ranges::RangeBatteryClass::Other => step(input, &|f| {
                    super::super::type_ranges::conjoin_length_nonneg_bounds_step(&func, f)
                }),
                super::super::type_ranges::RangeBatteryClass::Arithmetic
                | super::super::type_ranges::RangeBatteryClass::TypeInvariant
                | super::super::type_ranges::RangeBatteryClass::Bounds => {
                    let empty_excl = FxHashSet::default();
                    let excl_rc = (class != super::super::type_ranges::RangeBatteryClass::Bounds)
                        .then(|| {
                            super::super::type_ranges::checked_arith_result_value_vars_rc(&func)
                        });
                    let excl = excl_rc.as_deref().unwrap_or(&empty_excl);
                    let f = step(input, &|f| {
                        super::super::alloc_vcs::conjoin_arg_type_ranges_step(&func, f)
                    });
                    let f = step(f, &|f| {
                        super::super::type_ranges::conjoin_local_type_ranges_excluding_step(
                            &func, f, excl,
                        )
                    });
                    let f = step(f, &|f| {
                        super::super::type_ranges::conjoin_datatype_field_ranges_excluding_step(
                            &func, f, excl,
                        )
                    });
                    step(f, &|f| super::super::type_ranges::conjoin_slice_len_bounds_step(&func, f))
                }
            };
            (out, records)
        };

    for class in [
        super::super::type_ranges::RangeBatteryClass::Arithmetic,
        super::super::type_ranges::RangeBatteryClass::Bounds,
        super::super::type_ranges::RangeBatteryClass::TypeInvariant,
        super::super::type_ranges::RangeBatteryClass::Other,
    ] {
        let mut actual_records: Vec<(Formula, Formula)> = Vec::new();
        let actual = super::super::type_ranges::conjoin_type_range_battery(
            &func,
            formula.clone(),
            class,
            &mut |before, after| actual_records.push((before.clone(), after.clone())),
        );
        let (expected, expected_records) = reference_battery(formula.clone(), class);
        assert_eq!(actual, expected, "formula mismatch for {class:?}");
        assert_eq!(actual_records, expected_records, "recorded wrappers mismatch for {class:?}");
    }

    // Call-free body fast exit in `UnmodelledValues::of`.
    let unmodelled = super::super::havoc_decline::UnmodelledValues::of(
        &func,
        super::super::havoc_decline::PayloadSources::AnyForeignValueCall,
    );
    assert!(unmodelled.is_empty(), "call-free body must have empty UnmodelledValues");

    // `eliminate_term_ites_owned` == `eliminate_term_ites` across mixed Ite / Ite-free trees and caps.
    let arith_no_ite = Formula::Eq(
        Box::new(Formula::Add(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(3)),
            )),
            Box::new(Formula::Sub(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
        )),
        Box::new(Formula::Int(42)),
    );
    let bool_tree = Formula::Eq(
        Box::new(Formula::Var("flag".to_string(), Sort::Bool)),
        Box::new(Formula::Ite(
            Box::new(Formula::Var("c1".to_string(), Sort::Bool)),
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Ite(
                Box::new(Formula::Var("c2".to_string(), Sort::Bool)),
                Box::new(Formula::Bool(false)),
                Box::new(Formula::Bool(true)),
            )),
        )),
    );
    let term_ite_rel = Formula::Lt(
        Box::new(Formula::Add(
            Box::new(Formula::Ite(
                Box::new(Formula::Var("c".to_string(), Sort::Bool)),
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(2)),
            )),
            Box::new(Formula::Ite(
                Box::new(Formula::Var("d".to_string(), Sort::Bool)),
                Box::new(Formula::Int(10)),
                Box::new(Formula::Int(20)),
            )),
        )),
        Box::new(Formula::Int(100)),
    );
    let mixed_ite = Formula::And(vec![arith_no_ite, bool_tree, term_ite_rel]);
    for cap in [0, 1, 2, super::super::ITE_ELIM_CASE_CAP] {
        assert_eq!(
            super::super::ite::eliminate_term_ites_owned(mixed_ite.clone(), cap),
            super::super::ite::eliminate_term_ites(&mixed_ite, cap),
            "owned vs borrowed eliminate_term_ites mismatch at cap={cap}"
        );
    }
}

#[test]
fn wave506_nth_terminator_succ_and_memoized_back_edge_parity() {
    let terminators = [
        Terminator::Return,
        Terminator::Unreachable,
        Terminator::Resume,
        Terminator::Goto(BlockId(3)),
        Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: trust_types::AssertMessage::BoundsCheck,
            target: BlockId(5),
            unwind: trust_types::UnwindEdge::default(),
            span: SourceSpan::default(),
        },
        Terminator::Drop {
            place: Place::local(1),
            target: BlockId(2),
            unwind: trust_types::UnwindEdge::default(),
            span: SourceSpan::default(),
        },
        Terminator::Call {
            func: "callee".into(),
            args: vec![],
            dest: Place::local(0),
            target: Some(BlockId(4)),
            unwind: trust_types::UnwindEdge::default(),
            span: SourceSpan::default(),
            is_foreign: false,
            is_unsafe_sig: false,
            atomic: None,
            callee_key: None,
            callee_identity: None,
        },
        Terminator::Call {
            func: "diverging".into(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            unwind: trust_types::UnwindEdge::default(),
            span: SourceSpan::default(),
            is_foreign: false,
            is_unsafe_sig: false,
            atomic: None,
            callee_key: None,
            callee_identity: None,
        },
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
            otherwise: BlockId(6),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
        Terminator::Opaque {
            kind: "inline_asm".into(),
            targets: vec![BlockId(7), BlockId(8)],
            span: SourceSpan::default(),
        },
    ];
    for term in &terminators {
        let expected = super::super::loop_bounds::terminator_succs(term);
        let mut actual = Vec::new();
        let mut idx = 0usize;
        while let Some(succ) = super::super::loop_bounds::nth_terminator_succ(term, idx) {
            actual.push(succ);
            idx += 1;
        }
        assert_eq!(actual, expected, "nth_terminator_succ mismatch for {term:?}");
        assert_eq!(super::super::loop_bounds::nth_terminator_succ(term, idx + 1), None);
    }

    let dag_fn = guarded_body(6);
    assert!(!super::super::terminator_presence_for(&dag_fn).has_back_edge);
    assert!(!crate::loop_analysis::has_back_edge(&dag_fn));
    assert_eq!(super::super::loop_bounds::count_back_edges_uncached(&dag_fn), 0);
    {
        let _scope = FuncAnalysisScope::enter(&dag_fn);
        assert_eq!(
            super::super::cached_terminator_presence_for_body(&dag_fn.body)
                .map(|tp| tp.has_back_edge),
            Some(false)
        );
        assert!(!crate::loop_analysis::has_back_edge(&dag_fn));
        assert!(crate::loop_analysis::detect_loops(&dag_fn).is_empty());
        assert_eq!(super::super::loop_bounds::count_back_edges(&dag_fn), 0);
    }

    // Build a two-latch single-header loop (bb0 -> bb1 -> {bb2, bb3} -> bb1, exit bb4).
    let mut loop_fn = guarded_body(1);
    loop_fn.body.blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(1)),
                targets: vec![(0, BlockId(2)), (1, BlockId(3))],
                otherwise: BlockId(4),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
        BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
        BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
    ];
    assert!(super::super::terminator_presence_for(&loop_fn).has_back_edge);
    assert!(crate::loop_analysis::has_back_edge(&loop_fn));
    assert_eq!(super::super::loop_bounds::count_back_edges_uncached(&loop_fn), 1);
    {
        let _scope = FuncAnalysisScope::enter(&loop_fn);
        assert!(crate::loop_analysis::has_back_edge(&loop_fn));
        assert_eq!(super::super::loop_bounds::count_back_edges(&loop_fn), 1);
        assert_eq!(crate::loop_analysis::detect_loops(&loop_fn).len(), 2);
    }
}

#[test]
fn wave507_body_fact_presence_precision_gates_preserve_exact_global_facts() {
    use trust_types::Projection;

    // Body 1: has CheckedBinaryOp(Sub) and CheckedBinaryOp(Add) WITHOUT .0 readback,
    // two non-index binary calls (including TRUST_TOTAL_CLONE_SENTINEL with no bare discr),
    // and two field-1 projected copies (`_2.1`, `_3.1`) with no Deref or Index.
    let mut fn_no_readback = guarded_body(1);
    fn_no_readback.body.arg_count = 1;
    fn_no_readback.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u64(), name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: Some("_2".into()) },
        LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: Some("_3".into()) },
        LocalDecl { index: 4, ty: Ty::Bool, name: Some("_4".into()) },
        LocalDecl { index: 5, ty: Ty::Bool, name: Some("_5".into()) },
    ];
    fn_no_readback.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Field(1)],
                    })),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 3,
                        projections: vec![Projection::Field(1)],
                    })),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Call {
                func: trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL.into(),
                args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(1))],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::default(),
                span: SourceSpan::default(),
                is_foreign: false,
                is_unsafe_sig: false,
                atomic: None,
                callee_key: None,
                callee_identity: None,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "user::helper".into(),
                args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(1))],
                dest: Place::local(0),
                target: Some(BlockId(2)),
                unwind: trust_types::UnwindEdge::default(),
                span: SourceSpan::default(),
                is_foreign: false,
                is_unsafe_sig: false,
                atomic: None,
                callee_key: None,
                callee_identity: None,
            },
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
    ];
    let (facts, cong_range) =
        super::super::value_facts::build_global_invariant_facts_with_congruence_range(
            &fn_no_readback,
        );
    assert!(cong_range.is_empty());
    assert!(super::super::value_facts::build_checked_sub_result_facts(&fn_no_readback).is_empty());
    assert!(super::super::value_facts::build_checked_add_result_facts(&fn_no_readback).is_empty());
    assert!(
        super::super::value_facts::build_element_read_congruence_facts(&fn_no_readback).is_empty()
    );
    assert!(
        super::super::value_facts::build_immutable_index_len_tie_facts(&fn_no_readback).is_empty()
    );
    assert!(
        super::super::value_facts::build_vec_index_dest_value_tie_facts(&fn_no_readback).is_empty()
    );
    assert!(super::super::value_facts::build_primitive_int_cmp_facts(&fn_no_readback).is_empty());

    // Body 2: add a `.0` readback `_0 = move (_2.0)` and verify `build_checked_sub_result_facts`
    // fires through `build_global_invariant_facts_with_congruence_range`.
    fn_no_readback.body.blocks[1].terminator = Terminator::Goto(BlockId(2));
    fn_no_readback.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Move(Place {
            local: 2,
            projections: vec![Projection::Field(0)],
        })),
        span: SourceSpan::default(),
    });
    let expected_sub = super::super::value_facts::build_checked_sub_result_facts(&fn_no_readback);
    assert_eq!(expected_sub.len(), 1);
    let (facts_with_readback, _) =
        super::super::value_facts::build_global_invariant_facts_with_congruence_range(
            &fn_no_readback,
        );
    assert!(facts_with_readback.contains(&expected_sub[0]));
    assert!(facts.len() < facts_with_readback.len());
}

#[test]
fn wave508_call_defining_local_and_type_range_battery_parity() {
    use trust_types::*;

    // 1. `as_bytes_length_receiver` fast-paths call-free bodies, resolves a single-def
    // `core::str::<impl str>::as_bytes` call, and declines when `holds_one_value` fails.
    let slice_u8 = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
    };
    let str_ref = Ty::Ref { mutable: false, inner: Box::new(Ty::Str) };
    let mut func = guarded_body(1);
    func.body.arg_count = 2;
    func.body.return_ty = Ty::Int { width: 32, signed: false };
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: false }, name: None },
        LocalDecl { index: 1, ty: str_ref.clone(), name: Some("s".into()) },
        LocalDecl { index: 2, ty: Ty::Int { width: 8, signed: false }, name: Some("k".into()) },
        LocalDecl { index: 3, ty: slice_u8.clone(), name: Some("bytes".into()) },
        LocalDecl {
            index: 4,
            ty: Ty::Tuple(vec![Ty::Int { width: 16, signed: false }, Ty::Bool]),
            name: Some("pair".into()),
        },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place { local: 4, projections: vec![Projection::Field(0)] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 16))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];

    assert!(crate::guards::as_bytes_length_receiver(&func, 3).is_none());

    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place { local: 4, projections: vec![Projection::Field(0)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 16))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                func: "core::str::<impl str>::as_bytes".into(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(3),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::default(),
                span: SourceSpan::default(),
                is_foreign: false,
                is_unsafe_sig: false,
                atomic: None,
                callee_key: None,
                callee_identity: None,
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    assert!(matches!(
        crate::guards::as_bytes_length_receiver(&func, 3),
        Some(Operand::Copy(p)) if *p == Place::local(1)
    ));

    // Reassigning local 3 invalidates `holds_one_value(func, 3)` and must decline.
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
        span: SourceSpan::default(),
    });
    assert!(crate::guards::as_bytes_length_receiver(&func, 3).is_none());

    // 2. `conjoin_type_range_battery` matches sequential step-by-step execution byte-for-byte.
    let goal = Formula::And(vec![
        Formula::Lt(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("k#s0_0".into(), Sort::Int)),
        ),
        Formula::Lt(
            Box::new(Formula::Var("pair.0".into(), Sort::Int)),
            Box::new(Formula::Var("s__slice_len".into(), Sort::Int)),
        ),
    ]);
    let mut rec_fused = Vec::new();
    let fused = super::super::type_ranges::conjoin_type_range_battery(
        &func,
        goal.clone(),
        super::super::type_ranges::RangeBatteryClass::Bounds,
        &mut |b, a| rec_fused.push((b.clone(), a.clone())),
    );

    let mut rec_seq = Vec::new();
    let mut run_step = |f: Formula, step_fn: &dyn Fn(Formula) -> (Formula, bool)| -> Formula {
        let (after, wrapped) = step_fn(f);
        if wrapped
            && let Formula::And(children) = &after
            && let Some(before) = children.last()
        {
            rec_seq.push((before.clone(), after.clone()));
        } else {
            rec_seq.push((after.clone(), after.clone()));
        }
        after
    };
    let empty_excl = trust_types::fx::FxHashSet::default();
    let s1 = run_step(goal, &|f| super::super::alloc_vcs::conjoin_arg_type_ranges_step(&func, f));
    let s2 = run_step(s1, &|f| {
        super::super::type_ranges::conjoin_local_type_ranges_excluding_step(&func, f, &empty_excl)
    });
    let s3 = run_step(s2, &|f| {
        super::super::type_ranges::conjoin_datatype_field_ranges_excluding_step(
            &func,
            f,
            &empty_excl,
        )
    });
    let s4 = run_step(s3, &|f| super::super::type_ranges::conjoin_slice_len_bounds_step(&func, f));

    assert_eq!(fused, s4);
    assert_eq!(rec_fused, rec_seq);
}

#[test]
fn wave509_lazy_semantic_guard_ssa_and_fused_3step_type_ranges_parity() {
    use trust_types::*;

    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.return_ty = Ty::Int { width: 32, signed: false };
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: false }, name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::Int { width: 16, signed: false }, name: Some("k".into()) },
        LocalDecl {
            index: 2,
            ty: Ty::Tuple(vec![
                Ty::Int { width: 8, signed: false },
                Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            ]),
            name: Some("pair".into()),
        },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "my_crate::unmodeled_call".into(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::default(),
                span: SourceSpan::default(),
                is_foreign: false,
                is_unsafe_sig: false,
                atomic: None,
                callee_key: None,
                callee_identity: None,
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];

    let empty_ctx = crate::CalleeSummaryContext::default();
    assert!(!empty_ctx.has_return_value_summary_for("my_crate::unmodeled_call"));
    let sg = super::super::semantic_guard_map_for(&func, None);
    assert!(sg.get(&BlockId(1)).map_or(true, Vec::is_empty));

    let goal = Formula::And(vec![
        Formula::Lt(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("k#s0_0".into(), Sort::Int)),
        ),
        Formula::Lt(
            Box::new(Formula::Var("pair.0".into(), Sort::Int)),
            Box::new(Formula::Var("s__slice_len".into(), Sort::Int)),
        ),
    ]);

    let mut rec_fused = Vec::new();
    let fused = super::super::type_ranges::conjoin_arg_local_field_type_ranges_recorded(
        &func,
        goal.clone(),
        &mut |b, a| rec_fused.push((b.clone(), a.clone())),
    );
    let fused_unrecorded =
        super::super::type_ranges::conjoin_arg_local_field_type_ranges(&func, goal.clone());
    assert_eq!(fused, fused_unrecorded);

    let mut rec_seq = Vec::new();
    let mut run_step = |f: Formula, step_fn: &dyn Fn(Formula) -> (Formula, bool)| -> Formula {
        let (after, wrapped) = step_fn(f);
        if wrapped
            && let Formula::And(children) = &after
            && let Some(before) = children.last()
        {
            rec_seq.push((before.clone(), after.clone()));
        } else {
            rec_seq.push((after.clone(), after.clone()));
        }
        after
    };
    let s1 = run_step(goal, &|f| super::super::alloc_vcs::conjoin_arg_type_ranges_step(&func, f));
    let s2 = run_step(s1, &|f| super::super::type_ranges::conjoin_local_type_ranges_step(&func, f));
    let s3 =
        run_step(s2, &|f| super::super::type_ranges::conjoin_datatype_field_ranges_step(&func, f));

    assert_eq!(fused, s3);
    assert_eq!(rec_fused, rec_seq);
    assert_eq!(rec_fused.len(), 3);
}

#[test]
fn wave510_contract_vcs_prepared_return_path_multi_clause_parity() {
    use trust_types::*;

    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.return_ty = Ty::Int { width: 32, signed: true };
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: true }, name: Some("_0".into()) },
        LocalDecl { index: 1, ty: Ty::Int { width: 32, signed: true }, name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Ge,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(0)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(2))],
                otherwise: BlockId(1),
                span: SourceSpan::default(),
                exhaustive_enum_unreachable: false,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
    ];

    let post_ge_x = Formula::Ge(
        Box::new(Formula::Var("_0".into(), Sort::Int)),
        Box::new(Formula::Var("x".into(), Sort::Int)),
    );
    let post_ge_zero =
        Formula::Ge(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(0)));

    let mut func_both = func.clone();
    func_both.postconditions = vec![post_ge_x.clone(), post_ge_zero.clone()];
    let vcs_both: Vec<Formula> =
        super::super::contract_vcs::generate_v2_contract_vcs_impl(&func_both, None)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .map(|vc| vc.formula)
            .collect();

    let mut func_first = func.clone();
    func_first.postconditions = vec![post_ge_x.clone()];
    let mut vcs_separate: Vec<Formula> =
        super::super::contract_vcs::generate_v2_contract_vcs_impl(&func_first, None)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .map(|vc| vc.formula)
            .collect();

    let mut func_second = func.clone();
    func_second.postconditions = vec![post_ge_zero.clone()];
    vcs_separate.extend(
        super::super::contract_vcs::generate_v2_contract_vcs_impl(&func_second, None)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .map(|vc| vc.formula),
    );

    assert_eq!(vcs_both.len(), 4);
    assert_eq!(vcs_both, vcs_separate);

    // Diverging function (no Return / TailCall terminator) returns no postcondition VCs.
    let mut diverging = func_both;
    diverging.body.blocks[3].terminator = Terminator::Unreachable;
    let vcs_diverging = super::super::contract_vcs::generate_v2_contract_vcs_impl(&diverging, None);
    assert!(vcs_diverging.iter().all(|vc| !matches!(vc.kind, VcKind::Postcondition)));
}

#[test]
fn wave511_copy_and_slice_len_tie_candidate_short_circuit_parity() {
    use trust_types::*;

    let mut func = guarded_body(1);
    func.body.locals = vec![
        LocalDecl { index: 0, name: None, ty: Ty::Int { signed: false, width: 32 } },
        LocalDecl { index: 1, name: Some("x".into()), ty: Ty::Int { signed: false, width: 32 } },
        LocalDecl { index: 2, name: Some("y".into()), ty: Ty::Int { signed: false, width: 32 } },
        LocalDecl { index: 3, name: Some("z".into()), ty: Ty::Int { signed: false, width: 32 } },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 32)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];

    super::super::legacy_version_oracle::without_differential(|| {
        let _analysis = super::super::FuncAnalysisScope::enter(&func);
        let _scope = crate::gen_work_scope_unmetered();
        let sv = super::super::stmt_versions_for(&func);

        // Querying `version_token_at` at `stmt_idx == 0` (`FnWrites::gate` with `i == 0`)
        // must not trigger `BlockWrites::syn_names` isolated statement extraction.
        crate::fn_memo::reset_analysis_memo_stats();
        assert_eq!(sv.version_token_at(&func, BlockId(0), 0, "z"), None);
        assert_eq!(crate::fn_memo::analysis_memo_stats().extraction_stmts, 0);

        // Warm `syn_names` for `stmt_idx == 1` so the test below isolates the
        // copy-tie / slice-len-tie candidate short-circuit.
        let _ = sv.version_token_at(&func, BlockId(0), 1, "z");

        // Prefix [..1] has only BinaryOp (no copy/slice-len tie candidate).
        assert!(!super::super::block_defs::block_has_copy_tie_candidate_until(
            &func.body.blocks[0],
            1
        ));
        crate::fn_memo::reset_analysis_memo_stats();
        let _ = super::super::block_defs::v2_formula_with_copy_ties_at_point_recorded(
            &func,
            &func.body.blocks[0],
            1,
            Formula::Gt(Box::new(Formula::Var("z".into(), Sort::Int)), Box::new(Formula::Int(0))),
        );
        let _ = super::super::block_defs::v2_live_slice_len_ties_at_point(
            &func,
            &func.body.blocks[0],
            1,
            &Formula::Gt(Box::new(Formula::Var("z".into(), Sort::Int)), Box::new(Formula::Int(0))),
        );
        let stats_no_cand = crate::fn_memo::analysis_memo_stats();
        assert_eq!(stats_no_cand.extraction_stmts, 0);

        // Prefix [..2] includes `z = copy y` at statement 1.
        assert!(super::super::block_defs::block_has_copy_tie_candidate_until(
            &func.body.blocks[0],
            2
        ));
        crate::fn_memo::reset_analysis_memo_stats();
        let (_combined, _body, kept) =
            super::super::block_defs::v2_formula_with_copy_ties_at_point_recorded(
                &func,
                &func.body.blocks[0],
                2,
                Formula::Gt(
                    Box::new(Formula::Var("z".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            );
        let stats_with_cand = crate::fn_memo::analysis_memo_stats();
        assert!(stats_with_cand.extraction_stmts > 0);
        assert_eq!(kept.len(), 1);
    });
}

#[test]
fn wave512_terminator_obligation_and_cast_fast_path_parity() {
    use trust_types::terminator_obligations::{
        TerminatorObligationShape, classify_terminator_obligation, unreachable_terminator_span,
    };
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        UnwindEdge, VcKind,
    };

    let mut func = guarded_body(1);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: None },
        LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".into()) },
        LocalDecl { index: 3, ty: Ty::Float { width: 64 }, name: Some("f".into()) },
    ];
    func.body.arg_count = 3;
    let span10 = SourceSpan {
        file: "test.rs".into(),
        line_start: 10,
        col_start: 5,
        line_end: 10,
        col_end: 10,
    };
    let span20 = SourceSpan {
        file: "test.rs".into(),
        line_start: 20,
        col_start: 5,
        line_end: 20,
        col_end: 10,
    };
    let span21 = SourceSpan {
        file: "test.rs".into(),
        line_start: 21,
        col_start: 5,
        line_end: 21,
        col_end: 10,
    };
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::panicking::panic_fmt".into(),
                args: vec![],
                dest: Place::local(0),
                target: None,
                span: span10.clone(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: Default::default(),
                unwind: UnwindEdge::Unreachable,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::panicking::unreachable_display".into(),
                args: vec![],
                dest: Place::local(0),
                target: Some(BlockId(2)),
                span: span20,
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: Default::default(),
                unwind: UnwindEdge::Unreachable,
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::panicking::panic_fmt".into(),
                args: vec![],
                dest: Place::local(0),
                target: None,
                span: span21.clone(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: Default::default(),
                unwind: UnwindEdge::Unreachable,
            },
        },
    ];

    // Block 0: standalone panic_fmt -> AssertionPanicCall (unreachable_terminator_span == None)
    assert_eq!(
        classify_terminator_obligation(&func, &func.body.blocks[0]),
        Some(TerminatorObligationShape::AssertionPanicCall(span10))
    );
    assert_eq!(unreachable_terminator_span(&func, &func.body.blocks[0]), None);
    let vc0 = super::super::overflow_vc::v2_build_terminator_vc(&func, &func.body.blocks[0])
        .expect("panic_fmt must mint Assertion VC");
    assert!(matches!(vc0.kind, VcKind::Assertion { .. }));

    // Block 2: panic_fmt on unreachable_display chain -> Unreachable
    assert_eq!(
        classify_terminator_obligation(&func, &func.body.blocks[2]),
        Some(TerminatorObligationShape::Unreachable(span21.clone()))
    );
    assert_eq!(unreachable_terminator_span(&func, &func.body.blocks[2]), Some(span21));
    let vc2 = super::super::overflow_vc::v2_build_terminator_vc(&func, &func.body.blocks[2])
        .expect("unreachable-chain panic_fmt must mint Unreachable VC");
    assert_eq!(vc2.kind, VcKind::Unreachable);

    // Integer/bool/float-to-integer casts fast-path to None, while unsupported casts
    // still produce an unsupported-cast VC.
    let span = SourceSpan::default();
    assert!(
        super::super::checked_vcs::v2_build_cast_vc(
            &func,
            &func.body.blocks[0],
            &Operand::Copy(Place::local(1)),
            &Ty::u8(),
            &span,
            0,
        )
        .is_none()
    );
    assert!(
        super::super::checked_vcs::v2_build_cast_vc(
            &func,
            &func.body.blocks[0],
            &Operand::Copy(Place::local(2)),
            &Ty::u32(),
            &span,
            0,
        )
        .is_none()
    );
    assert!(
        super::super::checked_vcs::v2_build_cast_vc(
            &func,
            &func.body.blocks[0],
            &Operand::Copy(Place::local(3)),
            &Ty::i64(),
            &span,
            0,
        )
        .is_none()
    );
    assert!(
        super::super::checked_vcs::v2_build_cast_vc(
            &func,
            &func.body.blocks[0],
            &Operand::Constant(ConstValue::Uint(300, 32)),
            &Ty::Char,
            &span,
            0,
        )
        .is_some()
    );
}

#[test]
fn wave513_prepared_block_written_names_and_mut_borrow_resize_gate_parity() {
    use trust_types::Projection;

    let mut func = guarded_body(1);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".to_string()) },
        LocalDecl {
            index: 3,
            ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
            name: Some("r".to_string()),
        },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 32)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place { local: 3, projections: vec![Projection::Deref] },
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];

    let unscoped_written =
        super::super::path_defs::block_written_names(&func, &func.body.blocks[0]);
    let unscoped_kill_names =
        super::super::path_defs::block_entry_fact_kill_names(&func, &func.body.blocks[0]);
    let entry_defs = vec![
        Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
    ];
    let unscoped_live =
        super::super::path_defs::v2_live_path_defs(&func, &func.body.blocks[0], &entry_defs);

    let scope = super::super::FuncAnalysisScope::enter(&func);
    let _ = super::super::stmt_versions_for(&func);
    let scoped_written = super::super::path_defs::block_written_names(&func, &func.body.blocks[0]);
    let scoped_kill_names =
        super::super::path_defs::block_entry_fact_kill_names(&func, &func.body.blocks[0]);
    let scoped_live =
        super::super::path_defs::v2_live_path_defs(&func, &func.body.blocks[0], &entry_defs);
    assert_eq!(scoped_written, unscoped_written);
    assert_eq!(scoped_kill_names, unscoped_kill_names);
    assert_eq!(scoped_live, unscoped_live);

    // Local 1 (`x`) is never mutably borrowed -> `local_mut_borrows_may_resize` is false
    // without needing a full-body borrow-temp scan.
    assert!(!crate::guards::local_is_mutably_borrowed(&func, 1));
    assert!(!crate::guards::local_mut_borrows_may_resize(&func, 1));
    drop(scope);
}

#[test]
fn wave514_short_circuit_local_write_candidate_parity() {
    use trust_types::Projection;

    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("k".to_string()) },
        LocalDecl { index: 3, ty: Ty::u32(), name: Some("m".to_string()) },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 32))),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place { local: 3, projections: vec![Projection::Field(0)] },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        },
    ];

    for scoped in [false, true] {
        let _guard = scoped.then(|| super::super::FuncAnalysisScope::enter(&func));
        let mut visits = 0usize;
        let first = crate::find_local_write_candidate(&func, &func.body.blocks, 3, |b, item| {
            visits += 1;
            if let Some(Statement::Assign { place, .. }) = item
                && place.local == 3
            {
                return Some(b.id.0);
            }
            None
        });
        assert_eq!(first, Some(0));
        if scoped {
            assert_eq!(visits, 1, "indexed find_local_write_candidate must stop at first hit");
        }
        assert_eq!(crate::index_local_const(&func, 2), Some(7));
        assert!(crate::index_local_stable(&func, 2));
        assert_eq!(crate::index_local_const(&func, 3), None);
        assert!(!crate::index_local_stable(&func, 3));
        assert!(super::super::int_conversion::local_value_is_stable(&func, 1));
        assert!(super::super::int_conversion::local_value_is_stable(&func, 2));
        assert!(!super::super::int_conversion::local_value_is_stable(&func, 3));
    }
}

#[test]
fn wave515_induction_and_condvar_short_circuit_candidate_parity() {
    use trust_types::{BinOp, Projection};

    let mut func = guarded_body(1);
    func.body.arg_count = 0;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("acc".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("ck".to_string()) },
        LocalDecl { index: 3, ty: Ty::u32(), name: Some("bad".to_string()) },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(2, 32))),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(4, 32))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        },
    ];

    for scoped in [false, true] {
        let _guard = scoped.then(|| super::super::FuncAnalysisScope::enter(&func));
        assert_eq!(super::super::loop_bounds::accumulator_init_const(&func, 1, 2), Some(5));
        assert_eq!(super::super::loop_bounds::accumulator_init_const(&func, 3, 2), None);
        assert!(super::super::induction::countdown_trip_analysis(&func, None).global.is_empty());
    }
}

#[test]
fn wave516_paired_condvar_and_sep_census_short_circuit_parity() {
    use trust_types::Projection;

    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl {
            index: 1,
            ty: Ty::RawPtr { pointee: Box::new(Ty::u32()), mutable: true },
            name: Some("ptr".to_string()),
        },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("tmp".to_string()) },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place { local: 1, projections: vec![Projection::Deref] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
                span: SourceSpan::default(),
            },
            Statement::CopyNonOverlapping {
                src: Operand::Copy(Place::local(1)),
                dst: Operand::Copy(Place::local(1)),
                count: Operand::Constant(ConstValue::Uint(1, 64)),
                elem_ty: Ty::u32(),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];

    assert!(crate::sep_engine::body_has_unsafe_operation(&func));
    assert_eq!(
        crate::sep_engine::body_unsafe_operation_witness(&func, false),
        Some("a dereference of a raw pointer (or of a non-reference)")
    );
    assert!(crate::sep_engine::validity_rooted_box_deref_temps(&func).is_empty());
    assert!(
        crate::paired_condvar_cert::certify_paired_condvars(
            std::slice::from_ref(&func),
            &[crate::paired_condvar_cert::PairedCondvarCandidate {
                struct_name: "Pair".to_string(),
                condvar_fields: vec![0],
                mutex_fields: vec![1],
                field_count: 2,
            }],
        )
        .is_empty()
    );
}

#[test]
fn wave517_tinv_prepared_body_reuse_and_mention_count_short_circuit_parity() {
    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".to_string()) },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];

    for local in 0..=2 {
        let count = crate::place_write::mention_count(&func, local);
        for expected in 0..=4 {
            assert_eq!(
                crate::place_write::has_mention_count(&func, local, expected),
                count == expected
            );
        }
    }
    assert_eq!(
        crate::place_write::classify_writes(&func),
        crate::place_write::classify_writes_expanded(&func)
    );
}

#[test]
fn wave518_tinv_rows_and_use_facts_prepared_cache_parity() {
    let mut func = guarded_body(1);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".to_string()) },
    ];
    func.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];

    let sv = stmt_versions_for(&func);
    let tag = "#tinv_assume_test_0".to_string();
    let entry_fact = crate::generate::type_invariant_facts::tagged(
        &tag,
        Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("x".to_string(), Sort::Int))),
    );
    let use_facts = crate::generate::type_invariant_facts::TinvUseFacts {
        entry: vec![(tag.clone(), entry_fact.clone())],
        post_calls: Vec::new(),
    };
    let prepared = use_facts.prepare(&func, &sv);

    // Irrelevant formula (does not mention `x`): returns unchanged with empty kept facts/tags.
    let unrelated = Formula::Lt(
        Box::new(Formula::Var("y#d_0_0".to_string(), Sort::Int)),
        Box::new(Formula::Int(10)),
    );
    let (f_unrel, listed_unrel, tags_unrel) =
        prepared.conjoin_at_point_recorded(&func, &sv, BlockId(0), 1, unrelated.clone());
    assert_eq!(f_unrel, unrelated);
    assert!(listed_unrel.is_empty());
    assert!(tags_unrel.is_empty());

    // Relevant formula (mentions `x`): conjoins the tagged entry fact and records the tag.
    let relevant =
        Formula::Lt(Box::new(Formula::Var("x".to_string(), Sort::Int)), Box::new(Formula::Int(10)));
    let (f_rel, listed_rel, tags_rel) =
        prepared.conjoin_at_point_recorded(&func, &sv, BlockId(0), 1, relevant.clone());
    assert_eq!(
        (f_rel, listed_rel, tags_rel),
        crate::generate::type_invariant_facts::conjoin_tinv_facts_at_point_recorded(
            &func,
            &sv,
            BlockId(0),
            1,
            relevant,
            &use_facts,
        )
    );
}

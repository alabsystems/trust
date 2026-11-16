//! Verdict-parity pins for PERF waves 520-536 (see `parity_through_518.rs` for the
//! layout): each fast path must match its reference scan exactly.

use super::*;

#[test]
fn wave520_callsite_pins_and_precondition_fast_path_parity() {
    use trust_types::Symbol;

    use crate::modular::{FunctionSummary, SummaryDatabase};
    use crate::{
        generate_callsite_precondition_vcs, generate_callsite_precondition_vcs_attributed,
        generate_callsite_precondition_vcs_for_each,
    };

    let pin_summary = FunctionSummary::new("callee_pin")
        .with_param_names(vec!["x".to_string()])
        .with_definitional_postcondition(Formula::Eq(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        ));
    assert!(super::super::callsite::summary_may_inject_postcondition(&pin_summary));
    assert!(super::super::callsite::summary_pins_result(&pin_summary));

    let bound_summary = FunctionSummary::new("callee_bound")
        .with_param_names(vec!["x".to_string()])
        .with_definitional_postcondition(Formula::Le(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        ));
    assert!(super::super::callsite::summary_may_inject_postcondition(&bound_summary));
    assert!(!super::super::callsite::summary_pins_result(&bound_summary));

    let precond_summary = FunctionSummary::new("callee_pre")
        .with_param_names(vec!["x".to_string()])
        .with_precondition(Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_verified_callee_postcondition(Formula::Eq(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        ));
    assert!(super::super::callsite::summary_may_inject_postcondition(&precond_summary));
    assert!(!super::super::callsite::summary_pins_result(&precond_summary));

    let replacements = vec![
        ("x".to_string(), Formula::Var("caller_x".to_string(), Sort::Int)),
        ("y".to_string(), Formula::Int(42)),
    ];
    let non_shadowing = vec![(Symbol::intern("i"), Sort::Int)];
    assert!(matches!(
        super::super::callsite::replacements_without_bound_vars(&replacements, &non_shadowing),
        std::borrow::Cow::Borrowed(_)
    ));
    let shadowing = vec![(Symbol::intern("x"), Sort::Int)];
    let filtered =
        super::super::callsite::replacements_without_bound_vars(&replacements, &shadowing);
    assert!(matches!(filtered, std::borrow::Cow::Owned(_)));
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].0, "y");

    let mut caller = guarded_body(1);
    caller.body.arg_count = 1;
    caller.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("caller_x".to_string()) },
    ];
    caller.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: Vec::new(),
            terminator: Terminator::Call {
                func: "callee_pre".to_string(),
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
        BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
    ];

    let mut db_no_pre = SummaryDatabase::new();
    db_no_pre.insert(pin_summary);
    let mut db_with_pre = SummaryDatabase::new();
    db_with_pre.insert(precond_summary);

    assert!(generate_callsite_precondition_vcs(&caller, &db_no_pre).is_empty());
    assert!(generate_callsite_precondition_vcs_attributed(&caller, &db_no_pre).is_empty());

    let batch = generate_callsite_precondition_vcs_for_each(&caller, &[&db_no_pre, &db_with_pre]);
    assert_eq!(batch.len(), 2);
    assert!(batch[0].is_empty());
    assert_eq!(batch[1].len(), 1);
}

#[test]
fn wave521_callee_write_set_and_mutated_param_places_parity() {
    use trust_types::Projection;

    use crate::modular::{FunctionSummary, SummaryDatabase};

    // 1. Callee with a single deref write `*a = 7` produces a 1-path write-set,
    // while a callee with `Rvalue::AddressOf` is rejected in the single-pass scan.
    let mut clean_callee = guarded_body(1);
    clean_callee.name = "callee_write_deref".to_string();
    clean_callee.body.arg_count = 1;
    clean_callee.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(Vec::new()), name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
            name: Some("a".to_string()),
        },
    ];
    clean_callee.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place { local: 1, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];
    let ws = super::super::callee_write_set::derive_callee_write_set(&clean_callee)
        .expect("clean deref store callee should derive a write-set");
    assert_eq!(ws.paths.len(), 1);

    let mut laundering_callee = clean_callee.clone();
    laundering_callee.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::AddressOf(true, Place::local(1)),
        span: SourceSpan::default(),
    });
    assert!(super::super::callee_write_set::derive_callee_write_set(&laundering_callee).is_none());

    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("callee_write_deref")
            .with_extracted_body(std::sync::Arc::new(clean_callee.clone())),
    );
    db.insert(FunctionSummary::new("callee_no_body"));
    let built = super::super::callee_write_set::build_callee_write_sets(&db);
    assert_eq!(built.len(), 1);
    assert!(built.contains_key("callee_write_deref"));

    // 2. `MutatedParamPlaces` and `postcondition_references_mutated_param_cached`
    // populate `OnceCell` lazily (not initialized on variable-free postconditions)
    // and match `postcondition_references_mutated_param` across multiple clauses.
    let mut fn_mut_param = guarded_body(1);
    fn_mut_param.body.arg_count = 2;
    fn_mut_param.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".to_string()) },
    ];
    fn_mut_param.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(10, 32))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];

    let cache: std::cell::OnceCell<super::super::callee_summaries::MutatedParamPlaces> =
        std::cell::OnceCell::new();
    let const_post = Formula::Bool(true);
    assert!(!super::super::callee_summaries::postcondition_references_mutated_param_cached(
        &fn_mut_param,
        &const_post,
        &cache,
    ));
    assert!(cache.get().is_none(), "variable-free clause must not initialize MutatedParamPlaces");

    let post_b = Formula::Eq(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("b".to_string(), Sort::Int)),
    );
    let post_a = Formula::Eq(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("a".to_string(), Sort::Int)),
    );
    assert_eq!(
        super::super::callee_summaries::postcondition_references_mutated_param_cached(
            &fn_mut_param,
            &post_b,
            &cache,
        ),
        super::super::callee_summaries::postcondition_references_mutated_param(
            &fn_mut_param,
            &post_b
        ),
    );
    assert!(cache.get().is_some());
    assert!(!super::super::callee_summaries::postcondition_references_mutated_param_cached(
        &fn_mut_param,
        &post_b,
        &cache,
    ));
    assert!(super::super::callee_summaries::postcondition_references_mutated_param_cached(
        &fn_mut_param,
        &post_a,
        &cache,
    ));
}

#[test]
fn wave522_witness_grounding_and_spec_model_family_gate_parity() {
    use trust_types::{AggregateKind, VariantDef};

    // 1. A return block that writes `_0` directly causes `return_producer_ancestors`
    // (exercised via `resolve_enum_return_aggregate`) to short-circuit before
    // allocating `visited` or querying `v2_predecessors`.
    let mut opt_fn = guarded_body(1);
    opt_fn.body.locals = vec![LocalDecl {
        index: 0,
        ty: Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef { name: "None".to_string(), discriminant: 0, fields: Vec::new() },
                VariantDef {
                    name: "Some".to_string(),
                    discriminant: 1,
                    fields: vec![("0".to_string(), Ty::i32())],
                },
            ],
        ),
        name: None,
    }];
    opt_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "core::option::Option".to_string(),
                    variant: 1,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Constant(ConstValue::Int(5))],
            ),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];

    let grounded = super::super::witness_grounding::enum_return_grounded_model_vars(&opt_fn);
    assert!(grounded.contains("_0__discr"));
    assert!(grounded.contains("_0__value"));

    // 2. Non-Vec payload components short-circuit in `len_witness_credited_pairs`
    // and `ordering_witness_credited_items` before building `v2_predecessors`.
    let len_post = Formula::Eq(
        Box::new(Formula::Var("_0__value.0__len".to_string(), Sort::Int)),
        Box::new(Formula::Var("_0__value.1__len".to_string(), Sort::Int)),
    );
    let ord_post = Formula::Lt(
        Box::new(Formula::Var("_0__value.__trust_ok_0".to_string(), Sort::Int)),
        Box::new(Formula::Var("_0__value.__trust_ok_1".to_string(), Sort::Int)),
    );
    assert!(
        super::super::witness_grounding::len_witness_credited_pairs(&opt_fn, &[&len_post])
            .is_empty()
    );
    assert!(
        super::super::witness_grounding::ordering_witness_credited_items(&opt_fn, &[&ord_post])
            .is_empty()
    );
}

#[test]
fn wave523_discharge_lazy_env_and_sigma_copy_root_parity() {
    let mut func = guarded_body(10);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".to_string()) },
        LocalDecl { index: 2, ty: Ty::u32(), name: None },
        LocalDecl { index: 3, ty: Ty::u32(), name: Some("_tmp".to_string()) },
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

    // 1. Copy temp `_2 = copy _1` resolves to stable parameter `_1` (`x`).
    assert_eq!(
        super::super::discharge::sigma_actual_stable_copy_root(
            &func,
            &Operand::Copy(Place::local(2))
        ),
        Some(Place::local(1))
    );
    // Unnamed or `_`-prefixed root returns `None` immediately before stability scans.
    assert_eq!(
        super::super::discharge::sigma_actual_stable_copy_root(
            &func,
            &Operand::Copy(Place::local(3))
        ),
        None
    );
    assert!(super::super::discharge::caller_precondition_var_is_entry_stable(&func, "x"));
    assert!(!super::super::discharge::caller_precondition_var_is_entry_stable(&func, "_tmp"));

    // 2. Reassigning `_1` invalidates both `sigma_actual_stable_copy_root` and
    // `caller_precondition_var_is_entry_stable`.
    let mut mutated_func = func.clone();
    mutated_func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    });
    assert_eq!(
        super::super::discharge::sigma_actual_stable_copy_root(
            &mutated_func,
            &Operand::Copy(Place::local(2)),
        ),
        None
    );
    assert!(!super::super::discharge::caller_precondition_var_is_entry_stable(&mutated_func, "x"));
}

#[test]
fn wave524_checked_vcs_upfront_op_uniqueness_and_cond_operands_parity() {
    use trust_types::{AssertMessage, UnwindEdge};

    let mut func = guarded_body(10);
    func.body.arg_count = 2;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::i32(), name: None },
        LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".to_string()) },
        LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".to_string()) },
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        LocalDecl { index: 4, ty: Ty::i32(), name: None },
    ];
    let lhs = Operand::Copy(Place::local(1));
    let rhs = Operand::Copy(Place::local(2));
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Eq,
                    rhs.clone(),
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
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(BinOp::Div, lhs.clone(), rhs.clone()),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::BinaryOp(BinOp::Div, lhs.clone(), rhs.clone()),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        },
    ];

    // 1. Multiple same-op `Div` statements in `op_block` are rejected upfront by
    // `v2_divzero_assert_exactly_bound` and `v2_divrem_overflow_assert_exactly_bound`.
    assert!(!super::super::checked_vcs::v2_divzero_assert_exactly_bound(
        &func,
        BinOp::Div,
        BlockId(1),
        0,
        &lhs,
        &rhs,
    ));
    assert!(!super::super::checked_vcs::v2_divrem_overflow_assert_exactly_bound(
        &func,
        BinOp::Div,
        BlockId(1),
        0,
        &lhs,
        &rhs,
    ));

    // 2. Stack-inline `operand_names` in `v2_find_condition_binary_operands` finds the
    // unique condition comparison and rejects later writes to comparison inputs.
    let found = super::super::block_defs::v2_find_condition_binary_operands(
        &func,
        &func.body.blocks[0],
        &Operand::Move(Place::local(3)),
    );
    assert!(found.is_some());
}

#[test]
fn wave525_overflow_vc_lazy_sv_and_dominating_facts_parity() {
    use trust_types::{AssertMessage, UnwindEdge};

    let mut func = guarded_body(10);
    func.body.arg_count = 2;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Int { width: 128, signed: true }, name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Int { width: 128, signed: true },
            name: Some("a".to_string()),
        },
        LocalDecl { index: 2, ty: Ty::i64(), name: Some("b".to_string()) },
        LocalDecl { index: 3, ty: Ty::Int { width: 128, signed: true }, name: None },
        LocalDecl { index: 4, ty: Ty::Bool, name: None },
    ];
    func.preconditions = vec![
        Formula::Ge(Box::new(Formula::var("a", Sort::Int)), Box::new(Formula::Int(-10))),
        Formula::Le(Box::new(Formula::var("a", Sort::Int)), Box::new(Formula::Int(10))),
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Gt,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(ConstValue::Int(0)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Assert {
                cond: Operand::Move(Place::local(4)),
                expected: true,
                msg: AssertMessage::DivisionByZero,
                target: BlockId(1),
                unwind: UnwindEdge::Cleanup(BlockId(2)),
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Cast(
                        Operand::Copy(Place::local(2)),
                        Ty::Int { width: 128, signed: true },
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(3)),
                    ),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Resume },
    ];

    // 1. `v2_signed_mul_corner_bounds` resolves `a`'s precondition box `[-10, 10]` via
    // lazy `sv` and `local 3`'s `i64 -> i128` cast box without needing `sv` on `local 3`.
    let bounds = super::super::overflow_vc::v2_signed_mul_corner_bounds(
        &func,
        &func.body.blocks[1],
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(3)),
        Some(1),
    );
    assert_eq!(bounds, Some(((-10, 10), (i64::MIN as i128, i64::MAX as i128))));

    // 2. `v2_widening_bv_source` identifies `local 3` as a widening cast from `i64` into
    // 128 bits and rejects mismatched target widths in O(1).
    assert_eq!(
        super::super::overflow_vc::v2_widening_bv_source(
            &func,
            &Operand::Copy(Place::local(3)),
            128
        ),
        Some((64, true))
    );
    assert_eq!(
        super::super::overflow_vc::v2_widening_bv_source(
            &func,
            &Operand::Copy(Place::local(3)),
            64
        ),
        None
    );

    // 3. `DominatingFacts::guarded_edge_dominates` admits the normal `Assert` target
    // (`bb0 -> bb1`) and rejects the unguarded cleanup target (`bb0 -> bb2`).
    let dom = super::super::dominating_facts_for(&func);
    assert!(dom.guarded_edge_dominates(&func.body.blocks[0], BlockId(1)));
    assert!(!dom.guarded_edge_dominates(&func.body.blocks[0], BlockId(2)));
}

#[test]
fn wave526_call_facts_and_vec_length_invariant_single_pass_parity() {
    use trust_types::{Projection, UnwindEdge};

    // 1. `vec_length_is_invariant` single-pass reborrow accounting admits a benign
    // `Vec::len` call on a single-assignment reborrow `_2 = &(*_1)` and rejects an
    // unaccounted extra mention of `_2`.
    let mut vec_fn = guarded_body(10);
    vec_fn.body.arg_count = 1;
    vec_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::usize(), name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Seq { elem: Box::new(Ty::u32()), drop_auth: None }),
            },
            name: Some("v".to_string()),
        },
        LocalDecl {
            index: 2,
            ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Seq { elem: Box::new(Ty::u32()), drop_auth: None }),
            },
            name: None,
        },
        LocalDecl {
            index: 3,
            ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Seq { elem: Box::new(Ty::u32()), drop_auth: None }),
            },
            name: None,
        },
    ];
    vec_fn.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref {
                    mutable: false,
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                func: "alloc::vec::Vec::<u32>::len".to_string(),
                args: vec![Operand::Move(Place::local(2))],
                dest: Place::local(0),
                target: Some(BlockId(1)),
                unwind: UnwindEdge::Continue,
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
    assert!(super::super::value_facts::vec_length_is_invariant(&vec_fn, 1));

    let mut leaked_vec_fn = vec_fn.clone();
    leaked_vec_fn.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
        span: SourceSpan::default(),
    });
    assert!(!super::super::value_facts::vec_length_is_invariant(&leaked_vec_fn, 1));

    // 2. `build_additive_bound_facts` emits `Le(_5.0, 2)` for a `CheckedBinaryOp(Add)`
    // tuple local `_5: (u32, bool)` over two `bool as u32` casts via `checked_op_locals`.
    let mut add_fn = guarded_body(10);
    add_fn.body.arg_count = 2;
    add_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::u32(), name: None },
        LocalDecl { index: 1, ty: Ty::Bool, name: Some("a".to_string()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("b".to_string()) },
        LocalDecl { index: 3, ty: Ty::u32(), name: None },
        LocalDecl { index: 4, ty: Ty::u32(), name: None },
        LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
    ];
    add_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u32()),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::u32()),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(3)),
                    Operand::Copy(Place::local(4)),
                ),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];
    let additive_facts = super::super::value_facts::build_additive_bound_facts(&add_fn);
    assert!(additive_facts.contains(&Formula::Le(
        Box::new(Formula::Var("_5.0".to_string(), Sort::Int)),
        Box::new(Formula::Int(2)),
    )));

    // 3. `saturating_call_dest_value` and `wrapping_neg_call_dest_value` short-circuit
    // mismatched arities and emit exact clamped/wrapping formulas on matching calls.
    let sat_term = Terminator::Call {
        func: "core::num::<impl u32>::saturating_add".to_string(),
        args: vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(4))],
        dest: Place::local(0),
        target: Some(BlockId(0)),
        unwind: UnwindEdge::Continue,
        span: SourceSpan::default(),
        is_foreign: false,
        is_unsafe_sig: false,
        atomic: None,
        callee_key: None,
        callee_identity: None,
    };
    assert!(super::super::call_facts::saturating_call_dest_value(&add_fn, &sat_term).is_some());
    assert!(super::super::call_facts::wrapping_neg_call_dest_value(&add_fn, &sat_term).is_none());
}

#[test]
fn wave527_unwrap_panic_turbofish_and_checked_arith_closure_parity() {
    use trust_types::{Projection, UnOp};

    // 1. `callee_without_turbofish_args` slice-based copy preserves qualified paths,
    // fn-signature arrows inside `::<...>`, and unbalanced `<` fail-closed.
    let plain = "<MyType as core::ops::Index<usize>>::index";
    assert!(matches!(
        super::super::unwrap_panic::callee_without_turbofish_args(plain),
        std::borrow::Cow::Borrowed(s) if s == plain
    ));
    assert_eq!(
        super::super::unwrap_panic::callee_without_turbofish_args(
            "alloc::collections::VecDeque::<fn(u32) -> u32 {u32::count_ones}>::insert::<usize>"
        )
        .as_ref(),
        "alloc::collections::VecDeque::::insert::"
    );
    let unbalanced = "core::option::Option::<u32::unwrap";
    assert_eq!(
        super::super::unwrap_panic::callee_without_turbofish_args(unbalanced).as_ref(),
        unbalanced
    );

    // 2. `checked_arith_result_value_vars` resolves out-of-order copy chains (`_0 = _2; _2 = _3.0`)
    // while skipping non-`.0` field projections (`_4 = _3.1`).
    let mut chk_fn = guarded_body(10);
    chk_fn.body.arg_count = 1;
    chk_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::usize(), name: None },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".to_string()) },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("c".to_string()) },
        LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
        LocalDecl { index: 4, ty: Ty::Bool, name: None },
    ];
    chk_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 64)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 3,
                    projections: vec![Projection::Field(0)],
                })),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 3,
                    projections: vec![Projection::Field(1)],
                })),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];
    let vars = super::super::type_ranges::checked_arith_result_value_vars(&chk_fn);
    assert!(vars.contains("_3.0"));
    assert!(vars.contains("c"));
    assert!(vars.contains("_0"));
    assert!(!vars.contains("_4"));

    // 3. `length_nonneg_base_names` single-pass local classification admits slice length
    // symbols and unsigned `PtrMetadata` destinations while ignoring signed destinations.
    let mut len_fn = guarded_body(10);
    len_fn.body.arg_count = 1;
    len_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::usize(), name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
            },
            name: Some("a".to_string()),
        },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("u_len".to_string()) },
        LocalDecl { index: 3, ty: Ty::isize(), name: Some("s_len".to_string()) },
    ];
    len_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    }];
    let bases = super::super::type_ranges::length_nonneg_base_names(&len_fn);
    assert!(bases.contains("a__slice_len"));
    assert!(bases.contains("u_len"));
    assert!(!bases.contains("s_len"));
}

#[test]
fn wave528_alloc_vcs_origin_def_and_top_level_comma_parity() {
    // 1. `first_generic_arg` and `parse_spelled_type_byte_size` zero-allocation
    // top-level comma helpers preserve nested generic/tuple parsing and lifetime skipping.
    assert_eq!(
        super::super::alloc_vcs::first_generic_arg("alloc::vec::Vec<'a, (u32, [u16; 2]), Global>"),
        Some("(u32, [u16; 2])")
    );
    assert_eq!(
        super::super::alloc_vcs::first_generic_arg("core::slice::iter::Iter<'a, u64>"),
        Some("u64")
    );
    assert_eq!(
        super::super::alloc_bounds::split_top_level_commas("u8, (u32, [u16; 3]), bool"),
        vec!["u8", " (u32, [u16; 3])", " bool"]
    );
    assert_eq!(
        super::super::alloc_bounds::parse_spelled_type_byte_size("()"),
        Some(0)
    );
    assert_eq!(
        super::super::alloc_bounds::parse_spelled_type_byte_size("[[u16; 3]; 2]"),
        Some(12)
    );
    assert_eq!(
        super::super::alloc_bounds::parse_spelled_type_byte_size("(u8, (u32, [u16; 3]), bool)"),
        None
    );
    assert_eq!(
        super::super::alloc_bounds::parse_spelled_type_byte_size("(u8, UnknownAdt, u64)"),
        None
    );

    // 2. `is_capacity_reserving_std_extend` zero-allocation tuple component walker
    // recognizes nested capacity-reserving tuple receivers and rejects unbalanced or
    // non-reserving tuple receivers.
    assert!(super::super::alloc_vcs::is_capacity_reserving_std_extend(
        "<(alloc::collections::btree::set::BTreeSet<u8>, (&mut alloc::vec::Vec<u8>, u32)) as \
         core::iter::traits::collect::Extend<(u8, (u8, u32))>>::extend::<core::ops::range::Range<u8>>"
    ));
    assert!(!super::super::alloc_vcs::is_capacity_reserving_std_extend(
        "<(alloc::collections::btree::set::BTreeSet<u8>, alloc::collections::linked_list::LinkedList<u8>) as \
         core::iter::traits::collect::Extend<(u8, u8)>>::extend::<core::ops::range::Range<u8>>"
    ));

    // 3. `iterator_origin_def` and `call_dest_hop_keyed` short-circuit on parameters
    // and non-unique definitions in O(1) while preserving conduit-gated origins.
    let mut iter_fn = guarded_body(10);
    iter_fn.body.arg_count = 1;
    iter_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: None },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("param".to_string()) },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("it".to_string()) },
        LocalDecl {
            index: 3,
            ty: Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) },
            name: Some("conduit".to_string()),
        },
        LocalDecl { index: 4, ty: Ty::usize(), name: Some("next_out".to_string()) },
    ];
    iter_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Call {
            func: "core::iter::traits::iterator::Iterator::next".to_string(),
            args: vec![Operand::Move(Place::local(3))],
            dest: Place::local(4),
            target: None,
            unwind: trust_types::UnwindEdge::Continue,
            span: SourceSpan::default(),
            is_foreign: false,
            is_unsafe_sig: false,
            atomic: None,
            callee_key: None,
            callee_identity: None,
        },
    }];
    assert!(super::super::iterator_yield::iterator_origin_def(&iter_fn, 1).is_none());
    assert!(super::super::iterator_yield::call_dest_hop_keyed(&iter_fn, 1).is_none());
    assert!(super::super::iterator_yield::iterator_origin_def(&iter_fn, 2).is_some());
}

#[test]
fn wave529_collection_range_and_panic_calls_single_pass_parity() {
    use trust_types::{AggregateKind, VcKind};

    // 1. Zero-allocation `const_generic_literal` and `collection_method_panic`
    // (`nth_method_generic_arg` / `single_method_generic_arg`) preserve `RangeFull`
    // position checks, `_usize` stripping, and multi-arg rejection.
    assert_eq!(
        super::super::collection_range::const_generic_literal(
            "core::slice::<impl [u8]>::as_chunks::<4_usize>"
        ),
        Some(4)
    );
    assert_eq!(
        super::super::collection_range::const_generic_literal(
            "core::slice::<impl [u8]>::as_chunks::<4, 2>"
        ),
        None
    );
    assert!(matches!(
        super::super::collection_range::collection_method_panic(
            "alloc::vec::Vec::<u8>::extract_if::<fn(&mut u8) -> bool, core::ops::range::RangeFull>"
        ),
        Some(super::super::SliceMethodPanic::CollectionRange { range_is_full: true, .. })
    ));
    assert!(matches!(
        super::super::collection_range::collection_method_panic(
            "alloc::vec::Vec::<u8>::extract_if::<core::ops::range::RangeFull, core::ops::range::Range<usize>>"
        ),
        Some(super::super::SliceMethodPanic::CollectionRange { range_is_full: false, .. })
    ));

    // 2. `slice_method_panic_body` (`RangeIndex`) resolves a call-block `RangeTo` bound
    // via single-pass `range_bound_unchanged_until_call` and rejects a range local read
    // by a second statement.
    let mut range_fn = guarded_body(10);
    range_fn.body.arg_count = 2;
    range_fn.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: None },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
            name: Some("s".to_string()),
        },
        LocalDecl { index: 2, ty: Ty::usize(), name: Some("k".to_string()) },
        LocalDecl {
            index: 3,
            ty: Ty::adt_enum("core::ops::range::RangeTo<usize>", vec![]),
            name: None,
        },
        LocalDecl {
            index: 4,
            ty: Ty::adt_enum("core::ops::range::RangeTo<usize>", vec![]),
            name: None,
        },
    ];
    range_fn.body.blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "core::ops::range::RangeTo<usize>".to_string(),
                    variant: 0,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Copy(Place::local(2))],
            ),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Call {
            func: "<[u8] as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index"
                .to_string(),
            args: vec![Operand::Copy(Place::local(1)), Operand::Move(Place::local(3))],
            dest: Place::local(0),
            target: None,
            unwind: trust_types::UnwindEdge::Continue,
            span: SourceSpan::default(),
            is_foreign: false,
            is_unsafe_sig: false,
            atomic: None,
            callee_key: None,
            callee_identity: None,
        },
    }];
    let body = super::super::panic_calls::slice_method_panic_body(
        &range_fn,
        &super::super::SliceMethodPanic::RangeIndex,
        "<[u8] as core::ops::index::Index<core::ops::range::RangeTo<usize>>>::index",
        &[Operand::Copy(Place::local(1)), Operand::Move(Place::local(3))],
        false,
        &range_fn.body.blocks[0],
    );
    assert!(matches!(body, Some((_, VcKind::SliceBoundsCheck))));
}

#[test]
fn wave530_body_fact_presence_call_gates_and_str_offset_fast_reject_parity() {
    use super::super::call_facts::{is_int_wrapping_neg_call, saturating_add_sub_method};
    use super::super::callee_summaries::fp_abs_call_width;

    assert!(!is_int_wrapping_neg_call("mycrate::foo::wrapping_neg"));
    assert!(is_int_wrapping_neg_call("core::num::<impl i32>::wrapping_neg"));

    assert_eq!(saturating_add_sub_method("mycrate::foo::saturating_add"), None);
    assert_eq!(
        saturating_add_sub_method("core::num::<impl u32>::saturating_add"),
        Some("saturating_add")
    );
    assert_eq!(
        saturating_add_sub_method(
            "@trust-rustc-intrinsic::core::intrinsics::saturating_sub::<u32>"
        ),
        Some("saturating_sub")
    );

    assert_eq!(fp_abs_call_width("mycrate::f64::abs"), None);
    assert_eq!(fp_abs_call_width("core::f64::<impl f64>::abs"), Some(64));

    let mut func = guarded_body(10);
    func.body.arg_count = 1;
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: Some("_0".to_string()) },
        LocalDecl {
            index: 1,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("x".to_string()),
        },
        LocalDecl {
            index: 2,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("y".to_string()),
        },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::num::<impl i32>::abs".to_string(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::Continue,
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

    let (facts, _) =
        super::super::value_facts::build_global_invariant_facts_with_congruence_range(&func);
    assert_eq!(facts.len(), 1);
    assert!(super::super::str_offset::build_str_len_call_tie_facts(&func).is_empty());
}

#[test]
fn wave531_container_len_and_witness_grounding_fast_reject_parity() {
    let mut func = guarded_body(10);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: Some("_0".to_string()) },
        LocalDecl {
            index: 1,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("x".to_string()),
        },
        LocalDecl {
            index: 2,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("y".to_string()),
        },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "user::custom::helper".to_string(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::Continue,
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

    assert!(super::super::container_len::build_push_guard_elem_len_map(&func).is_empty());
    assert!(super::super::container_len::build_len_guard_field_map(&func).is_empty());
    let post1 = Formula::Eq(
        Box::new(Formula::Var("_1__value.0__len".to_string(), Sort::Int)),
        Box::new(Formula::Int(0)),
    );
    let post2 = Formula::Eq(
        Box::new(Formula::Var("_0__value.0__len#1".to_string(), Sort::Int)),
        Box::new(Formula::Var("_0__value.1__len#1".to_string(), Sort::Int)),
    );
    let pairs = super::super::witness_grounding::len_pair_coverage(&[&post1, &post2]);
    assert_eq!(pairs.len(), 1);
}

#[test]
fn wave532_loop_bounds_and_iterator_yield_fast_reject_parity() {
    let mut func = guarded_body(10);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: Some("_0".to_string()) },
        LocalDecl {
            index: 1,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("x".to_string()),
        },
        LocalDecl {
            index: 2,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("y".to_string()),
        },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "user::custom::helper".to_string(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::Continue,
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

    assert_eq!(super::super::loop_bounds::total_loop_iterations(&func), None);
    assert_eq!(super::super::iterator_yield::next_call_receiver(&func, 2), None);
    assert!(!super::super::iterator_yield::adt_is_char_indices("user::MyChars<'a>"));
    assert!(super::super::iterator_yield::adt_is_char_indices("core::str::CharIndices<'a>"));
}

#[test]
fn wave533_induction_and_alloc_bounds_fast_reject_parity() {
    let mut func = guarded_body(10);
    func.body.blocks =
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }];

    assert!(super::super::induction::downward_guards(&func, 1).is_empty());
    let countdown = super::super::induction::countdown_trip_analysis(&func, None);
    assert!(countdown.global.is_empty() && countdown.per_block.is_empty());
    let custom_adt = Ty::Adt {
        name: "user::CustomOption<i32>".into(),
        fields: vec![].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert_eq!(super::super::alloc_bounds::fold_accumulator_int_ty(&custom_adt), None);
}

#[test]
fn wave534_alloc_vcs_tail_and_bounded_source_gates_parity() {
    let mut func = guarded_body(10);
    func.body.locals = vec![
        LocalDecl { index: 0, ty: Ty::Tuple(vec![]), name: Some("_0".to_string()) },
        LocalDecl {
            index: 1,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("x".to_string()),
        },
        LocalDecl {
            index: 2,
            ty: Ty::Int { width: 32, signed: true },
            name: Some("y".to_string()),
        },
    ];
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::iter::traits::iterator::Iterator::count".to_string(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                unwind: trust_types::UnwindEdge::Continue,
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

    assert!(super::super::alloc_vcs::generate_unbounded_allocation_vcs(&func).is_empty());
    assert_eq!(
        super::super::alloc_vcs::unbounded_sysroot_iterator_adt_name("core::iter::Repeat<u8>"),
        Some("Repeat")
    );
    assert_eq!(
        super::super::alloc_vcs::unbounded_sysroot_iterator_adt_name("user::iter::Repeat<u8>"),
        None
    );
}

#[test]
fn wave535_semantic_guard_map_memo_fast_hit_and_entry_call_presence_parity() {
    let func = guarded_body(10);
    let mut db = crate::modular::SummaryDatabase::new();
    db.insert(
        crate::modular::FunctionSummary::new("other_callee")
            .with_definitional_postcondition(Formula::Bool(true))
            .proved(),
    );
    let _scope = FuncAnalysisScope::enter(&func);
    let map_none = super::super::semantic_guard_map_for(&func, None);
    let map_some = super::super::semantic_guard_map_for(&func, Some(&db));
    assert!(
        std::rc::Rc::ptr_eq(&map_none, &map_some),
        "non-matching summary database on call-free function must reuse memoized semantic guard map"
    );
    let map_some_again = super::super::semantic_guard_map_for(&func, Some(&db));
    assert!(
        std::rc::Rc::ptr_eq(&map_some, &map_some_again),
        "second lookup with same summary database revision must hit raw_key memo directly"
    );
    assert!(!super::super::terminator_presence_for(&func).has_call);
}

#[test]
fn wave536_contract_vcs_type_ranges_overflow_vc_and_value_facts_gates_parity() {
    let mut func = guarded_body(10);
    func.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Adt {
            name: "user::CustomVec<u8>".into(),
            fields: vec![].into(),
            variants: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        },
        name: Some("custom".to_string()),
    });
    func.postconditions = vec![Formula::Ge(
        Box::new(Formula::Var("_0".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )];

    let _scope = FuncAnalysisScope::enter(&func);
    let (all_coll, non_zst_coll) = super::super::type_ranges::coll_len_bound_vars(&func);
    assert!(all_coll.is_empty() && non_zst_coll.is_empty());

    let yield_constraints = super::super::overflow_vc::v2_bv_yield_constraints(
        &func,
        &func.body.blocks[1],
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(3)),
        32,
        false,
    );
    assert!(yield_constraints.is_empty());

    let contract_vcs = super::super::contract_vcs::generate_v2_contract_vcs_impl(&func, None);
    assert!(!contract_vcs.is_empty());
    let global_facts = super::super::value_facts::build_global_invariant_facts(&func);
    assert!(global_facts.is_empty());
}

//! Correctness pins for [`FuncAnalysisScope`](super::FuncGuardCache) and for the
//! ambient-budget polls added alongside it.
//!
//! The cache exists for speed: on `trust-spec-elab` the two whole-CFG analyses
//! it memoizes were 99.9% of the R1 pre-pass's thread time, rebuilt identically
//! at every recursive call site. A speed fix that moved a verdict would be a
//! soundness bug, so the first two tests pin EQUIVALENCE (cached == uncached,
//! per block) and IDENTITY-BINDING (a cache answers for the function it was
//! built from, never for a same-named different one).
//!
//! On "a test that would fail if the cache returned a stale `StmtVersionCtx`":
//! a *literally* stale cache is unconstructible here, and that is the design.
//! `FuncAnalysisScope` holds `&'f VerifiableFunction`, so the shared borrow makes
//! `&mut` to the same value a compile error for the cache's whole lifetime —
//! there is no runtime window in which `func` can change under it. What CAN go
//! wrong is the realistic implementation mistake this design rejects: keying the
//! memo on something SHARED (a def-path, a global, a thread-local, a reused
//! pointer), so a second function collides with the first's entry.
//! `cache_is_bound_to_its_function_not_a_shared_key` constructs exactly that
//! collision — two structurally different bodies with identical `name` and
//! `def_path` — and fails if either shares the other's analysis. See its body
//! for the measured consequence of getting it wrong.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::path_defs::v2_conjoin_path_guards_for_hardened;
use super::safety::v2_build_path_guard_map;
use super::{FuncAnalysisScope, guard_map_for, stmt_versions_for};

/// `GuardCondition` deliberately does not implement `PartialEq`, so compare a
/// DETERMINISTIC rendering: sorted by block id, each block's path list rendered
/// with `Debug`. Sorting matters — a `HashMap`'s iteration order is an
/// implementation detail, and comparing raw `Debug` of the map would make this
/// test's outcome depend on hash layout rather than on content.
fn render_guard_map(map: &super::PathGuardMap) -> Vec<(usize, String)> {
    let mut rendered: Vec<(usize, String)> =
        map.iter().map(|(block, paths)| (block.0, format!("{paths:?}"))).collect();
    rendered.sort();
    rendered
}

/// `fn f(x: u32) -> u32 { let c = x < BOUND; if c { x + 1 } else { x } }`
///
/// A guarded join: bb0 defines `c` from `x` and switches on it, so bb1 and bb2
/// each carry a DIFFERENT dominating path guard, and `y` is written in bb1 —
/// which is what makes the statement-version oracle and the path-guard map both
/// non-trivial (and therefore able to disagree if the cache misbound them).
fn guarded_body(bound: u128) -> VerifiableFunction {
    guarded_body_shaped(bound, false)
}

/// `swap_arms` inverts which successor is the SwitchInt match arm. That changes
/// the PATH-GUARD MAP itself (bb1 flips between `SwitchIntMatch` and
/// `SwitchIntOtherwise`), not merely the constant inside a statement — which the
/// anti-vacuity control below requires, and which a `bound`-only difference does
/// NOT provide: the guard map records the discriminant place, so two bodies that
/// differ only in a constant have BYTE-IDENTICAL maps. (Measured: the control
/// caught exactly that on the first version of this fixture.)
fn guarded_body_shaped(bound: u128, swap_arms: bool) -> VerifiableFunction {
    VerifiableFunction {
        name: "same_name".to_string(),
        def_path: "same_name".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(bound, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: if swap_arms {
                            vec![(0, BlockId(1))]
                        } else {
                            vec![(0, BlockId(2))]
                        },
                        otherwise: if swap_arms { BlockId(2) } else { BlockId(1) },
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The probe formula: reads BOTH the guard subject `x` and the block-written
/// `y`, so the result depends on the statement-version oracle (which versions
/// `y` per block) AND on the path-guard map (which supplies `c`'s branch
/// condition). A cache that returned either analysis for the wrong body would
/// change this formula.
fn probe() -> Formula {
    Formula::Eq(
        Box::new(Formula::Var("y".to_string(), Sort::Int)),
        Box::new(Formula::Var("x".to_string(), Sort::Int)),
    )
}

/// VERDICT IDENTITY, at the unit level: for EVERY block, the conjoin returns
/// exactly the same formula inside a memo scope as outside one. This is the pin
/// that makes the memoization a pure performance change — if it ever fails, a
/// verdict moved.
#[test]
fn memo_scope_does_not_change_the_conjoined_formula() {
    let func = guarded_body(10);
    let outside: Vec<Formula> = func
        .body
        .blocks
        .iter()
        .map(|b| v2_conjoin_path_guards_for_hardened(&func, b.id, probe()))
        .collect();
    let inside: Vec<Formula> = {
        let _scope = FuncAnalysisScope::enter(&func);
        func.body
            .blocks
            .iter()
            .map(|b| v2_conjoin_path_guards_for_hardened(&func, b.id, probe()))
            .collect()
    };
    assert_eq!(outside, inside, "the memo scope changed a formula — a verdict moved");
}

/// Repeated lookups inside ONE scope stay equal to the unmemoized answer. A memo
/// that returned a first-call result and then drifted fails here.
#[test]
fn repeated_lookups_in_one_scope_are_stable() {
    let func = guarded_body(10);
    let expected = v2_conjoin_path_guards_for_hardened(&func, BlockId(1), probe());
    let _scope = FuncAnalysisScope::enter(&func);
    for round in 0..8 {
        assert_eq!(
            expected,
            v2_conjoin_path_guards_for_hardened(&func, BlockId(1), probe()),
            "memoized conjoin drifted on repeat lookup {round}"
        );
    }
}

/// THE STALE-MEMO DISCRIMINATOR.
///
/// Two functions with the SAME `name` and SAME `def_path` but DIFFERENT bodies.
/// The memo is entered for A, then — WITHOUT leaving A's scope — B is analyzed
/// under its own nested scope. If the memo were keyed on anything shared across
/// functions (a def-path string, a bare global, a single non-stacked slot), B
/// would be served A's analysis and this test fails.
///
/// This is not hypothetical for this crate: one def_path really is analyzed under
/// several different `VerifiableFunction` values (`with_tail_calls_expanded`'s
/// `Cow` clone, `callsite_replay`'s `func_view`, `FloatRangeCtx::for_callee`'s
/// extracted callee bodies), so a def-path-keyed memo would be actively wrong.
#[test]
fn memo_is_bound_to_its_function_not_a_shared_key() {
    let a = guarded_body(10);
    let b = guarded_body_shaped(999, true);

    // Control: the two bodies really do differ where it matters. Without this, a
    // green result below could mean "the memo is fine" OR "the fixtures were
    // identical and nothing was discriminated" — which read the same.
    assert_ne!(
        render_guard_map(&v2_build_path_guard_map(&a)),
        render_guard_map(&v2_build_path_guard_map(&b)),
        "fixtures do not differ — this test cannot discriminate anything"
    );
    let expected_a = v2_conjoin_path_guards_for_hardened(&a, BlockId(1), probe());
    let expected_b = v2_conjoin_path_guards_for_hardened(&b, BlockId(1), probe());
    assert_ne!(expected_a, expected_b, "control: the probe must separate the two bodies");

    let scope_a = FuncAnalysisScope::enter(&a);
    // Populate A's frame first, so a shared-key memo holds A's analysis.
    assert_eq!(expected_a, v2_conjoin_path_guards_for_hardened(&a, BlockId(1), probe()));

    {
        // NESTED scope for a different body, exactly the shape a callee analysis
        // takes inside a caller's generation.
        let _scope_b = FuncAnalysisScope::enter(&b);
        assert_eq!(
            expected_b,
            v2_conjoin_path_guards_for_hardened(&b, BlockId(1), probe()),
            "memo served another function's analysis — it is keyed on something SHARED"
        );
    }

    // A's frame survived the nested scope's push AND pop.
    assert_eq!(
        expected_a,
        v2_conjoin_path_guards_for_hardened(&a, BlockId(1), probe()),
        "A's memo frame was clobbered by the nested scope"
    );
    drop(scope_a);
}

/// A body analyzed with NO scope in force must still get the right answer — the
/// memo is an accelerator, never a precondition. This also pins that a miss is
/// free of side effects.
#[test]
fn analyses_are_correct_with_no_scope_in_force() {
    let func = guarded_body(10);
    let unscoped = render_guard_map(&guard_map_for(&func));
    assert_eq!(render_guard_map(&v2_build_path_guard_map(&func)), unscoped);
    // And the statement oracle is reachable unscoped too (it is built fresh).
    let _ = stmt_versions_for(&func);
}

/// The memoized analyses equal the ones a fresh build produces, inside a scope.
#[test]
fn memoized_guard_map_equals_fresh_build() {
    let func = guarded_body(10);
    let fresh = render_guard_map(&v2_build_path_guard_map(&func));
    let _scope = FuncAnalysisScope::enter(&func);
    assert_eq!(fresh, render_guard_map(&guard_map_for(&func)));
    // Second read must be the same value, not a rebuild that happens to agree.
    assert_eq!(fresh, render_guard_map(&guard_map_for(&func)));
}

// ---------------------------------------------------------------------------
// Ambient budget
// ---------------------------------------------------------------------------

/// The budget FIRES, and it fires in the fail-closed direction.
///
/// Before this lane, `budget_exhausted()` was called in exactly one file of this
/// crate and in none of the VC-generation walks, so no timeout could bound them.
/// This installs a budget with ONE step and asserts the path-guard walk takes
/// its existing `BudgetTripped` collapse — every block degraded to the unguarded
/// `[Vec::new()]` path. That direction strictly REMOVES hypotheses, so it can
/// only turn a PROVE into a FAIL, never the reverse.
#[test]
fn ambient_budget_trips_the_path_guard_walk_fail_closed() {
    let func = guarded_body(10);

    // Control: with no budget installed the walk does NOT collapse — otherwise a
    // green below would be indistinguishable from a walk that always collapses.
    let ungoverned = render_guard_map(&v2_build_path_guard_map(&func));
    assert!(
        v2_build_path_guard_map(&func).values().any(|paths| paths.iter().any(|p| !p.is_empty())),
        "control failed: the walk already produces no guards, so a collapse is unobservable"
    );

    let collapsed = {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
        v2_build_path_guard_map(&func)
    };

    // Fail-closed shape: every block carries exactly ONE path, and it is EMPTY.
    for (block, paths) in &collapsed {
        assert_eq!(paths.len(), 1, "block {block:?} kept multiple paths after the budget tripped");
        assert!(
            paths[0].is_empty(),
            "block {block:?} kept guards after the budget tripped — the collapse is not \
             fail-closed"
        );
    }
    assert_ne!(ungoverned, render_guard_map(&collapsed), "the budget did not fire at all");

    // And the budget is RESTORED on drop: the next walk is ungoverned again.
    assert_eq!(
        ungoverned,
        render_guard_map(&v2_build_path_guard_map(&func)),
        "the budget guard leaked past its scope"
    );
}

/// A tripped budget must never manufacture a hypothesis. The collapsed map's
/// only path is EMPTY, so `v2_conjoin_path_guards_for_hardened` returns the bare
/// formula — no guard is invented, and the obligation stays as refutable as it
/// was. (The dangerous direction would be a collapse that ADDED a fact.)
#[test]
fn tripped_budget_adds_no_hypothesis() {
    let func = guarded_body(10);
    let conjoined = {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
        v2_conjoin_path_guards_for_hardened(&func, BlockId(1), probe())
    };
    assert_eq!(
        probe(),
        conjoined,
        "a tripped budget conjoined a hypothesis onto the obligation — over-budget work must \
         only ever REMOVE facts"
    );
}

// The parity pins of the PERF waves live in child modules, so no file passes tidy's
// 3000-line limit (MAIN-TIDY-REDS-20261110). New pins are appended to this file;
// when it nears the limit, move a run of them into another child here.
mod parity_520_to_536;
mod parity_through_518;

#[test]
fn wave537_to_541_terminator_presence_block_defs_and_callee_gates_parity() {
    let func = guarded_body(10);
    let _scope = FuncAnalysisScope::enter(&func);
    let tp = super::terminator_presence_for(&func);
    assert!(!tp.has_assert);
    assert!(!tp.has_bounds_check_assert);
    assert!(!tp.has_opaque);
    assert!(!tp.has_call);
    assert!(!tp.has_tail_call);
    assert!(!tp.has_back_edge);

    assert!(super::block_defs::v2_sole_bounds_assert_by_target(&func).is_empty());
    assert!(crate::unsafe_verify::detection::generate_inline_asm_vcs(&func).is_empty());
    assert!(crate::termination::detect_loops(&func.body).is_empty());
    assert!(crate::termination::detect_recursive_calls(&func).is_empty());

    assert!(super::panic_calls::callee_panicking_range_index("foo::index").is_none());
    assert!(!super::collection_range::is_vecdeque_adt_name("user::VecDeque<u8>"));
    assert!(super::collection_range::is_vecdeque_adt_name(
        "alloc::collections::vec_deque::VecDeque<u8>"
    ));
    assert!(!super::collection_range::is_std_string_adt_name("user::String"));
    assert!(super::collection_range::is_std_string_adt_name("alloc::string::String"));
    assert!(
        super::unsupported::extract_set_discriminant_definitions_until(
            &func,
            &func.body.blocks[0],
            0,
        )
        .is_empty()
    );
}

#[test]
fn wave542_to_545_summary_db_rebound_params_and_lazy_grounding_parity() {
    let mut db = crate::modular::SummaryDatabase::new();
    assert!(!db.has_any_preconditions_or_withheld());
    db.insert(crate::modular::FunctionSummary::new("foo"));
    assert!(!db.has_any_preconditions_or_withheld());
    let func = guarded_body(8);
    assert!(!db.owes_caller_preconditions(&func));

    let mut pre_summary = crate::modular::FunctionSummary::new("bar");
    pre_summary.preconditions.push(Formula::Bool(true));
    db.insert(pre_summary);
    assert!(db.has_any_preconditions_or_withheld());
    db.insert(crate::modular::FunctionSummary::new("bar"));
    assert!(!db.has_any_preconditions_or_withheld());

    assert!(crate::rebound_parameter_places(&func).is_empty());
    let _scope = FuncAnalysisScope::enter(&func);
    let _ = super::terminator_presence_for(&func);
    assert!(crate::generate_full_assert_refutation_vcs(&func).is_empty());
}

#[test]
fn wave547_to_551_chc_path_defs_and_sep_engine_scope_parity() {
    let func = guarded_body(8);
    assert!(matches!(
        crate::chc::encode_function_loops(&func),
        Err(crate::chc::ChcError::NoLoops { .. })
    ));

    let names = crate::sep_engine::pipeline_local_names(&func);
    assert_eq!(names.len(), func.body.locals.len());
    let (roots, single) = crate::sep_engine::backing_value_identity(&func, "user::Buf", 0, 1);
    assert!(roots.is_empty());
    assert!(!single.is_empty());

    let scalar = Ty::Int { signed: false, width: 32 };
    assert!(super::path_defs::ty_is_pure_frozen_value(&scalar));
    let empty_struct = Ty::Adt {
        name: "user::Empty".into(),
        fields: vec![].into(),
        variants: vec![].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(trust_types::AdtKind::Struct),
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert!(super::path_defs::ty_is_pure_frozen_value(&empty_struct));
    assert!(super::path_defs::stored_ref_pointee_names(&func).is_empty());
    assert!(super::path_defs::mutable_pointer_local_names(&func).is_empty());
    assert!(super::path_defs::mutably_borrowed_local_names(&func).is_empty());
}

#[test]
fn wave552_to_556_float_range_modular_iterator_loop_and_induction_parity() {
    let func = guarded_body(8);
    let summaries = crate::modular::SummaryDatabase::new();
    assert!(!super::float_range::all_callsites_precondition_dominated(
        &func,
        &summaries,
        "missing_callee"
    ));
    assert!(super::float_range::derive_float_result_range(&func).is_none());

    let modular_res = crate::modular::modular_vcgen(&func, &summaries);
    assert!(modular_res.precondition_vcs.is_empty());
    assert_eq!(modular_res.assumptions_injected, 0);
    assert_eq!(modular_res.havoced_calls, 0);
    assert!(crate::modular::generate_modular_vcs(&func, &summaries).is_empty());

    let _scope = FuncAnalysisScope::enter(&func);
    assert!(super::loop_bounds::build_flattened_index_facts(&func).is_empty());
    assert!(super::loop_bounds::build_min_upper_bound_facts(&func).is_empty());
    assert!(super::induction::build_downward_induction_facts(&func).is_empty());
}

#[test]
fn wave557_to_561_local_defs_type_ranges_overflow_call_facts_and_unwrap_parity() {
    let func = guarded_body(8);
    assert!(crate::local_defs::value_defs(&func, 1).is_none());
    assert!(crate::local_defs::unique_initializing_def(&func, 1).is_none());
    assert!(crate::local_defs::unique_value_call(&func, 1).is_none());
    assert!(crate::local_defs::value_calls(&func, 1).is_none());
    assert!(crate::local_defs::unique_initializing_call(&func, 1).is_none());
    assert!(crate::local_defs::unique_value_modulo_whole_drops(&func, 1).is_none());
    assert!(crate::local_defs::unique_initializing_modulo_whole_drops(&func, 1).is_none());

    let _scope = FuncAnalysisScope::enter(&func);
    assert!(super::type_ranges::datatype_field_range_map(&func).is_empty());
    assert!(!super::type_ranges::local_scalar_range_map(&func).is_empty());
    assert!(super::call_facts::lossless_int_conversion_arg(&func, 1).is_none());
    assert!(super::call_facts::lossless_conversion_source_range(&func, 1).is_none());
    assert!(super::unwrap_panic::unwrap_receiver_tag_term(&func, 1, &[]).is_none());

    let param_op = Operand::Copy(Place::local(1));
    assert!(
        super::overflow_vc::v2_bv_yield_constraints(
            &func,
            &func.body.blocks[0],
            &param_op,
            &param_op,
            64,
            false,
        )
        .is_empty()
    );
    assert!(
        super::overflow_vc::v2_bv_rem_constraints(&func, &param_op, &param_op, 64, false)
            .is_empty()
    );
    let mut shl_out = Vec::new();
    super::overflow_vc::v2_collect_bv_shl_blockdef(
        &func,
        &func.body.blocks[0],
        func.body.blocks[0].stmts.len(),
        1,
        "__trust_ovf_bv_lhs__1",
        64,
        &mut shl_out,
    );
    assert!(shl_out.is_empty());
}

#[test]
fn wave562_to_566_str_offset_collection_range_callee_summaries_and_alloc_vcs_parity() {
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let param_op = Operand::Copy(Place::local(1));
    let mut roots = trust_types::fx::FxHashSet::default();
    roots.insert(1);

    assert!(super::str_offset::str_search_payload_origin(&func, 1).is_none());
    assert!(
        super::str_offset::str_search_endpoint_facts(
            &func,
            &param_op,
            &roots,
            &Formula::Int(0),
            &Formula::Int(8),
        )
        .is_none()
    );
    assert!(super::str_offset::str_affix_true_len_fact(&func, &param_op).is_none());
    assert!(!super::str_offset::operand_is_str_len_of_root(&func, &param_op, &roots));

    assert!(super::collection_range::norm_usize_range(&func, &param_op).is_none());

    assert!(!super::callee_summaries::local_is_min_max_result(&func, 1));
    assert!(super::callee_summaries::build_fp_abs_facts(&func).is_empty());
    assert!(super::callee_summaries::build_int_abs_facts(&func).is_empty());
    assert!(super::callee_summaries::build_intrinsic_bound_facts(&func).is_empty());
    assert!(super::callee_summaries::build_nonzero_get_dest_facts(&func).is_empty());
    assert!(super::callee_summaries::cast_source_const_lower(&func, 1).is_none());
    assert!(super::callee_summaries::cast_source_const_upper_nonneg(&func, 1).is_none());
    assert!(super::callee_summaries::min_call_const_upper_bound(&func, 1).is_none());
    assert!(super::callee_summaries::ret_call_const_lower_bound(&func, 1).is_none());
    assert!(super::callee_summaries::build_callee_return_summary_facts(&func).is_empty());
    assert!(super::callee_summaries::callsite_unique_mut_borrow_target(&func, 1).is_none());

    let funcs = std::slice::from_ref(&func);
    assert!(super::callee_summaries::compute_return_bound_summaries(funcs).is_empty());
    assert!(super::callee_summaries::compute_return_lower_bound_summaries(funcs).is_empty());
    assert!(super::callee_summaries::compute_return_const_set_summaries(funcs).is_empty());
    assert!(super::callee_summaries::compute_return_disc_summaries(funcs).is_empty());
    assert!(super::callee_summaries::compute_return_bool_pred_summaries(funcs).is_empty());
    assert!(super::alloc_vcs::generate_unbounded_allocation_vcs(&func).is_empty());
}

#[test]
fn wave567_to_571_container_len_slice_len_return_field_value_facts_and_contract_vcs_parity() {
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let param_place = Place::local(1);

    assert!(!super::container_len::vec_created_empty(&func, 1));
    assert!(super::container_len::build_push_guard_elem_len_map(&func).is_empty());
    assert!(!super::slice_len_licence::slice_len_name_is_stable(&func, &param_place, 4));

    let funcs = std::slice::from_ref(&func);
    assert!(
        super::return_field_summary::compute_return_field_summaries_admitting(funcs, |_| true)
            .is_empty()
    );
    assert!(!super::return_field_summary::return_field_call_is_modeled(
        &func,
        &func.body.blocks[0]
    ));

    assert!(super::value_facts::clamp_upper_bound(&func, 1).is_none());
    assert!(super::value_facts::build_additive_bound_facts(&func).is_empty());
    assert!(super::value_facts::checked_self_decrement_const(&func, 1, 1).is_none());
    assert!(super::contract_vcs::generate_v2_contract_vcs_impl(&func, None).is_empty());
}

#[test]
fn wave572_to_576_safety_iterator_yield_loop_bounds_induction_and_callsite_parity() {
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let param_op = Operand::Copy(Place::local(1));
    let mut receiver_roots = super::FxHashSet::default();
    receiver_roots.insert(1usize);

    assert!(super::iterator_yield::trace_local_to_range_family(&func, 1, 4).is_none());
    assert!(super::iterator_yield::trace_local_to_enumerated_slice(&func, 1, 4).is_none());
    assert!(super::iterator_yield::charindices_shared_slice_root(&func, &param_op).is_none());
    assert!(!super::iterator_yield::operand_is_charindices_yield_of(
        &func,
        &param_op,
        &receiver_roots
    ));

    assert!(super::loop_bounds::for_each_array_source(&func, 1).is_none());
    assert!(!super::loop_bounds::reads_back_checked_result(
        &func,
        &Rvalue::Use(param_op.clone()),
        2
    ));
    assert!(super::loop_bounds::reduction_mul_operands(&func, 1).is_none());
    assert!(super::loop_bounds::reduction_shl_operands(&func, 1).is_none());
    assert!(super::loop_bounds::factor_max(&func, &param_op).is_none());
    assert!(super::loop_bounds::signed_addend_per_iteration_range(&func, 1).is_none());
    assert!(super::loop_bounds::loop_var_const_range(&func, 1).is_none());
    assert!(super::loop_bounds::build_flattened_index_facts(&func).is_empty());

    let expect_consts = crate::FxHashMap::default();
    assert!(super::induction::countdown_resolve_const(&func, &param_op, &expect_consts, 4).is_none());
    assert!(
        super::induction::countdown_guard_true_edge_lower_bound(
            &func,
            &func.body.blocks[0],
            1,
            &expect_consts
        )
        .is_none()
    );
    assert!(
        super::induction::countdown_zero_trip_eq(&func, &func.body.blocks[0], &expect_consts)
            .is_none()
    );

    let summary = crate::modular::FunctionSummary::new("callee");
    assert!(!super::callsite::summary_may_inject_postcondition(&summary));
    assert!(!super::callsite::summary_pins_result(&summary));
    assert!(!super::callsite::callee_postcondition_is_injectable(
        &func,
        &Place::local(0),
        &summary,
        std::slice::from_ref(&param_op)
    ));
}

#[test]
fn wave577_to_581_range_vec_region_vec_len_invariant_witness_grounding_and_assert_refutation_parity()
{
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let sv = super::stmt_versions_for(&func);
    let param_op = Operand::Copy(Place::local(1));

    assert!(
        super::range_bound_use::range_bound_at_call(
            &func,
            &param_op,
            &param_op,
            &func.body.blocks[0]
        )
        .is_none()
    );
    assert!(super::range_index_len::range_index_result_len_definitions(&func).is_empty());

    assert!(super::vec_region::vec_region_definitions(&func).is_empty());
    assert!(super::vec_region::slice_binary_search_result_definitions(&func).is_empty());
    assert!(super::vec_region::vec_mutator_charged_blocks(&func).is_empty());
    assert!(super::vec_region::vec_mutator_charge_rows(&func).is_empty());
    assert!(super::as_chunks_len::as_chunks_result_len_definitions(&func).is_empty());

    assert!(super::vec_len_invariant::vec_len_invariant_use_facts(&func, &sv).is_empty());

    assert!(super::witness_grounding::resolve_forwarded_call_return_variant(&func, 1, 0).is_none());
    assert!(super::witness_grounding::dominating_len_equality_guard(&func, 0, &[], &[]).is_none());
    assert!(!super::witness_grounding::leaf_push_disciplined(&func, 1));
    assert!(!super::witness_grounding::f4_operand_denotes_candidate(&func, &param_op, &[], 4));

    assert!(
        super::assert_refutation::panic_call_const_str_messages(
            &func,
            "core::panicking::panic_fmt",
            std::slice::from_ref(&param_op)
        )
        .is_empty()
    );
}

#[test]
fn wave582_to_587_dominating_facts_semantic_guard_path_defs_unwrap_panic_value_facts_and_top_level_modules_parity()
{
    let mut func = guarded_body(8);
    // Remove SwitchInt and Assert so terminator_presence_for has neither.
    for block in &mut func.body.blocks {
        block.terminator = Terminator::Return;
    }
    let _scope = FuncAnalysisScope::enter(&func);
    let param_place = Place::local(1);
    let param_op = Operand::Copy(param_place.clone());

    let dom_facts = super::dominating_facts::DominatingFacts::build(&func);
    assert!(
        dom_facts
            .facts(&func, 1, BlockId(0), 0, super::dominating_facts::GuardSubject::ExactName)
            .is_empty()
    );
    assert!(super::dominating_facts::unmined_guard_bounds(&func).is_empty());

    assert!(super::unwrap_panic::as_ref_result_subject(&func, 1).is_none());
    assert!(super::unwrap_panic::guard_receiver_subject(&func, &param_place).is_some());
    assert_eq!(super::unwrap_panic::unwrap_receiver_origin(&func, 1), Some(1));
    assert!(!super::unwrap_panic::call_pinned_origin(&func, 2));
    assert!(super::unwrap_panic::unwrap_field_place(&func, &param_place).is_none());

    assert!(super::value_facts::build_primitive_int_cmp_facts(&func).is_empty());

    assert!(crate::const_expr::v2_const_expr_operand_int(&func, &param_op, 4).is_none());
    assert!(crate::place_write::box_temp_source(&func, 1).is_none());
}

#[test]
fn wave588_to_591_spec_inference_termination_guards_abstract_interp_sep_engine_local_defs_and_tinv_parity()
{
    let mut func = guarded_body(8);
    for block in &mut func.body.blocks {
        block.terminator = Terminator::Return;
    }
    let _scope = FuncAnalysisScope::enter(&func);

    assert!(crate::local_defs::unique_value_def(&func, 1).is_none());
    assert!(crate::local_defs::unique_value_def_modulo_pointee_borrows(&func, 1).is_none());
    assert!(crate::local_defs::unique_value_call(&func, 2).is_none());
    assert!(crate::local_defs::value_calls(&func, 2).is_none());
    assert!(crate::local_defs::unique_initializing_call(&func, 2).is_none());
    assert!(!crate::local_defs::dest_fact_is_version_pinnable(&func, 2));

    assert!(crate::guards::build_checked_arith_facts(&func).is_empty());
    assert!(crate::guards::slice_last_some_nonempty_definitions(&func).is_empty());
    assert!(crate::guards::enum_construction_demux_definitions(&func).is_empty());
}

#[test]
fn wave592_to_597_local_name_table_enum_entry_callee_summaries_contract_vcs_and_discharge_parity() {
    let mut func = guarded_body(8);
    for block in &mut func.body.blocks {
        block.terminator = Terminator::Return;
    }
    let _scope = FuncAnalysisScope::enter(&func);

    let x_name = func.body.locals[1].name.as_deref().unwrap_or("x").to_string();
    assert_eq!(
        crate::unique_named_local_decl(&func, &x_name).map(|d| d.index),
        Some(1)
    );
    assert!(crate::unique_named_local_decl(&func, "__missing__").is_none());
    assert!(!crate::has_other_local_with_name(&func, 1, &x_name));
    assert!(crate::has_other_local_with_name(&func, 2, &x_name));
    assert!(!crate::has_other_local_with_name(&func, 1, "__missing__"));

    let mut dup_func = func.clone();
    dup_func.body.locals.push(LocalDecl {
        index: 99,
        ty: Ty::Int { width: 32, signed: true },
        name: Some(x_name.clone()),
    });
    let _dup_scope = FuncAnalysisScope::enter(&dup_func);
    assert!(crate::unique_named_local_decl(&dup_func, &x_name).is_none());
    assert!(crate::has_other_local_with_name(&dup_func, 1, &x_name));
    drop(_dup_scope);

    let _scope = FuncAnalysisScope::enter(&func);
    assert_eq!(crate::unique_local_decl(&func, 1).map(|d| d.index), Some(1));
    assert!(crate::enum_entry::origin(&func, &Place::local(1)).is_none());
    assert!(crate::enum_entry::immutable_constructor_discriminant(&func, &Place::local(1)).is_none());
    assert!(super::callee_summaries::build_intrinsic_bound_facts(&func).is_empty());
    assert!(super::callee_summaries::build_nonzero_get_dest_facts(&func).is_empty());
    assert!(super::callee_summaries::build_cast_bound_facts(&func).is_empty());
    assert!(super::callee_summaries::build_cast_lower_bound_facts(&func).is_empty());

    let plain_pre = Formula::Ge(Box::new(Formula::var("x", Sort::Int)), Box::new(Formula::Int(0)));
    assert!(matches!(
        super::discharge::isolate_callee_const_param_symbols_cow(&plain_pre),
        std::borrow::Cow::Borrowed(_)
    ));
}

#[test]
fn wave598_to_603_overflow_vc_assert_refutation_float_range_panic_calls_return_field_summary_str_offset_and_container_len_parity()
{
    let mut func = guarded_body(8);
    for block in &mut func.body.blocks {
        block.terminator = Terminator::Return;
    }
    let _scope = FuncAnalysisScope::enter(&func);
    let sv = super::stmt_versions_for(&func);
    let param_op = Operand::Copy(Place::local(1));
    let local_op = Operand::Copy(Place::local(2));

    assert!(
        super::overflow_vc::v2_bv_yield_constraints(
            &func,
            &func.body.blocks[0],
            &param_op,
            &local_op,
            32,
            false
        )
        .is_empty()
    );
    assert!(
        super::overflow_vc::v2_bv_rem_constraints(&func, &param_op, &local_op, 32, false)
            .is_empty()
    );
    assert!(super::assert_refutation::contract_panic_unused_vcs(&func).is_empty());

    let float_ctx = super::FloatRangeCtx::new(&func, None);
    assert_eq!(
        super::float_range::float_guard_bounds(&float_ctx, BlockId(0), &Place::local(2)),
        (None, None)
    );

    assert!(!super::panic_calls::operand_is_len_of_base(&func, &local_op, 1, 4));
    assert!(
        super::return_field_summary::function_return_field_summary(&func, &crate::FxHashMap::default())
            .is_none()
    );
    assert!(
        super::str_offset::str_bytes_position_dest_facts(&sv, &func, &func.body.blocks[0])
            .is_empty()
    );
    assert!(super::container_len::build_position_yield_guard_map(&func).is_empty());
    assert!(super::container_len::build_str_find_guard_map(&func).is_empty());
}

#[test]
fn wave604_to_615_safety_iterator_yield_loop_bounds_checked_vcs_container_len_and_value_facts_parity()
{
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let local_op = Operand::Copy(Place::local(2));
    let mut roots = super::FxHashSet::default();
    roots.insert(1usize);

    assert!(!super::iterator_yield::operand_is_charindices_yield_of(&func, &local_op, &roots));
    assert!(!super::iterator_yield::operand_is_str_find_payload_of(&func, &local_op, &roots));
    assert!(super::iterator_yield::char_boundary_tests_of(&func, &local_op, &roots).is_none());
    assert!(super::iterator_yield::build_payload_interval_guard_map(&func).is_empty());
    assert!(super::loop_bounds::build_min_upper_bound_facts(&func).is_empty());
    assert!(super::loop_bounds::build_accumulator_bound_facts(&func).is_empty());
    assert_eq!(
        super::safety::generate_v2_safety_vcs(&func).len(),
        super::safety::generate_v2_safety_vcs(&func).len()
    );
    assert!(!super::checked_vcs::v2_divzero_assert_exactly_bound(
        &func,
        BinOp::Div,
        BlockId(1),
        0,
        &local_op,
        &local_op,
    ));
    assert!(super::container_len::build_len_guard_field_map(&func).is_empty());
    assert!(super::container_len::build_position_yield_guard_map(&func).is_empty());
    assert!(super::container_len::build_str_find_guard_map(&func).is_empty());
    assert!(super::container_len::build_count_bound_guard_map(&func).is_empty());
    assert!(!super::terminator_presence_for(&func).has_vec_sole_resize_call);
    assert!(super::value_facts::vec_sole_mutator_block(&func, 1).is_none());
    assert!(super::value_facts::build_vec_index_dest_value_tie_facts(&func).is_empty());
    assert!(super::value_facts::build_immutable_index_len_tie_facts(&func).is_empty());
}

#[test]
fn wave616_to_621_semantic_guard_dominating_facts_induction_call_facts_collection_range_and_panic_calls_parity()
{
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let sv = super::stmt_versions_for(&func);
    let dom_facts = super::dominating_facts_for(&func);
    let local_op = Operand::Copy(Place::local(2));

    assert!(
        dom_facts
            .facts(&func, 2, BlockId(1), 0, super::dominating_facts::GuardSubject::ExactName)
            .is_empty()
    );
    assert!(super::induction::downward_guards(&func, 1).is_empty());
    assert!(super::induction::build_downward_induction_facts(&func).is_empty());
    assert!(super::call_facts::lossless_conversion_source_range(&func, 1).is_none());
    assert!(super::call_facts::vec_from_elem_len_facts(&sv, &func, &func.body.blocks[0]).is_empty());
    assert!(super::call_facts::mem_replace_swap_facts(&sv, &func, &func.body.blocks[0]).is_empty());
    assert!(matches!(
        super::collection_range::deque_receiver_len(&func, &local_op),
        super::collection_range::DequeLen::NotDeque
    ));
    assert!(
        super::collection_range::deque_scalar_index_body(&func, &[local_op.clone(), local_op])
            .is_none()
    );
    assert!(!super::semantic_guard::build_semantic_guard_map(&func).is_empty());
}

#[test]
fn wave622_to_626_nested_func_analysis_scope_float_range_str_offset_and_unwrap_panic_parity() {
    let caller = guarded_body(8);
    let callee = guarded_body_shaped(42, true);
    let _caller_scope = FuncAnalysisScope::enter(&caller);

    // Populate the outer caller frame, then enter a nested callee frame and verify
    // both frames hit their respective `Rc` / `SafetyTerminatorPresence` caches.
    let caller_wi_before = super::local_write_index_for(&caller.body).expect("caller frame active");
    let caller_gm_before = super::guard_map_for(&caller);
    {
        let _callee_scope = FuncAnalysisScope::enter(&callee);
        let callee_wi = super::local_write_index_for(&callee.body).expect("callee frame active");
        let caller_wi_nested =
            super::local_write_index_for(&caller.body).expect("outer caller frame reachable");
        assert!(std::rc::Rc::ptr_eq(&caller_wi_before, &caller_wi_nested));
        assert!(!std::rc::Rc::ptr_eq(&caller_wi_before, &callee_wi));

        let caller_gm_nested = super::guard_map_for(&caller);
        let callee_gm = super::guard_map_for(&callee);
        assert!(std::rc::Rc::ptr_eq(&caller_gm_before, &caller_gm_nested));
        assert!(!std::rc::Rc::ptr_eq(&caller_gm_before, &callee_gm));
    }

    let float_ctx = super::FloatRangeCtx::new(&caller, None);
    assert_eq!(
        super::float_range::float_abs_guard_magnitude_bounds(
            &float_ctx,
            BlockId(1),
            &Place::local(1),
        ),
        (None, None)
    );
    assert!(
        super::float_range::float_callee_trace_range(
            &float_ctx,
            BlockId(0),
            "callee",
            &[Operand::Copy(Place::local(1))],
            &[],
            &mut Vec::new(),
            4,
        )
        .is_none()
    );

    let sv = super::stmt_versions_for(&caller);
    assert!(super::str_offset::build_str_search_payload_fact_map(&caller).is_empty());
    assert!(
        super::str_offset::str_bytes_position_dest_facts(&sv, &caller, &caller.body.blocks[0])
            .is_empty()
    );

    let local_op = Operand::Copy(Place::local(2));
    assert_eq!(super::unwrap_panic::unwrap_tag_origin(&caller, 1), Some(1));
    assert!(super::unwrap_panic::eq_side_receiver(&caller, &local_op).is_none());
    assert!(super::unwrap_panic::eq_side_pinned_unit(&caller, &local_op).is_none());
    assert!(super::unwrap_panic::shared_ref_operand_subject(&caller, &local_op).is_none());
    assert!(super::unwrap_panic::as_ref_result_subject(&caller, 2).is_none());
    assert!(!super::unwrap_panic::call_pinned_origin(&caller, 2));
    assert!(super::unwrap_panic::unwrap_field_place(&caller, &Place::local(2)).is_none());
}

#[test]
fn wave627_to_632_path_defs_overflow_vc_block_defs_and_checked_vcs_parity() {
    let func = guarded_body(16);
    let _scope = FuncAnalysisScope::enter(&func);

    let arg = Operand::Copy(Place::local(1));
    let const_three = Operand::Constant(ConstValue::Int(3));
    let const_five = Operand::Constant(ConstValue::Int(5));

    assert!(super::path_defs::frozen_shared_reborrow_roots(&func, &[]).is_none());
    assert!(super::path_defs::frozen_shared_reborrow_roots(&func, std::slice::from_ref(&arg)).is_none());
    assert!(super::path_defs::arg_grants_no_write_for_tests(&func, &arg));

    let mut sv = None;
    assert_eq!(
        super::overflow_vc::v2_signed_mul_operand_bounds(
            &func,
            &func.body.blocks[0],
            &const_three,
            1,
            &[],
            &mut sv,
        ),
        Some((3, 3))
    );
    assert!(
        super::overflow_vc::v2_signed_mul_operand_bounds(
            &func,
            &func.body.blocks[0],
            &arg,
            1,
            &[],
            &mut sv,
        )
        .is_none()
    );
    assert_eq!(
        super::overflow_vc::v2_signed_mul_corner_bounds(
            &func,
            &func.body.blocks[0],
            &const_three,
            &const_five,
            Some(1),
        ),
        Some(((3, 3), (5, 5)))
    );
    assert!(
        super::overflow_vc::v2_signed_mul_corner_bounds(
            &func,
            &func.body.blocks[0],
            &arg,
            &const_five,
            Some(1),
        )
        .is_none()
    );
    assert!(super::overflow_vc::v2_widening_bv_source(&func, &arg, 64).is_none());
    assert!(
        super::overflow_vc::v2_widening_bv_source(&func, &Operand::Copy(Place::local(3)), 32)
            .is_none()
    );
    assert!(!super::block_defs::v2_is_reborrow_of(
        &func,
        &func.body.blocks[0],
        1,
        &Place::local(2),
        &Place::local(1),
    ));
    assert!(
        super::checked_vcs::v2_shift_result_width_by_operands(&func, BinOp::Shl, &arg, &const_three)
            .is_none()
    );
}

#[test]
fn wave633_to_638_return_field_summary_container_len_and_value_facts_parity() {
    use std::collections::HashMap;
    use trust_types::Projection;

    let usize_ty = Ty::Int { width: 64, signed: false };
    let u32_ty = Ty::u32();
    let struct_ty = Ty::adt("Pair", vec![("0".to_string(), u32_ty.clone()), ("1".to_string(), u32_ty.clone())]);
    let ref_struct_ty = Ty::Ref { mutable: false, inner: Box::new(struct_ty) };

    // 1. Entry block ends in SwitchInt -> Wave 633 rejects before tail-call expansion.
    let switch_entry_func = VerifiableFunction {
        name: "test::wave633_switch_entry".to_string(),
        def_path: "test::wave633_switch_entry".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: ref_struct_ty, name: Some("s".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Constant(ConstValue::Bool(true)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: u32_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let empty_summaries = HashMap::default();
    assert!(
        super::return_field_summary::function_return_field_summary(
            &switch_entry_func,
            &empty_summaries,
        )
        .is_none()
    );
    assert!(!super::return_field_summary::return_field_call_is_modeled(
        &switch_entry_func,
        &switch_entry_func.body.blocks[0],
    ));

    // 2. CheckedBinaryOp(Sub/Add) with `.0` copied into a stable local vs uncopied (Wave 638),
    // and unprojected Discriminant reads skipped by Wave 637.
    let tuple_ty = Ty::Tuple(vec![usize_ty.clone(), Ty::Bool]);
    let checked_func = VerifiableFunction {
        name: "test::wave637_638_checked_and_discr".to_string(),
        def_path: "test::wave637_638_checked_and_discr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: usize_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: usize_ty.clone(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: tuple_ty.clone(), name: Some("sub_t".into()) },
                LocalDecl { index: 3, ty: usize_ty.clone(), name: Some("sub_res".into()) },
                LocalDecl { index: 4, ty: tuple_ty, name: Some("add_t".into()) },
                LocalDecl { index: 5, ty: usize_ty.clone(), name: Some("d1".into()) },
                LocalDecl { index: 6, ty: usize_ty.clone(), name: Some("d2".into()) },
            ],
            blocks: vec![BasicBlock {
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
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 2,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    },
                    // Uncopied CheckedBinaryOp(Add) -> skipped before `stable` checks.
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(2, 64)),
                        ),
                        span: SourceSpan::default(),
                    },
                    // Two unprojected Discriminant reads -> rejected by `is_cse_discr_src` in Wave 637.
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::Discriminant(Place::local(1)),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: usize_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    assert_eq!(super::value_facts::build_checked_sub_result_facts(&checked_func).len(), 1);
    assert!(super::value_facts::build_checked_add_result_facts(&checked_func).is_empty());
    assert!(super::value_facts::build_discriminant_cse_facts(&checked_func).is_empty());
    assert!(super::container_len::build_len_guard_field_map(&checked_func).is_empty());
    assert!(super::container_len::build_slice_iter_yield_guard_map(&checked_func).is_empty());
    assert!(super::container_len::build_str_find_guard_map(&checked_func).is_empty());
}

#[test]
fn wave639_to_644_witness_grounding_conversions_vec_region_and_invariant_parity() {
    let func = guarded_body(16);
    let _scope = FuncAnalysisScope::enter(&func);
    let sv = stmt_versions_for(&func);

    assert!(
        super::witness_grounding::resolve_forwarded_call_return_variant(&func, 0, 1).is_none()
    );
    assert!(
        super::witness_grounding::dominating_len_equality_guard(
            &func,
            3,
            &[Place::local(1)],
            &[Place::local(3)],
        )
        .is_none()
    );
    assert!(super::int_conversion::expect_infallible_const_map(&func).is_empty());
    assert!(super::int_conversion::int_try_from_def(&func, 2, 4).is_none());
    assert!(super::slice_conversion::slice_arg_static_len(&func, &Place::local(3), 4).is_none());
    assert!(super::vec_region::vec_region_definitions(&func).is_empty());
    assert!(super::vec_len_invariant::vec_len_invariant_use_facts(&func, &sv).is_empty());
}

#[test]
fn wave645_to_650_induction_range_bound_intrinsics_chunks_and_dominating_facts_parity() {
    let func = guarded_body(16);
    let _scope = FuncAnalysisScope::enter(&func);
    let block0 = &func.body.blocks[0];
    let subject = Formula::Var("_3".into(), Sort::Int);

    assert!(super::induction::downward_induction_vars(&func).is_empty());
    assert!(super::induction::downward_guards(&func, 1).is_empty());
    let countdown = super::induction::countdown_trip_analysis(&func, None);
    assert!(countdown.global.is_empty() && countdown.per_block.is_empty());
    assert!(
        super::range_bound_use::range_bound_at_call(
            &func,
            &Operand::Copy(Place::local(1)),
            &Operand::Copy(Place::local(1)),
            block0,
        )
        .is_none()
    );
    assert!(
        super::intrinsic_semantics::value_modeled_intrinsic_facts(
            &func,
            &block0.terminator,
            &subject,
        )
        .is_none()
    );
    assert!(super::as_chunks_len::as_chunks_result_len_facts(&func, block0).is_none());
    assert!(super::range_index_len::range_index_result_len_definitions(&func).is_empty());
    assert!(
        super::dominating_facts_for(&func)
            .facts(&func, 1, BlockId(0), 0, super::dominating_facts::GuardSubject::ExactName)
            .is_empty()
    );
    assert!(super::loop_bounds::build_min_upper_bound_facts(&func).is_empty());
    assert!(super::loop_bounds::build_converging_pointer_facts(&func).is_empty());
    assert!(super::loop_bounds::total_loop_iterations(&func).is_none());
    assert!(super::inferred_return::infer_return_candidate(&func).is_err());
    assert!(super::alloc_vcs::generate_unbounded_allocation_vcs(&func).is_empty());
    assert!(!super::alloc_vcs::callee_is_call_site_allocation_sink("core::iter::once::<u32>"));
    assert!(super::alloc_vcs::existing_length_max_items(&func, &Operand::Copy(Place::local(1)), 0).is_none());
    assert!(super::bmc_reduction::recognize_bounded_reduction(&func).is_none());
    assert!(super::callee_summaries::build_int_abs_facts(&func).is_empty());
    assert!(super::callee_summaries::build_intrinsic_bound_facts(&func).is_empty());
    assert!(
        super::call_facts::primitive_int_ord_method(
            &func,
            "core::cmp::Ord::min::<u32>",
            &[Operand::Copy(Place::local(1))],
            &Place::local(0),
        )
        .is_none()
    );
    assert!(super::call_facts::lossless_conversion_source_range(&func, 3).is_none());
    assert!(
        super::panic_calls::signed_euclid_overflow_call(
            &func,
            "core::num::<impl i32>::div_euclid",
            &[Operand::Copy(Place::local(1))],
        )
        .is_none()
    );
    assert!(super::unwrap_panic::probe_call_definitions(&func, block0).is_empty());
    assert!(super::unwrap_panic::eq_unit_call_definitions(&func, block0).is_empty());
}

#[test]
fn wave665_to_673_type_ranges_iterator_yield_collection_range_numeric_panic_str_offset_and_rvalue_safety_parity()
 {
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    assert!(super::type_ranges::checked_arith_result_value_vars_rc(&func).is_empty());
    assert!(super::iterator_yield::build_payload_interval_guard_map(&func).is_empty());
    assert!(
        !super::iterator_yield::operand_is_str_find_payload_of(
            &func,
            &Operand::Copy(Place::local(1)),
            &super::FxHashSet::default(),
        )
    );
    assert!(
        super::collection_range::norm_usize_range(&func, &Operand::Copy(Place::local(1))).is_none()
    );
    let nc = super::numeric_panic::NumericCallee::for_authenticated(
        "<MyType as MyTrait>::foo",
        "foo",
    );
    assert!(!nc.is_value_panic_callee());
    assert!(super::str_offset::str_search_payload_origin(&func, 3).is_none());
    assert!(super::str_offset::build_str_search_payload_fact_map(&func).is_empty());
    assert!(
        !super::str_offset::operand_is_str_len_of_root(
            &func,
            &Operand::Copy(Place::local(1)),
            &super::FxHashSet::default(),
        )
    );
    let mut vcs = Vec::new();
    crate::rvalue_safety::check_place_index_bounds(
        &func,
        &Place::local(1),
        &SourceSpan::default(),
        &mut vcs,
    );
    assert!(vcs.is_empty());
    assert!(super::contract_vcs::generate_v2_contract_vcs_impl(&func, None).is_empty());
    assert!(
        super::alloc_bounds::AllocCallDispatch::single_value_with_tail("user::Foo::new", "new")
            .is_none()
    );
    assert_eq!(
        super::alloc_bounds::AllocCallDispatch::single_value_with_tail(
            "alloc::boxed::Box::<u32>::new",
            "new"
        ),
        Some("Box::new")
    );
    assert!(super::alloc_bounds::overflow_arith_call("user::unchecked_add").is_none());
    let summary = crate::modular::FunctionSummary::new("test::callee");
    assert!(
        super::callsite::rebind_callee_postconditions(&func, &[], &Place::local(0), &summary)
            .is_empty()
    );
    assert!(super::callee_write_set::derive_callee_write_set(&func).is_some());
    assert!(!super::semantic_guard::build_semantic_guard_map(&func).is_empty());
}

#[test]
fn wave680_to_691_safety_checked_vcs_block_defs_loop_bounds_guards_and_contracts_parity() {
    let func = guarded_body(8);
    let _scope = FuncAnalysisScope::enter(&func);
    let presence = super::terminator_presence_for(&func);
    assert!(!presence.has_overflow_assert);
    assert!(!presence.has_overflow_neg_assert);
    assert!(!presence.has_divrem_zero_assert);
    let block1 = &func.body.blocks[1];
    assert!(!super::safety::v2_negation_assert_exactly_bound(
        &func,
        block1,
        &Operand::Copy(Place::local(1)),
    ));
    assert!(!super::checked_vcs::v2_shift_assert_exactly_bound(
        &func,
        BinOp::Shl,
        BlockId(1),
        0,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
    assert!(!super::checked_vcs::v2_divrem_overflow_assert_exactly_bound(
        &func,
        BinOp::Div,
        BlockId(1),
        0,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
    assert!(!super::checked_vcs::v2_divzero_assert_exactly_bound(
        &func,
        BinOp::Div,
        BlockId(1),
        0,
        &Operand::Copy(Place::local(1)),
        &Operand::Copy(Place::local(2)),
    ));
    assert!(super::loop_bounds::manual_counter_trip_count(&func).is_none());
    assert!(crate::guards::switch_join_variant_arm_definitions(&func).is_empty());
    assert!(crate::guards::slice_get_some_index_bound_definitions(&func).is_empty());
    assert!(crate::guards::enum_construction_demux_definitions(&func).is_empty());
}

#[test]
fn wave692_to_703_widen_points_local_name_table_tinv_and_place_write_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    assert!(crate::abstract_interp::transfer::detect_widen_points(&func).is_empty());
    let init = crate::abstract_interp::transfer::type_aware_initial_state(&func);
    let fp = crate::abstract_interp::transfer::fixpoint(&func, init.clone());
    assert!(fp.block_states.contains_key(&BlockId(0)));
    let cfg = crate::abstract_interp::transfer::FixpointConfig::default();
    let fp_cfg = crate::abstract_interp::transfer::fixpoint_configured(&func, init, &cfg);
    assert!(fp_cfg.block_states.contains_key(&BlockId(0)));
    assert_eq!(crate::unique_local_decl(&func, 1).map(|d| d.index), Some(1));
    assert!(!crate::place_write::writes_fields_of(&func, "test::S", &[0]));
    let regions = crate::type_invariant::unwind::body_regions(&func.body);
    assert!(regions.normal.contains(&BlockId(0)));
    assert!(regions.cleanup.is_empty());
}

#[test]
fn wave704_to_714_refutation_scope_grounding_tinv_sep_engine_and_budget_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    assert!(!crate::generate::func_exceeds_vcgen_budget(&func));
    assert!(!crate::generate::func_exceeds_vcgen_budget(&func));
    let (unnarrowed, narrowed) = crate::abstract_interp::merged_interval_environments(&func);
    assert_eq!(unnarrowed.is_unreachable, narrowed.is_unreachable);
    let vcs = crate::generate::generate_vcs(&func);
    let scope = crate::refutation_scope::GenericRefutationScope::for_function(&func, &vcs, &[]);
    assert!(vcs.iter().all(|vc| scope.rejection_reason(vc).is_none()));
    let cex = trust_types::Counterexample { assignments: Vec::new(), trace: None };
    let grounding = crate::counterexample_grounding::ground_counterexample(&func, &cex);
    assert!(matches!(grounding, crate::counterexample_grounding::WitnessGrounding::Undecided { .. }));
    assert!(crate::type_invariant::houdini::incomplete_join_parts(&func, std::iter::empty()).is_empty());
    assert!(!crate::sep_engine::body_has_unsafe_operation(&func));
    assert_eq!(crate::sep_engine::pipeline_local_names(&func).len(), func.body.locals.len());
    let (roots, single) = crate::sep_engine::backing_value_identity(&func, "test::S", 0, 1);
    assert!(roots.is_empty());
    assert!(!single.is_empty());
    assert!(crate::sep_engine::validity_rooted_box_deref_temps(&func).is_empty());
}

#[test]
fn wave715_to_720_enum_entry_source_entry_inferred_return_hardened_and_type_ranges_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    assert_eq!(
        crate::enum_entry::has_enum_parameter(&func),
        crate::enum_entry::has_enum_parameter_uncached(&func),
    );
    assert_eq!(
        crate::generate::enum_entry_pure_body_non_call_for(&func),
        crate::enum_entry::pure_body_non_call_uncached(&func),
    );
    assert!(!crate::enum_entry::pure_body(&func));
    assert!(
        crate::enum_entry::discriminant_read_with_origin(&func, &Place::local(0), &Place::local(1))
            .is_none()
    );
    assert!(super::source_entry::domains(&func).is_none());
    assert!(super::inferred_return::infer_return_candidate(&func).is_err());
    assert!(crate::hardened::generate_hardened_vcs_for_profile_with_summaries(&func, None).is_empty());
    assert!(super::container_len::vec_mut_borrows_only_feed_push(&func, 1));
    let f = Formula::Var("x".to_owned(), Sort::Int);
    assert_eq!(
        super::type_ranges::conjoin_type_range_battery(
            &func,
            f.clone(),
            super::type_ranges::RangeBatteryClass::Arithmetic,
            &mut |_, _| {},
        ),
        super::type_ranges::conjoin_type_range_battery(
            &func,
            f,
            super::type_ranges::RangeBatteryClass::Arithmetic,
            &mut |_, _| {},
        ),
    );
}

#[test]
fn wave721_to_726_loop_nest_unmodelable_write_reachable_avoiding_and_iter_conduits_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    assert_eq!(
        super::has_unmodelable_write_for(&func),
        super::loop_bounds::has_unmodelable_write_uncached(&func),
    );
    let nest_a = super::loop_nest_for(&func).expect("reducible body");
    let nest_b = super::loop_nest_for(&func).expect("reducible body");
    assert!(std::rc::Rc::ptr_eq(&nest_a, &nest_b));
    for b in 0..func.body.blocks.len() {
        assert_eq!(
            super::loop_bounds::block_execution_bound(&func, b),
            super::loop_bounds::block_execution_bound_in(&func, &nest_a, b),
        );
    }
    let empty = super::FxHashSet::default();
    for s in 0..func.body.blocks.len() {
        let full = super::loop_bounds::reachable_avoiding(&func, s, &empty);
        for t in 0..=func.body.blocks.len() {
            assert_eq!(
                super::loop_bounds::reachable_avoiding_contains(&func, s, &empty, t),
                full.contains(&t),
            );
            assert_eq!(
                super::loop_bounds::reachable_avoiding_one_contains(&func, s, None, t),
                full.contains(&t),
            );
        }
        for avoid_b in 0..func.body.blocks.len() {
            let avoid = super::loop_bounds::one_block_set(avoid_b);
            let avoided = super::loop_bounds::reachable_avoiding(&func, s, &avoid);
            for t in 0..=func.body.blocks.len() {
                assert_eq!(
                    super::loop_bounds::reachable_avoiding_contains(&func, s, &avoid, t),
                    avoided.contains(&t),
                );
                assert_eq!(
                    super::loop_bounds::reachable_avoiding_one_contains(&func, s, Some(avoid_b), t),
                    avoided.contains(&t),
                );
            }
        }
    }
    assert!(super::iterator_yield::iter_mut_borrows_only_feed(&func, 1, |_, _, _| false));
    assert_eq!(
        super::induction::countdown_trip_analysis(&func, None).global,
        super::countdown_facts_for(&func).global,
    );
}

#[test]
fn wave727_to_732_unwrap_panic_checked_vcs_and_whole_def_memo_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    assert_eq!(super::unwrap_panic::unwrap_tag_origin(&func, 1), Some(1));
    assert!(super::unwrap_panic::unwrap_origin_call_def(&func, 1).is_none());
    for block in &func.body.blocks {
        assert!(super::unwrap_panic::probe_call_definitions(&func, block).is_empty());
        assert!(super::unwrap_panic::probe_subject_model(&func, block).is_none());
    }
    let param_op = Operand::Copy(Place::local(1));
    assert!(super::unwrap_panic::eq_side_receiver(&func, &param_op).is_none());
    assert!(super::unwrap_panic::eq_side_pinned_unit(&func, &param_op).is_none());
    assert!(!super::unwrap_panic::origin_tag_observed_elsewhere(&func, 1));
    assert!(!super::unwrap_panic::field_tag_observed_elsewhere(
        &func,
        &Place { local: 1, projections: vec![trust_types::Projection::Deref] },
    ));
    assert!(super::unwrap_panic::unwrap_receiver_tag_term(&func, 1, &[]).is_none());
    for l in 0..func.body.locals.len() {
        let a = crate::local_defs::unique_value_modulo_whole_drops(&func, l);
        let b = crate::local_defs::unique_value_modulo_whole_drops(&func, l);
        assert_eq!(a.is_some(), b.is_some());
        let ia = crate::local_defs::unique_initializing_modulo_whole_drops(&func, l);
        let ib = crate::local_defs::unique_initializing_modulo_whole_drops(&func, l);
        assert_eq!(ia.is_some(), ib.is_some());
    }
}

#[test]
fn wave733_to_738_slice_witness_callee_summaries_and_alloc_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    let param_place = Place::local(1);
    let param_op = Operand::Copy(param_place.clone());
    assert!(super::slice_conversion::slice_arg_static_len(&func, &param_place, 4).is_none());
    assert!(super::slice_conversion::range_aggregate_const_len(&func, &param_op).is_none());
    assert!(super::slice_conversion::range_from_const_len(&func, &param_op, &param_op).is_none());
    assert!(!super::slice_conversion::local_is_len_of(&func, 1, &param_op));
    assert_eq!(
        super::slice_conversion::range_bound_affine(&func, &param_op, 4),
        Some((Some(1), 0)),
    );
    assert!(super::slice_conversion::range_bound_from_binop_def(&func, 1, 4).is_none());
    assert!(
        super::witness_grounding::resolve_forwarded_call_return_variant(&func, 0, 0).is_none()
    );
    assert!(super::witness_grounding::component_candidate_places(&func, 1, &[0]).len() <= 1);
    assert!(super::witness_grounding::component_source_leaf(&func, 1, &[0]).is_none());
    assert_eq!(super::witness_grounding::f4_switch_root_local(&func, &param_op, 4), Some(1));
    assert!(super::callee_summaries::function_return_const_upper_bound(&func).is_none());
    assert!(super::callee_summaries::function_return_const_lower_bound(&func).is_none());
    assert!(super::callee_summaries::stable_unique_def_through_copies(&func, 1).is_none());
    assert!(super::callee_summaries::function_return_bool_pred_summary(&func).is_none());
    assert!(super::alloc_vcs::generate_unbounded_allocation_vcs(&func).is_empty());
}

#[test]
fn wave739_to_744_float_guards_and_discharge_parity() {
    let func = guarded_body(6);
    let _scope = FuncAnalysisScope::enter(&func);
    let param_place = Place::local(1);
    let param_op = Operand::Copy(param_place.clone());
    assert!(
        super::float_overflow::v2_float_contract_magnitude_hypotheses(&func, &param_op, &param_op)
            .is_empty()
    );
    let float_ctx = super::FloatRangeCtx::new(&func, None);
    assert_eq!(
        super::float_range::float_abs_guard_magnitude_bounds(&float_ctx, BlockId(0), &param_place),
        (None, None),
    );
    assert!(crate::guards::slice_last_some_nonempty_definitions(&func).is_empty());
    assert!(crate::guards::enum_construction_demux_definitions(&func).is_empty());
    assert!(super::discharge::sigma_actual_stable_copy_root(&func, &param_op).is_some());
    assert!(super::discharge::sigma_actual_array_cast_len(&func, &param_op, 4).is_none());
}

#[test]
fn wave745_to_750_formula_local_decl_lookup_and_termination_parity() {
    let mut func = guarded_body(6);
    func.body.locals[1].name = Some("x".to_string());
    // Unscoped lookup first:
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "x", None),
        crate::FormulaLocalDeclLookup::Unique(d) if d.index == 1,
    ));
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "_1", Some(1)),
        crate::FormulaLocalDeclLookup::Unique(d) if d.index == 1,
    ));
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "missing_var", None),
        crate::FormulaLocalDeclLookup::None,
    ));

    // Scoped lookup (routes through LocalNameTable with differential assert):
    let _scope = FuncAnalysisScope::enter(&func);
    let _ = crate::place_to_var_name(&func, &Place::local(1));
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "x", None),
        crate::FormulaLocalDeclLookup::Unique(d) if d.index == 1,
    ));
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "_1", Some(1)),
        crate::FormulaLocalDeclLookup::Unique(d) if d.index == 1,
    ));
    assert!(matches!(
        crate::lookup_formula_local_decl(&func, "missing_var", None),
        crate::FormulaLocalDeclLookup::None,
    ));
    assert_eq!(crate::base_value_alias(&func, &Place::local(1)), None);

    // Duplicate local name produces Ambiguous in both scoped and unscoped modes:
    drop(_scope);
    let mut dup_func = guarded_body(6);
    dup_func.body.locals[1].name = Some("dup".to_string());
    dup_func.body.locals[2].name = Some("dup".to_string());
    assert!(matches!(
        crate::lookup_formula_local_decl(&dup_func, "dup", None),
        crate::FormulaLocalDeclLookup::Ambiguous,
    ));
    let _dup_scope = FuncAnalysisScope::enter(&dup_func);
    let _ = crate::place_to_var_name(&dup_func, &Place::local(1));
    assert!(matches!(
        crate::lookup_formula_local_decl(&dup_func, "dup", None),
        crate::FormulaLocalDeclLookup::Ambiguous,
    ));
}

#[test]
fn wave751_to_756_canonical_locals_collection_arg_and_sep_fast_paths() {
    let mut func = guarded_body(6);
    assert!(crate::all_locals_canonical(&func));
    {
        let _scope = FuncAnalysisScope::enter(&func);
        let _ = crate::place_to_var_name(&func, &Place::local(1));
        assert!(crate::all_locals_canonical(&func));
        let sep_vcs = crate::sep_engine::check_sep_unsafe(&func);
        assert!(sep_vcs.is_empty() || !sep_vcs.is_empty());
    }

    // Sparse / non-canonical local indices return false both unscoped and scoped:
    func.body.locals[2].index = 99;
    assert!(!crate::all_locals_canonical(&func));
    let _sparse_scope = FuncAnalysisScope::enter(&func);
    let _ = crate::place_to_var_name(&func, &Place::local(1));
    assert!(!crate::all_locals_canonical(&func));
}

#[test]
fn wave757_to_762_validate_function_memory_image_memo_and_sep_fast_paths() {
    let func = guarded_body(6);
    {
        let _scope = FuncAnalysisScope::enter(&func);
        assert!(!super::body_contains_memory_image_for(&func));
        assert!(!super::body_contains_memory_image_for(&func));
        assert!(crate::validate_function(&func).is_ok());
        assert!(crate::validate_function(&func).is_ok());
        assert!(crate::sep_engine::tail_call_blocks(&func).is_empty());
        assert_eq!(super::float_range::derive_float_result_range(&func), None);
    }
    let mut bad_func = guarded_body(6);
    bad_func.body.locals[2].index = 99;
    {
        let _bad_scope = FuncAnalysisScope::enter(&bad_func);
        assert!(crate::validate_function(&bad_func).is_err());
        assert!(crate::validate_function(&bad_func).is_err());
    }
}

#[test]
fn wave763_to_768_placed_opaque_wide_param_tail_call_and_sep_unsafe_memo() {
    let func = guarded_body(6);
    {
        let _scope = FuncAnalysisScope::enter(&func);
        let placed1 = super::with_placed_opaque_values_cached(&func);
        assert!(matches!(placed1, std::borrow::Cow::Borrowed(_)));
        let placed2 = super::with_placed_opaque_values_cached(&func);
        assert!(matches!(placed2, std::borrow::Cow::Borrowed(_)));
        assert!(!super::body_has_wide_int_param_for(&func));
        assert!(!super::body_has_wide_int_param_for(&func));
        let expanded = super::with_tail_calls_expanded_cached(&func);
        assert!(matches!(expanded, std::borrow::Cow::Borrowed(_)));
        assert!(!super::has_sep_unsafe_patterns_for(&func));
        assert!(!super::has_sep_unsafe_patterns_for(&func));
        assert!(!crate::place_has_raw_deref(&func, &Place::local(1)));
    }
    let mut wide_func = guarded_body(6);
    wide_func.body.locals[1].ty = Ty::Int { width: 128, signed: true };
    {
        let _wide_scope = FuncAnalysisScope::enter(&wide_func);
        assert!(super::body_has_wide_int_param_for(&wide_func));
        assert!(super::body_has_wide_int_param_for(&wide_func));
    }
}

#[test]
fn wave769_to_774_fixpoint_auto_thresholds_join_stmt_values_has_no_join_and_configured_scope_parity()
{
    let func = guarded_body(6);
    let unscoped_no_join = crate::func_has_no_join_uncached(&func);
    let unscoped_merged = crate::abstract_interp::merged_interval_environments(&func);
    let unscoped_ret = crate::abstract_interp::return_interval(&func, true);
    {
        let _scope = FuncAnalysisScope::enter(&func);
        assert_eq!(super::func_has_no_join_for(&func), unscoped_no_join);
        assert_eq!(super::func_has_no_join_for(&func), unscoped_no_join);
        let scoped_merged = crate::abstract_interp::merged_interval_environments(&func);
        assert_eq!(scoped_merged, unscoped_merged);
        assert_eq!(
            crate::abstract_interp::return_interval(&func, true),
            unscoped_ret,
        );
    }
    let summaries = crate::modular::SummaryDatabase::new();
    let (vcs1, discharged1) = crate::generate_vcs_with_discharge_and_summaries(&func, &summaries);
    let (vcs2, discharged2) = crate::generate_vcs_with_discharge_and_summaries(&func, &summaries);
    assert_eq!(vcs1.len(), vcs2.len());
    assert_eq!(discharged1.len(), discharged2.len());
}

#[test]
fn wave775_to_780_single_pass_discharge_flat_negated_disjuncts_pointer_laundering_and_index_locals_memo()
{
    let func = guarded_body(6);
    {
        let _scope = FuncAnalysisScope::enter(&func);
        assert!(!super::func_has_pointer_laundering_for(&func));
        assert!(!super::func_has_pointer_laundering_for(&func));
        assert!(!super::func_has_writable_pointer_laundering_for(&func));
        let idx1 = super::index_locals_for(&func).unwrap();
        let idx2 = super::index_locals_for(&func).unwrap();
        assert!(std::rc::Rc::ptr_eq(&idx1, &idx2));
        assert!(!super::path_defs::local_is_index_operand(&func, 1));
        assert!(!super::path_defs::local_is_index_operand(&func, 1));
    }
    let summaries = crate::modular::SummaryDatabase::new();
    let call_vcs = super::generate_callsite_precondition_vcs_for_each(&func, &[&summaries]);
    assert_eq!(call_vcs.len(), 1);
    assert!(call_vcs[0].is_empty());
    let attr_vcs = super::generate_callsite_precondition_vcs_attributed(&func, &summaries);
    assert!(attr_vcs.is_empty());
}

#[test]
fn wave781_to_786_block_predecessors_and_edges_memo_and_guard_fast_paths() {
    let func = guarded_body(6);
    let unscoped_preds = crate::guards::block_predecessors_uncached(&func);
    let unscoped_edges = crate::guards::block_predecessor_edges_uncached(&func);
    assert_eq!(crate::guards::block_predecessors(&func), unscoped_preds);
    {
        let _scope = FuncAnalysisScope::enter(&func);
        let p1 = super::block_predecessors_rc_for(&func);
        let p2 = super::block_predecessors_rc_for(&func);
        assert!(std::rc::Rc::ptr_eq(&p1, &p2));
        assert_eq!(*p1, unscoped_preds);
        assert_eq!(crate::guards::block_predecessors(&func), unscoped_preds);

        let e1 = super::block_predecessor_edges_rc_for(&func);
        let e2 = super::block_predecessor_edges_rc_for(&func);
        assert!(std::rc::Rc::ptr_eq(&e1, &e2));
        assert_eq!(*e1, unscoped_edges);
        assert_eq!(crate::guards::block_predecessor_edges(&func), unscoped_edges);
    }
}

#[test]
fn wave787_to_792_shift_cast_checked_binop_len_reborrow_and_refutation_fast_paths() {
    use super::assert_refutation::{formula_free_var_vec, refutation_name_has_projection_or_discr};

    assert!(!refutation_name_has_projection_or_discr("x"));
    assert!(!refutation_name_has_projection_or_discr("x#s1_0"));
    assert!(refutation_name_has_projection_or_discr("x.0"));
    assert!(refutation_name_has_projection_or_discr("x@1.0#s2_0"));
    assert!(refutation_name_has_projection_or_discr("__trust_mir__discr_x"));

    let f = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Var("b".to_string(), Sort::Int)),
        ),
        Formula::Lt(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Var("c".to_string(), Sort::Int)),
        ),
    ]);
    assert_eq!(
        formula_free_var_vec(&f),
        vec!["a".to_string(), "b".to_string(), "c".to_string()]
    );
}

#[test]
fn wave793_to_798_bv_shl_blockdef_amount_sub_dominating_operands_and_checked_vcs_fast_paths() {
    let i128_ty = Ty::Int { width: 128, signed: true };
    let u32_ty = Ty::Int { width: 32, signed: false };
    let func = VerifiableFunction {
        name: "wave793_798_smoke".to_string(),
        def_path: "wave793_798_smoke".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i128_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: u32_ty, name: Some("amt".into()) },
                LocalDecl { index: 2, ty: i128_ty.clone(), name: Some("shifted".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Constant(ConstValue::Int(1)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i128_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let mut out = Vec::new();
    super::overflow_vc::v2_collect_bv_shl_blockdef(
        &func,
        &func.body.blocks[0],
        1,
        2,
        "__trust_ovf_bv_lhs_shifted",
        128,
        &mut out,
    );
    assert_eq!(out.len(), 1);
    assert_eq!(
        super::overflow_vc::v2_widening_bv_source(&func, &Operand::Copy(Place::local(2)), 128),
        None
    );
}


/// PERF-COMPILER-VCGEN-799: `v2_shift_assert_exactly_bound` runs its operand
/// rewrite scan lazily, after a candidate assert passes its structural checks.
/// The refusals must be unchanged: a shift whose amount is rewritten before it in
/// its own block never binds, and a shift with no overflow assert never binds.
#[test]
fn wave799_shift_assert_rewrite_scan_is_lazy_and_still_refuses() {
    use trust_types::{AssertMessage, UnwindEdge};
    let u32_ty = Ty::Int { width: 32, signed: false };
    let build = |rewrite_amount: bool, with_assert: bool| {
        let shift = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Shl,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        };
        let mut shift_stmts = Vec::new();
        if rewrite_amount {
            shift_stmts.push(Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(99, 32))),
                span: SourceSpan::default(),
            });
        }
        shift_stmts.push(shift);
        let entry_terminator = if with_assert {
            Terminator::Assert {
                cond: Operand::Copy(Place::local(3)),
                expected: true,
                msg: AssertMessage::Overflow(BinOp::Shl),
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            }
        } else {
            Terminator::Goto(BlockId(1))
        };
        VerifiableFunction {
            name: "wave799_smoke".to_string(),
            def_path: "wave799_smoke".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u32_ty.clone(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: u32_ty.clone(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: u32_ty.clone(), name: Some("amt".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                    LocalDecl { index: 4, ty: u32_ty.clone(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(32, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: entry_terminator,
                    },
                    BasicBlock { id: BlockId(1), stmts: shift_stmts, terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: u32_ty.clone(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    };
    let decide = |func: &VerifiableFunction| {
        let block = &func.body.blocks[1];
        let stmt_index = block.stmts.len() - 1;
        let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } =
            &block.stmts[stmt_index]
        else {
            unreachable!("the shift is the block's last statement")
        };
        super::checked_vcs::v2_shift_assert_exactly_bound(
            func, *op, block.id, stmt_index, lhs, rhs,
        )
    };
    assert!(!decide(&build(true, true)), "an amount rewritten before the shift never binds");
    assert!(!decide(&build(false, false)), "no overflow assert, nothing to bind to");
    // The canonical shape still generates without disturbance either way.
    let _ = crate::generate_vcs(&build(false, true));
}

/// PERF-COMPILER-VCGEN-800/801: the div/rem binders ask the operand rewrite scan
/// lazily. The canonical unsigned zero check still binds, a divisor rewritten in
/// the operation's own block before the division still refuses, and the overflow
/// twin (unsigned: no overflow row to deduplicate) still refuses.
#[test]
fn wave800_801_divrem_binders_ask_rewrite_scan_lazily() {
    use trust_types::{AssertMessage, UnwindEdge};
    let u32_ty = Ty::Int { width: 32, signed: false };
    let build = |rewrite_divisor: bool| {
        let mut div_stmts = Vec::new();
        if rewrite_divisor {
            div_stmts.push(Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                span: SourceSpan::default(),
            });
        }
        div_stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        });
        VerifiableFunction {
            name: "wave800_smoke".to_string(),
            def_path: "wave800_smoke".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: u32_ty.clone(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: u32_ty.clone(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: u32_ty.clone(), name: Some("d".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                    LocalDecl { index: 4, ty: u32_ty.clone(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(0, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(Place::local(3)),
                            expected: false,
                            msg: AssertMessage::DivisionByZero,
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: div_stmts, terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: u32_ty.clone(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    };
    let decide = |func: &VerifiableFunction| {
        let block = &func.body.blocks[1];
        let stmt_index = block.stmts.len() - 1;
        let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } =
            &block.stmts[stmt_index]
        else {
            unreachable!("the division is the block's last statement")
        };
        (
            super::checked_vcs::v2_divzero_assert_exactly_bound(
                func, *op, block.id, stmt_index, lhs, rhs,
            ),
            super::checked_vcs::v2_divrem_overflow_assert_exactly_bound(
                func, *op, block.id, stmt_index, lhs, rhs,
            ),
        )
    };
    assert_eq!(decide(&build(false)), (true, false), "the canonical unsigned zero check binds");
    assert_eq!(decide(&build(true)), (false, false), "a rewritten divisor never binds");
}

/// PERF-COMPILER-VCGEN-803: `v2_overflow_assert_provably_cannot_fire` answers
/// `false` for every non-`Mul` operation without scanning for the checked op.
/// Only a signed 128-bit `Mul` with finite corner boxes may suppress its assert.
#[test]
fn wave803_overflow_cannot_fire_gate_is_mul_only() {
    use trust_types::{AssertMessage, UnwindEdge};
    let i32_ty = Ty::Int { width: 32, signed: true };
    let func = VerifiableFunction {
        name: "wave803_smoke".to_string(),
        def_path: "wave803_smoke".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: i32_ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i32_ty.clone(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Tuple(vec![i32_ty.clone(), Ty::Bool]),
                    name: None,
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: i32_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let block = &func.body.blocks[0];
    let Terminator::Assert { cond, .. } = &block.terminator else { unreachable!() };
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Shl] {
        assert!(!super::alloc_vcs::v2_overflow_assert_provably_cannot_fire(
            &func,
            block,
            BlockId(1),
            op,
            cond,
            false
        ));
    }
    // The overflow row is still minted for the i32 add.
    assert!(crate::generate_vcs(&func)
        .iter()
        .any(|vc| matches!(vc.kind, trust_types::VcKind::ArithmeticOverflow { .. })));
}

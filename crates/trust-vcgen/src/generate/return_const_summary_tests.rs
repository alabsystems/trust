use trust_types::{
    BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::{
    build_semantic_guard_map, compute_return_bound_summaries, compute_return_const_set_summaries,
    compute_return_lower_bound_summaries,
};

const SMALL_DEN: &str = "test::small_den";

fn assign_const(local: usize, v: u128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(v, 64))),
        span: SourceSpan::default(),
    }
}

/// ny's `small_den` shape: `match g { 0 => 1, 1 => 2, _ => 4 }` — a
/// `SwitchInt` over three arms, each assigning a constant to the return
/// local `_0`, joining at a single `Return`. With `third_arm_const: false`,
/// the otherwise-arm returns `g` instead (`_0 = copy _1`) — ONE non-const
/// return site, which must fail the whole summary closed.
fn small_den_fn(third_arm_const: bool) -> VerifiableFunction {
    let bb3_stmt = if third_arm_const {
        assign_const(0, 4)
    } else {
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        }
    };
    VerifiableFunction {
        name: "small_den".into(),
        def_path: SMALL_DEN.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("g".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign_const(0, 1)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign_const(0, 2)],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![bb3_stmt],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn caller(g) { d = small_den(g); }` — one call, one successor block.
fn caller_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".into(),
        def_path: "test::caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("g".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("d".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: SMALL_DEN.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: Some(trust_types::CalleeIdentity {
                            // A concrete call: the compiler gives it an identity, and a body-derived
                            // summary applies only to a call to its own body (`crate::call_reaches_summarized_body`).
                            stable_crate_id: 1,
                            def_index: 1,
                            substs_digest: [0, 0],
                        }),
                        callee_key: crate::sep_engine::tests::fixture_key(&SMALL_DEN.to_string()),
                        is_foreign: false,
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
    }
}

#[test]
fn small_den_summaries_capture_min_max_and_const_set() {
    let funcs = [small_den_fn(true)];
    assert_eq!(
        compute_return_lower_bound_summaries(&funcs).get(SMALL_DEN),
        Some(&1),
        "every return site is a const >= 1 — the lower summary must be its min"
    );
    assert_eq!(
        compute_return_bound_summaries(&funcs).get(SMALL_DEN),
        Some(&4),
        "every return site is a const <= 4 — the upper summary must be its max"
    );
    assert_eq!(
        compute_return_const_set_summaries(&funcs).get(SMALL_DEN),
        Some(&vec![1, 2, 4]),
        "all-const return sites must yield the exact sorted const set"
    );
}

#[test]
fn one_non_const_return_site_fails_all_summaries_closed() {
    // The otherwise-arm returns `g` — its value is unknown, so NO summary
    // (lower, upper, or set) may be recorded: the bound must hold for
    // EVERY input and EVERY return path.
    let funcs = [small_den_fn(false)];
    assert!(
        compute_return_lower_bound_summaries(&funcs).is_empty(),
        "a non-const return site must fail the lower summary closed"
    );
    assert!(
        compute_return_bound_summaries(&funcs).is_empty(),
        "a non-const return site must fail the upper summary closed"
    );
    assert!(
        compute_return_const_set_summaries(&funcs).is_empty(),
        "a non-const return site must fail the const-set summary closed"
    );
}

#[test]
fn call_defined_return_site_fails_closed() {
    // Replace the otherwise-arm with a RECURSIVE return site
    // `_0 = small_den(g)` — a call dest the const scan cannot see through.
    // Fail-closed: no summary of any shape.
    let mut func = small_den_fn(true);
    func.body.blocks[3] = BasicBlock {
        id: BlockId(3),
        stmts: vec![],
        terminator: Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: SMALL_DEN.into(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: Some(BlockId(4)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key(&SMALL_DEN.to_string()),
            is_foreign: false,
        },
    };
    let funcs = [func];
    assert!(
        compute_return_lower_bound_summaries(&funcs).is_empty()
            && compute_return_bound_summaries(&funcs).is_empty()
            && compute_return_const_set_summaries(&funcs).is_empty(),
        "a call-defined (recursive) return site must fail every summary closed"
    );
}

#[test]
fn tail_call_defined_return_site_fails_closed() {
    // A TailCall writes the implicit return place.  Treating it as merely an
    // exit would incorrectly retain the constants from the other arms.
    let mut func = small_den_fn(true);
    func.body.blocks[3] = BasicBlock {
        id: BlockId(3),
        stmts: vec![],
        terminator: Terminator::TailCall {
            func: SMALL_DEN.into(),
            args: vec![Operand::Copy(Place::local(1))],
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            is_foreign: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key(&SMALL_DEN.to_string()),
        },
    };
    let funcs = [func];
    assert!(
        compute_return_lower_bound_summaries(&funcs).is_empty()
            && compute_return_bound_summaries(&funcs).is_empty()
            && compute_return_const_set_summaries(&funcs).is_empty(),
        "an opaque tail-call return site must fail every const summary closed"
    );
}

/// Trust (2026-09-30): the same call WITHOUT an identity — what the compiler emits
/// for a dispatch whose instantiation still mentions a type parameter, e.g. the
/// unresolvable `t.m(x)` inside `fn f<T: Tr>` rendering a blanket impl's def path —
/// gets none of the summary facts (`crate::call_reaches_summarized_body`).
#[test]
fn call_site_without_an_identity_gets_no_summary_facts() {
    let funcs = [small_den_fn(true)];
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs))
            .with_summary_body_identities(crate::test_summary_body_identities(
                funcs.iter().map(|f| f.def_path.clone()),
            )),
    );
    let mut caller = caller_fn();
    if let Terminator::Call { callee_identity, .. } = &mut caller.body.blocks[0].terminator {
        *callee_identity = None;
    }
    let guards = build_semantic_guard_map(&caller).get(&BlockId(1)).cloned().unwrap_or_default();
    let mentions_d = |f: &Formula| f.free_variables().iter().any(|v| v.starts_with("d#"));
    assert!(
        !guards.iter().any(mentions_d),
        "an unidentified call must carry no summary fact about its dest; got {guards:?}"
    );
}

/// Trust (2026-09-30, round 7): a call that carries ANOTHER body's identity — what a
/// concrete call to a trait default method carries when its rendering matches an
/// override elsewhere (residual 7c) — gets none of the summary facts either.
#[test]
fn call_site_with_another_bodys_identity_gets_no_summary_facts() {
    let funcs = [small_den_fn(true)];
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs))
            .with_summary_body_identities(crate::test_summary_body_identities(
                funcs.iter().map(|f| f.def_path.clone()),
            )),
    );
    let mut caller = caller_fn();
    if let Terminator::Call { callee_identity: Some(id), .. } =
        &mut caller.body.blocks[0].terminator
    {
        id.def_index = 2;
    }
    let guards = build_semantic_guard_map(&caller).get(&BlockId(1)).cloned().unwrap_or_default();
    let mentions_d = |f: &Formula| f.free_variables().iter().any(|v| v.starts_with("d#"));
    assert!(
        !guards.iter().any(mentions_d),
        "a call to another body must carry no summary fact about its dest; got {guards:?}"
    );
}

/// A trait impl method's summary is registered for exactly the identity a call to
/// that impl carries (`SummaryBodyIdentity::Instance`): the same trait item at
/// another instantiation — which coherence routes to a different impl, or to the
/// trait's default — gets none of its facts, and the exact instantiation does.
#[test]
fn trait_impl_summary_applies_only_at_its_own_instantiation() {
    let funcs = [small_den_fn(true)];
    let exact =
        trust_types::CalleeIdentity { stable_crate_id: 1, def_index: 1, substs_digest: [0, 0] };
    let ids = funcs
        .iter()
        .map(|f| (f.def_path.clone(), crate::SummaryBodyIdentity::Instance(exact)))
        .collect();
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs))
            .with_summary_body_identities(ids),
    );
    let mentions_d = |f: &Formula| f.free_variables().iter().any(|v| v.starts_with("d#"));
    let exact_guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        exact_guards.iter().any(mentions_d),
        "the impl's own instantiation gets the summary facts; got {exact_guards:?}"
    );
    let mut caller = caller_fn();
    if let Terminator::Call { callee_identity: Some(id), .. } =
        &mut caller.body.blocks[0].terminator
    {
        id.substs_digest = [0, 1];
    }
    let guards = build_semantic_guard_map(&caller).get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        !guards.iter().any(mentions_d),
        "another instantiation of the trait item must carry no summary fact; got {guards:?}"
    );
}

#[test]
fn call_site_gets_lower_upper_and_const_set_facts() {
    let funcs = [small_den_fn(true)];
    let _summary_scope = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs))
            .with_summary_body_identities(crate::test_summary_body_identities(
                funcs.iter().map(|f| f.def_path.clone()),
            )),
    );
    let guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();

    // The dest fact is versioned to the call terminator token (`d#s0_t`),
    // mirroring the stdlib min/max bound emission.
    let d = || Box::new(Formula::Var("d#s0_t".into(), Sort::Int));
    let lower = Formula::Ge(d(), Box::new(Formula::Int(1)));
    let upper = Formula::Le(d(), Box::new(Formula::Int(4)));
    let const_set = Formula::Or(vec![
        Formula::Eq(d(), Box::new(Formula::Int(1))),
        Formula::Eq(d(), Box::new(Formula::Int(2))),
        Formula::Eq(d(), Box::new(Formula::Int(4))),
    ]);
    assert!(
        guards.contains(&lower),
        "call site must carry the summary lower bound `d >= 1`; got {guards:?}"
    );
    assert!(
        guards.contains(&upper),
        "call site must carry the summary upper bound `d <= 4`; got {guards:?}"
    );
    assert!(
        guards.contains(&const_set),
        "call site must carry the exact const-set disjunction; got {guards:?}"
    );
}

#[test]
fn no_summary_emits_no_call_site_fact() {
    // Fail-closed at the USE site too: with no installed summary for the
    // callee (the default), the call dest gets no return-summary fact.
    let guards =
        build_semantic_guard_map(&caller_fn()).get(&BlockId(1)).cloned().unwrap_or_default();
    assert!(
        guards.iter().all(|f| !format!("{f:?}").contains("d#")),
        "an unsummarized callee must yield NO dest fact; got {guards:?}"
    );
}

// ── the summaries as GLOBAL facts (TRUST-10, 2026-09-23) ────────────────────
//
// `build_callee_return_summary_facts` states the same three summaries about a
// local whose ONE value is the summarised call, so they reach a loop body the
// call-site path fact above never reaches. The real-MIR half (bit-vec's
// `reverse_bits`) is `tests/loop_callee_return_summary_realmir.rs`; these pin the
// gate.

fn small_den_summary_scope() -> crate::VcgenContextGuard {
    let funcs = [small_den_fn(true)];
    crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default()
            .with_return_bounds(compute_return_bound_summaries(&funcs))
            .with_return_lower_bounds(compute_return_lower_bound_summaries(&funcs))
            .with_return_const_sets(compute_return_const_set_summaries(&funcs)),
    )
}

#[test]
fn a_call_only_local_gets_the_summaries_as_global_facts() {
    let _scope = small_den_summary_scope();
    let facts = super::callee_summaries::build_callee_return_summary_facts(&caller_fn());
    // BARE name: the global set is version-renamed with the body.
    let d = || Box::new(Formula::Var("d".into(), Sort::Int));
    let expected = [
        Formula::Le(d(), Box::new(Formula::Int(4))),
        Formula::Ge(d(), Box::new(Formula::Int(1))),
        Formula::Or(vec![
            Formula::Eq(d(), Box::new(Formula::Int(1))),
            Formula::Eq(d(), Box::new(Formula::Int(2))),
            Formula::Eq(d(), Box::new(Formula::Int(4))),
        ]),
    ];
    for fact in &expected {
        assert!(facts.contains(fact), "missing global fact {fact:?}; got {facts:?}");
    }
    assert_eq!(facts.len(), expected.len(), "no other fact may be emitted; got {facts:?}");
}

#[test]
fn no_installed_summary_emits_no_global_fact() {
    let facts = super::callee_summaries::build_callee_return_summary_facts(&caller_fn());
    assert!(facts.is_empty(), "an unsummarised callee must yield no fact; got {facts:?}");
}

#[test]
fn a_local_with_a_second_definition_gets_no_global_fact() {
    // `d = small_den(g); d = g;` — the call is not `d`'s only value, and `g` is
    // unbounded, so `d ∈ {1, 2, 4}` would be false after the second write.
    let _scope = small_den_summary_scope();
    let mut caller = caller_fn();
    caller.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    });
    let facts = super::callee_summaries::build_callee_return_summary_facts(&caller);
    assert!(facts.is_empty(), "a reassigned local must get no fact; got {facts:?}");
}

#[test]
fn a_mutably_borrowed_local_gets_no_global_fact() {
    // `let p = &mut d;` — a store through `p` is a write no scan keyed on `d` sees.
    let _scope = small_den_summary_scope();
    let mut caller = caller_fn();
    caller.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::usize()) },
        name: Some("p".into()),
    });
    caller.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
        span: SourceSpan::default(),
    });
    let facts = super::callee_summaries::build_callee_return_summary_facts(&caller);
    assert!(facts.is_empty(), "an escaped local must get no fact; got {facts:?}");
}

#[test]
fn a_parameter_written_by_the_call_gets_no_global_fact() {
    // `g = small_den(g)` — the ENTRY value of `g` reaches every read on a path that
    // skips the call, so the summary is not a fact about `g`.
    let _scope = small_den_summary_scope();
    let mut caller = caller_fn();
    if let Terminator::Call { dest, .. } = &mut caller.body.blocks[0].terminator {
        *dest = Place::local(1);
    }
    let facts = super::callee_summaries::build_callee_return_summary_facts(&caller);
    assert!(facts.is_empty(), "a parameter must get no fact; got {facts:?}");
}

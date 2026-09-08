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
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Sort, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
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
                        targets: if swap_arms { vec![(0, BlockId(1))] } else { vec![(0, BlockId(2))] },
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

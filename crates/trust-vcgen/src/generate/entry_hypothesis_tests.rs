//! The DROPPED-ENTRY-HYPOTHESIS tripwire — the third silent-weakening sibling
//! in `contract_vcs.rs`, after the return-slot and out-parameter twins.
//!
//! THE DEFECT. `gate_contract_preconditions` drops the whole contract-derived
//! precondition set whenever it cannot bind the predicate to entry parameters.
//! The postcondition lane then assembles its VC over an entry state constrained
//! by nothing but the always-true synthetic facts appended AFTER the gate, so
//! `Not(post)` is satisfiable at an entry state the author's `requires` forbids.
//! The row comes back Failed and the verifier mints
//! `verified_counterexample = true` against correct code.
//!
//! Measured on the current stage2 for
//! `#[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn f(n: i32) -> i32 { n }`:
//! 1 proved, 2 FAILED — with `n = -1`, a call the precondition forbids.
//!
//! THE DISCRIMINATION THESE TESTS ENFORCE. The fix is worthless if it suppresses
//! rows wholesale, so every case below pins one of the three outcomes:
//!
//!   * the dependent clause fails CLOSED (visible unsupported row, no refutable
//!     Postcondition VC);
//!   * the clause that is provable WITHOUT the hypothesis still gets its
//!     refutable Postcondition VC — turning `ensures(*ret >= n)` over `{ n }`
//!     into an unsupported row would be a capability regression;
//!   * the clause whose counterexample the precondition ADMITS still gets its
//!     refutable Postcondition VC — a real bug must still be caught.

use trust_types::{
    BasicBlock, BlockId, Contract, ContractKind, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

use super::{
    dropped_requires_clauses, forced_parameter_alias, generate_v2_contract_vcs_impl,
    only_excluded_counterexamples,
};

// ───────────────────────────── builders ─────────────────────────────

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn int_var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn ge(lhs: Formula, rhs: Formula) -> Formula {
    Formula::Ge(Box::new(lhs), Box::new(rhs))
}

fn le(lhs: Formula, rhs: Formula) -> Formula {
    Formula::Le(Box::new(lhs), Box::new(rhs))
}

fn eq(lhs: Formula, rhs: Formula) -> Formula {
    Formula::Eq(Box::new(lhs), Box::new(rhs))
}

fn lowered(body: &str) -> String {
    format!("{}{body}", crate::contracts::LOWERED_CONTRACT_PREFIX)
}

/// The always-true `i32` parameter range fact `integer_param_range_preconditions`
/// appends AFTER the assumption gate — the reason "`preconditions` is non-empty"
/// says nothing about whether the authored `requires` survived.
fn i32_range_fact(name: &str) -> Formula {
    Formula::And(vec![
        ge(int_var(name), Formula::Int(-2_147_483_648)),
        le(int_var(name), Formula::Int(2_147_483_647)),
    ])
}

/// `fn f(n: i32) -> i32 { n }` — the identity body of the measured repro.
///
/// `requires_text` is the authored `requires` (`None` for a function with no
/// precondition at all); `assumed` is what `func.preconditions` carries, i.e.
/// what the assumption gate let through.
fn identity_fn(
    requires_text: Option<&str>,
    ensures_text: &str,
    ensures: Formula,
    assumed: Vec<Formula>,
) -> VerifiableFunction {
    let mut contracts = Vec::new();
    if let Some(text) = requires_text {
        contracts.push(Contract {
            kind: ContractKind::Requires,
            span: span(),
            body: lowered(text),
        });
    }
    contracts.push(Contract {
        kind: ContractKind::Ensures,
        span: span(),
        body: lowered(ensures_text),
    });
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: span(),
        body: VerifiableBody {
            // Local 0 carries the `__ret` debug name the `#[ensures]` lowering
            // mints — the same shape the dumped body shows.
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("__ret".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts,
        preconditions: assumed,
        postconditions: vec![ensures],
        spec: Default::default(),
    }
}

/// `fn f(n: i32) -> i32 { let x = n; x }` — the SHADOWED spelling of the same
/// body, exactly as the current stage2 extracts it: MIR copy-propagation parks
/// the body `let x` on the parameter local and the last-write-wins debug-name
/// collapse names local 1 `x`, so the VC reads `x`/`_0` while the authored
/// `requires` still reads `n`.
///
/// Confirmed against the dumped body of the measured repro
/// (`-Ztrust-dump=mir:`): `locals[1] = {"index":1,"name":"x"}`, `arg_count = 1`,
/// and the assumed set carries only the synthetic `x` range fact.
fn shadowed_identity_fn(
    requires_text: Option<&str>,
    ensures_text: &str,
    ensures: Formula,
    assumed: Vec<Formula>,
) -> VerifiableFunction {
    let mut func = identity_fn(requires_text, ensures_text, ensures, assumed);
    func.body.locals[1].name = Some("x".into());
    func
}

/// A function whose parameter list can force NO correspondence at all (it has no
/// parameters), so a case built on it exercises the model search alone.
fn no_parameters() -> VerifiableFunction {
    let mut func = identity_fn(None, "result >= 0", ge(int_var("_0"), Formula::Int(0)), vec![]);
    func.body.arg_count = 0;
    func.body.locals.truncate(1);
    func
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

/// Every fail-closed `spec_unverifiable` row's detail string.
fn unverifiable_details(func: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail }
                if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND =>
            {
                Some(detail)
            }
            _ => None,
        })
        .collect()
}

// ═══════════════════════════════════════════════════════════════════════
// THE REPRO — a clause whose every counterexample the dropped `requires`
// forbids must fail CLOSED, not refute.
// ═══════════════════════════════════════════════════════════════════════

fn pa_dropped() -> VerifiableFunction {
    identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        // The gate cleared the authored fact; only the synthetic range survives.
        vec![i32_range_fact("n")],
    )
}

#[test]
fn dropped_requires_dependent_clause_fails_closed_instead_of_refuting() {
    let func = pa_dropped();
    assert!(
        postcondition_vcs(&func).is_empty(),
        "`ensures(*ret >= 0)` over `{{ n }}` is refutable ONLY at `n < 0`, which the \
         dropped `requires(n >= 0)` forbids; emitting a refutable Postcondition VC \
         here is what mints `verified_counterexample = true` against correct code"
    );
    let details = unverifiable_details(&func);
    assert_eq!(details.len(), 1, "exactly one visible fail-closed row: {details:?}");
    assert!(
        details[0].contains("under-constrained entry state"),
        "the row must name the actual gap: {}",
        details[0]
    );
}

// ═══════════════════════════════════════════════════════════════════════
// THE CAPABILITY GUARDS — both must keep their refutable Postcondition VC.
// ═══════════════════════════════════════════════════════════════════════

/// The measured control: `ensures(*ret >= n)` over `{ n }` PROVES today even
/// though the `requires` was dropped, because it does not need the hypothesis.
/// A blanket suppression would turn it into an unsupported row.
///
/// The tripwire cannot touch it by construction: firing requires EXHIBITING a
/// model of the assembled row, and this row has none.
#[test]
fn clause_provable_without_the_hypothesis_keeps_its_vc() {
    let func = identity_fn(
        Some("n >= 0"),
        "result >= n",
        ge(int_var("_0"), int_var("n")),
        vec![i32_range_fact("n")],
    );
    assert_eq!(
        postcondition_vcs(&func).len(),
        1,
        "the provable control must still get its body-aware Postcondition VC"
    );
    assert!(
        unverifiable_details(&func).is_empty(),
        "no fail-closed row may replace a row that proves: {:?}",
        unverifiable_details(&func)
    );
}

/// A REAL bug: `ensures(|r| *r >= 5)` over `{ n }` is violated at `n == 0`,
/// which `requires(n >= 0)` ADMITS. The counterexample is a legal call, so the
/// row must stay refutable.
#[test]
fn clause_refutable_under_the_precondition_still_refutes() {
    let func = identity_fn(
        Some("n >= 0"),
        "result >= 5",
        ge(int_var("_0"), Formula::Int(5)),
        vec![i32_range_fact("n")],
    );
    assert_eq!(
        postcondition_vcs(&func).len(),
        1,
        "a counterexample the precondition admits is a genuine one and must be reported"
    );
    assert!(
        unverifiable_details(&func).is_empty(),
        "real bugs must still be caught: {:?}",
        unverifiable_details(&func)
    );
}

/// The gate KEPT the precondition: `func.preconditions` carries the authored
/// fact, so there is no dropped hypothesis and the lane is untouched.
#[test]
fn surviving_requires_leaves_the_row_untouched() {
    let func = identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![ge(int_var("n"), Formula::Int(0)), i32_range_fact("n")],
    );
    assert!(dropped_requires_clauses(&func).is_empty(), "the authored clause is carried");
    assert_eq!(postcondition_vcs(&func).len(), 1);
    assert!(unverifiable_details(&func).is_empty());
}

/// No `requires` at all: `ensures(|r| *r >= 0)` over `{ n }` is genuinely false
/// for this function and must keep refuting. Nothing was dropped, so nothing is
/// excluded.
#[test]
fn function_without_requires_still_refutes() {
    let func =
        identity_fn(None, "result >= 0", ge(int_var("_0"), Formula::Int(0)), vec![i32_range_fact("n")]);
    assert!(dropped_requires_clauses(&func).is_empty());
    assert_eq!(
        postcondition_vcs(&func).len(),
        1,
        "a function with no precondition genuinely violates this clause"
    );
    assert!(unverifiable_details(&func).is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// DETECTION — `func.preconditions` is not a provenance carrier.
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn synthetic_range_facts_do_not_count_as_a_carried_requires() {
    let dropped = dropped_requires_clauses(&pa_dropped());
    assert_eq!(
        dropped.len(),
        1,
        "`preconditions` holds ONLY the synthetic i32 range fact, so the authored \
         `requires` was dropped: {dropped:?}"
    );
    assert_eq!(dropped[0], ge(int_var("n"), Formula::Int(0)));
}

#[test]
fn a_carried_clause_recognized_across_the_parser_sort_sentinel() {
    // The parser stamps every unresolved leaf `Sort::Int`; the compiler's typed
    // lowering carries the real sort. A `bool` precondition must still be
    // recognized as carried, or the tripwire would think it was dropped.
    let func = identity_fn(
        Some("flag"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![Formula::Var("flag".to_string(), Sort::Bool)],
    );
    assert!(
        dropped_requires_clauses(&func).is_empty(),
        "the typed `Bool` lowering IS the authored clause"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// THE SEARCH — its three declining directions are the soundness argument.
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn search_declines_when_the_row_has_no_model() {
    // `_0 == n AND NOT(_0 >= n)` — unsatisfiable, i.e. PROVABLE. No model can be
    // exhibited, so the tripwire can never fire on it. This is the property that
    // makes "never turns a PROVED into unsupported" structural rather than
    // heuristic.
    let vc = Formula::And(vec![
        eq(int_var("_0"), int_var("n")),
        Formula::Not(Box::new(ge(int_var("_0"), int_var("n")))),
    ]);
    assert!(!only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("n"), Formula::Int(0))]));
}

#[test]
fn search_fires_when_every_model_violates_the_dropped_clause() {
    let vc = Formula::And(vec![
        eq(int_var("_0"), int_var("n")),
        Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(0)))),
    ]);
    assert!(only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("n"), Formula::Int(0))]));
}

#[test]
fn search_declines_on_a_model_the_dropped_clause_admits() {
    let vc = Formula::And(vec![
        eq(int_var("_0"), int_var("n")),
        Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(5)))),
    ]);
    assert!(
        !only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("n"), Formula::Int(0))]),
        "`n == 0` refutes the clause AND satisfies the precondition"
    );
}

#[test]
fn search_declines_on_an_irrelevant_hypothesis() {
    let vc = Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(0))));
    assert!(
        !only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("m"), Formula::Int(0))]),
        "a hypothesis about a name this row never reads cannot be what makes it refutable"
    );
}

#[test]
fn search_declines_outside_the_declared_fragment() {
    // A bitvector variable is outside the fragment: this module does not
    // implement machine semantics, so it must never claim a model under them.
    let bv = Formula::Var("_0".to_string(), Sort::BitVec(32));
    let vc = Formula::And(vec![
        eq(bv.clone(), Formula::Var("n".to_string(), Sort::BitVec(32))),
        Formula::Not(Box::new(Formula::Ge(Box::new(bv), Box::new(Formula::Int(0))))),
    ]);
    assert!(!only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("n"), Formula::Int(0))]));
}

#[test]
fn search_declines_on_an_uninterpreted_leaf() {
    // `Div` is outside the fragment (SMT-LIB `Int` division is Euclidean, not
    // Rust's truncating division), so no model may be claimed.
    let vc = Formula::And(vec![
        eq(int_var("_0"), Formula::Div(Box::new(int_var("n")), Box::new(Formula::Int(2)))),
        Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(0)))),
    ]);
    assert!(!only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("n"), Formula::Int(0))]));
}

#[test]
fn search_declines_with_an_empty_dropped_set() {
    let vc = Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(0))));
    assert!(!only_excluded_counterexamples(&no_parameters(), &vc, &[]));
}

#[test]
fn search_declines_over_the_variable_budget() {
    // Seven independent variables: over `MAX_WITNESS_VARS`, so the search
    // declines rather than fires on a partial exploration.
    let mut conjuncts = vec![Formula::Not(Box::new(ge(int_var("_0"), Formula::Int(0))))];
    for name in ["a", "b", "c", "d", "e", "g"] {
        conjuncts.push(ge(int_var(name), Formula::Int(0)));
    }
    let vc = Formula::And(conjuncts);
    assert!(!only_excluded_counterexamples(&no_parameters(), &vc, &[ge(int_var("_0"), Formula::Int(0))]));
}

// ═══════════════════════════════════════════════════════════════════════
// THE RENAMED-PARAMETER CASE — `{ let x = n; x }`.
//
// The clause is written in the SOURCE namespace (`n`) and the row is assembled
// in the BODY namespace (`x`/`_0`), because copy-propagation parks the body
// `let x` on the parameter local and the debug-name collapse is last-write-wins.
// They are one entity: parameter position 1. Measured on the current stage2 as
// `1 proved, 2 FAILED` with `verified_counterexample = true` against correct
// code — a spelling-only relevance test never sees the connection.
// ═══════════════════════════════════════════════════════════════════════

fn shadowed_dropped() -> VerifiableFunction {
    shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![i32_range_fact("x")],
    )
}

#[test]
fn renamed_parameter_dependent_clause_fails_closed_instead_of_refuting() {
    let func = shadowed_dropped();
    assert_eq!(
        dropped_requires_clauses(&func),
        vec![ge(int_var("n"), Formula::Int(0))],
        "the authored `requires` is still spelled `n`; only the BODY was renamed"
    );
    assert!(
        postcondition_vcs(&func).is_empty(),
        "`ensures(*ret >= 0)` over `{{ let x = n; x }}` is refutable ONLY at entry \
         values the dropped `requires(n >= 0)` forbids — `n` and `x` are parameter \
         position 1 under two spellings"
    );
    let details = unverifiable_details(&func);
    assert_eq!(details.len(), 1, "exactly one visible fail-closed row: {details:?}");
    assert!(details[0].contains("under-constrained entry state"), "{}", details[0]);
}

/// THE COUNTERPART THAT MUST NOT MOVE. `ensures(|r| *r >= 5)` over the same
/// renamed body is a REAL bug: `n == 0` satisfies `requires(n >= 0)` and violates
/// the postcondition, so a model that the restated clause ADMITS exists and the
/// row must stay refutable. Measured as `1 proved, 2 FAILED` today, and that
/// verdict is the honest one.
#[test]
fn renamed_parameter_clause_refutable_under_the_precondition_still_refutes() {
    let func = shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 5",
        ge(int_var("_0"), Formula::Int(5)),
        vec![i32_range_fact("x")],
    );
    assert_eq!(
        postcondition_vcs(&func).len(),
        1,
        "`x == 0` is a model of the row that the restated `x >= 0` admits"
    );
    assert!(unverifiable_details(&func).is_empty(), "{:?}", unverifiable_details(&func));
}

/// The provable control under the SAME renaming: `ensures(*ret >= x)` over
/// `{ let x = n; x }` needs no hypothesis and has no model, so the search finds
/// none and the row is emitted untouched. This is the property that makes
/// "never turns a PROVED into unsupported" structural: the restatement rewrites
/// only the dropped clause, never the row whose models are searched.
#[test]
fn renamed_parameter_provable_clause_keeps_its_vc() {
    let func = shadowed_identity_fn(
        Some("n >= 0"),
        "result >= x",
        ge(int_var("_0"), int_var("x")),
        vec![i32_range_fact("x")],
    );
    assert_eq!(postcondition_vcs(&func).len(), 1);
    assert!(unverifiable_details(&func).is_empty(), "{:?}", unverifiable_details(&func));
}

/// THE HAZARD THE GATE EXISTS TO PREVENT, pinned. The restated clause is an aid
/// for REFUSING; it must never be conjoined onto anything. Nothing this lane
/// emits — for the firing case or any other — may contain `x >= 0`.
#[test]
fn the_restated_clause_never_enters_an_emitted_formula() {
    fn mentions(formula: &Formula, needle: &Formula) -> bool {
        let mut found = false;
        formula.visit(&mut |node| {
            if node == needle {
                found = true;
            }
        });
        found
    }
    let restated = ge(int_var("x"), Formula::Int(0));
    for func in [
        shadowed_dropped(),
        shadowed_identity_fn(
            Some("n >= 0"),
            "result >= 5",
            ge(int_var("_0"), Formula::Int(5)),
            vec![i32_range_fact("x")],
        ),
    ] {
        for vc in generate_v2_contract_vcs_impl(&func, None) {
            assert!(
                !mentions(&vc.formula, &restated),
                "a clause the assumption gate DROPPED became a hypothesis: {:?}",
                vc.formula
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// THE CORRESPONDENCE — forced by parameter POSITION, declined when it is not
// uniquely determined. Every case below is a way for the map to be a guess.
// ═══════════════════════════════════════════════════════════════════════

/// `fn f(<p1>: <t1>, <p2>: <t2>)`, parameter locals 1 and 2 in declaration order.
fn two_param_fn(first: (Option<&str>, Ty), second: (Option<&str>, Ty)) -> VerifiableFunction {
    let mut func = identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![],
    );
    func.body.locals[1] = LocalDecl {
        index: 1,
        ty: first.1,
        name: first.0.map(str::to_string),
    };
    func.body.locals.push(LocalDecl {
        index: 2,
        ty: second.1,
        name: second.0.map(str::to_string),
    });
    func.body.arg_count = 2;
    func
}

fn requires_clause(text: &str) -> Vec<Formula> {
    vec![trust_types::parse_spec_expr(text).expect("test clause parses")]
}

#[test]
fn one_alias_and_one_unclaimed_position_force_the_correspondence() {
    assert_eq!(
        forced_parameter_alias(&shadowed_dropped(), &requires_clause("n >= 0")),
        Some(("n".to_string(), "x".to_string())),
        "one parameter, one unresolved spelling: the map is the unique total map"
    );
}

#[test]
fn an_already_named_position_narrows_the_correspondence_to_the_other() {
    // `a` is parameter 1's own body spelling and the clause uses it, so position
    // 2 is the only unclaimed one and `n` can only be it.
    let func = two_param_fn((Some("a"), Ty::i32()), (Some("x"), Ty::i32()));
    assert_eq!(
        forced_parameter_alias(&func, &requires_clause("a > 0 && n < 10")),
        Some(("n".to_string(), "x".to_string()))
    );
}

#[test]
fn two_unclaimed_positions_leave_the_correspondence_ambiguous() {
    let func = two_param_fn((Some("x"), Ty::i32()), (Some("y"), Ty::i32()));
    assert_eq!(
        forced_parameter_alias(&func, &requires_clause("n >= 0")),
        None,
        "`n` could be either position; preferring one would be a guess"
    );
}

#[test]
fn two_unresolved_spellings_leave_the_correspondence_ambiguous() {
    let func = two_param_fn((Some("a"), Ty::i32()), (Some("x"), Ty::i32()));
    assert_eq!(forced_parameter_alias(&func, &requires_clause("m >= 0 && n >= 0")), None);
}

#[test]
fn an_unnamed_parameter_position_declines() {
    // Position 2 has no body spelling at all, so it could be the one the clause
    // means and there would be nothing to restate into.
    let func = two_param_fn((Some("x"), Ty::i32()), (None, Ty::i32()));
    assert_eq!(forced_parameter_alias(&func, &requires_clause("n >= 0")), None);
}

#[test]
fn a_reserved_spelling_is_never_resolved_to_a_parameter() {
    // The `__` metadata family / the return place / `_<digits>` are model and
    // projection terms, not parameters. Restating one onto a parameter would
    // rename a fact about a length or a return place into a fact about an entry
    // value. (`result` is spelled `_0` by the time the parser is done with it.)
    for name in ["buf__len", "__old_n", "_0", "_2", "n__discr", "n__value", "n__sign"] {
        assert_eq!(
            forced_parameter_alias(&shadowed_dropped(), &[ge(int_var(name), Formula::Int(0))]),
            None,
            "`{name}` must not resolve to a parameter"
        );
    }
}

#[test]
fn a_single_underscore_user_spelling_can_resolve_to_a_parameter() {
    // Synthetic projections now live in the reserved double-underscore family.
    // A legal source binding such as `buf_len` must remain available to users.
    assert_eq!(
        forced_parameter_alias(&shadowed_dropped(), &requires_clause("buf_len >= 0")),
        Some(("buf_len".to_string(), "x".to_string()))
    );
}

#[test]
fn a_projection_or_deref_spelling_is_never_resolved_to_a_parameter() {
    for name in ["n*", "self.0", "n#3"] {
        assert_eq!(
            forced_parameter_alias(
                &shadowed_dropped(),
                &[ge(int_var(name), Formula::Int(0))]
            ),
            None,
            "{name} is a place rendering, not a parameter's own name"
        );
    }
}

#[test]
fn a_parameter_type_that_does_not_admit_the_sort_declines() {
    let func = shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![],
    );
    for ty in [Ty::Bool, Ty::Float { width: 64 }, Ty::Char] {
        let mut func = func.clone();
        func.body.locals[1].ty = ty.clone();
        assert_eq!(
            forced_parameter_alias(&func, &requires_clause("n >= 0")),
            None,
            "an `Int` clause is not a restatement of a {ty:?} parameter"
        );
    }
}

#[test]
fn a_quantified_clause_is_never_renamed() {
    // `Formula::rename_var` is a syntactic rename with no binder awareness.
    let clause = Formula::forall(
        &[("k", Sort::Int)],
        ge(int_var("n"), Formula::Var("k".to_string(), Sort::Int)),
    );
    assert_eq!(forced_parameter_alias(&shadowed_dropped(), &[clause]), None);
}

#[test]
fn a_clause_already_in_the_body_namespace_is_left_alone() {
    // Nothing is unresolved, so there is nothing to restate — the pre-existing
    // spelling-overlap path runs unchanged.
    assert_eq!(forced_parameter_alias(&pa_dropped(), &requires_clause("n >= 0")), None);
}

#[test]
fn a_function_with_no_parameters_forces_nothing() {
    assert_eq!(forced_parameter_alias(&no_parameters(), &requires_clause("n >= 0")), None);
}

// ═══════════════════════════════════════════════════════════════════════
// THE STALENESS WITNESS for the ASSUMPTION-side twin of this correspondence.
//
// `trust_mir_extract::contract_assumption_gate` now performs the SAME positional
// restatement, but on the other side of the line: when the correspondence is
// FORCED it RENAMES the clause into the body's spelling and KEEPS it as an entry
// hypothesis, so `#[requires(n >= 0)]` over `{ let x = n; x }` is assumed as
// `x >= 0` and the true postcondition proves instead of being an honest UNKNOWN.
// That mints a PROVE, so the question this module's own restatement never had to
// answer becomes load-bearing: CAN THE ASSUMED ENTRY FACT GO STALE?
//
// The answer is the version rename at the conjoin boundary
// (`conjoin_preconditions_versioned`, which replaced the retired
// `formula_survives_redefs` precondition kill — S2c item 3). It renames every
// PLACE variable of the VC body to its value at the read point and leaves the
// preconditions at the bare ENTRY spelling, so a fact about a place the body
// reassigned names a DIFFERENT SMT variable from the read and cannot constrain it.
//
// THE POINT THESE TESTS PIN: that machinery is keyed on the names
// `place_to_var_name` mints — i.e. on the BODY spelling `x`, never on the source
// spelling `n`. So restating the clause as `x` is precisely what puts it INSIDE
// the staleness discipline; the un-restated `n` is not a place name at all and
// would receive none of it. If this ever stops holding, the gate-side rename must
// not ship as an assumption.
// ═══════════════════════════════════════════════════════════════════════

/// `fn f(n: i32) -> i32 { let x = n; x = 7; x }` after the collapse: the parameter
/// local (body spelling `x`) is REASSIGNED before the return, which is exactly the
/// shape that would stale an entry fact about it.
fn reassigned_parameter_fn() -> VerifiableFunction {
    let mut func = shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        vec![ge(int_var("x"), Formula::Int(0))],
    );
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Int(7))),
            span: span(),
        },
    );
    func
}

#[test]
fn the_restated_entry_fact_is_version_severed_from_a_reassigned_parameter() {
    use super::StmtVersionCtx;
    let func = reassigned_parameter_fn();
    let sv = StmtVersionCtx::build(&func);
    let terminal = func.body.blocks[0].stmts.len();

    // The BODY spelling is what the version oracle tracks: a read after the
    // reassignment is versioned away from the bare entry name.
    assert!(
        sv.version_token_at(&func, BlockId(0), terminal, "x").is_some(),
        "the reassigned parameter's BODY spelling must version at a later read"
    );
    // ... and a read BEFORE the write is still the entry value, so a genuine entry
    // fact is not severed from the reads it legitimately governs.
    assert!(
        sv.version_token_at(&func, BlockId(0), 0, "x").is_none(),
        "a read before the write is the entry value and must stay bare"
    );
    // The SOURCE spelling is not a place name at all, so the oracle has nothing to
    // say about it — an un-restated clause gets no staleness protection whatsoever.
    // This is the asymmetry that makes the rename REQUIRED rather than merely
    // convenient.
    assert!(
        sv.version_token_at(&func, BlockId(0), terminal, "n").is_none(),
        "the source spelling is outside the place namespace the oracle keys on"
    );
}

#[test]
fn the_restated_entry_fact_cannot_constrain_a_post_reassignment_read() {
    use super::conjoin_preconditions_versioned;
    let func = reassigned_parameter_fn();
    let killed = trust_types::fx::FxHashSet::default();
    // A VC body that READS the parameter place after the reassignment.
    let vc_body = ge(int_var("x"), Formula::Int(1000));
    let conjoined = conjoin_preconditions_versioned(
        &func,
        BlockId(0),
        &[ge(int_var("x"), Formula::Int(0))],
        &killed,
        vc_body,
    );
    let vars = conjoined.free_variables();
    assert!(vars.contains("x"), "the entry hypothesis keeps the bare ENTRY spelling: {vars:?}");
    assert!(
        vars.iter().any(|v| v.starts_with("x#")),
        "the post-write body read is version-renamed away from it: {vars:?}"
    );
    // Name-disjointness IS the kill: the assumed entry fact and the reassigned read
    // are different SMT variables, so the fact cannot vacuously discharge an
    // obligation about the new value.
    assert!(
        !vars.iter().any(|v| v.starts_with("n")),
        "nothing in the emitted formula is written in the SOURCE namespace: {vars:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// THE GATE-SIDE OUTCOME — what the assumed restatement buys, end of lane.
//
// With `trust-mir-extract`'s forced restatement in place, the extracted function
// for `#[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn f(n: i32) -> i32
// { let x = n; x }` carries the authored clause as `x >= 0` (the BODY spelling)
// instead of dropping it. These tests pin the consequences on this side of the
// line: the tripwire must stand down (there is nothing under-constrained any
// more), the emitted postcondition row must actually carry the hypothesis, and —
// the control that must not move — a FALSE postcondition must still refute.
// ═══════════════════════════════════════════════════════════════════════

fn shadowed_with_restated_requires() -> VerifiableFunction {
    shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 0",
        ge(int_var("_0"), Formula::Int(0)),
        // What the gate now lets through: the restated authored clause, plus the
        // synthetic range fact appended after it.
        vec![ge(int_var("x"), Formula::Int(0)), i32_range_fact("x")],
    )
}

#[test]
fn an_assumed_restatement_stands_the_tripwire_down() {
    let func = shadowed_with_restated_requires();
    // `dropped_requires_clauses` still reports the authored clause: it matches the
    // SOURCE spelling against the carried facts, and the carried fact is the
    // restated one. That mis-signal is inert, and this test is why: the restated
    // clause is a CONJUNCT of the assembled row, so every model of the row
    // satisfies it and the search can never classify one as excluded.
    for vc in generate_v2_contract_vcs_impl(&func, None) {
        assert!(
            !only_excluded_counterexamples(&func, &vc.formula, &requires_clause("n >= 0")),
            "an assumed hypothesis cannot be `excluded` by its own models: {:?}",
            vc.formula
        );
    }
    assert!(
        unverifiable_details(&func).is_empty(),
        "no fail-closed row once the clause is actually assumed: {:?}",
        unverifiable_details(&func)
    );
}

#[test]
fn the_assumed_restatement_reaches_the_postcondition_row() {
    fn mentions(formula: &Formula, needle: &Formula) -> bool {
        let mut found = false;
        formula.visit(&mut |node| {
            if node == needle {
                found = true;
            }
        });
        found
    }
    let func = shadowed_with_restated_requires();
    let rows = postcondition_vcs(&func);
    assert_eq!(rows.len(), 1, "the postcondition row is emitted, not refused");
    // `x >= 0` ∧ `_0 == x` ∧ ¬(`_0 >= 0`) is unsatisfiable, which is exactly why
    // the row proves; the checkable part here is that the hypothesis is present.
    assert!(
        mentions(&rows[0].formula, &ge(int_var("x"), Formula::Int(0))),
        "the entry hypothesis must be conjoined onto the row: {:?}",
        rows[0].formula
    );
}

/// THE CONTROL THAT MUST NOT MOVE, restated-hypothesis edition. `requires(n >= 0)`
/// with `ensures(*ret >= 5)` over `{ let x = n; x }` is a FALSE postcondition, and
/// assuming the (true) precondition must not launder it: `x == 0` satisfies
/// `x >= 0` and violates `*ret >= 5`, so the row stays refutable and the function
/// is still REJECTED. This is the direct guard against the restatement proving a
/// contract that does not hold.
#[test]
fn an_assumed_restatement_does_not_prove_a_false_postcondition() {
    let func = shadowed_identity_fn(
        Some("n >= 0"),
        "result >= 5",
        ge(int_var("_0"), Formula::Int(5)),
        vec![ge(int_var("x"), Formula::Int(0)), i32_range_fact("x")],
    );
    let rows = postcondition_vcs(&func);
    assert_eq!(rows.len(), 1, "the false postcondition must remain a refutable row, not a proof");
    assert!(
        unverifiable_details(&func).is_empty(),
        "and it must not be laundered into an unsupported row: {:?}",
        unverifiable_details(&func)
    );
    // Exhibit the counterexample the assumed hypothesis ADMITS: `x == 0` satisfies
    // `x >= 0` and refutes `*ret >= 5`. `only_excluded_counterexamples` returning
    // false is the machine-checked statement that this refutation is honest, i.e.
    // that the kept hypothesis did not make the row vacuous.
    assert!(
        !only_excluded_counterexamples(&func, &rows[0].formula, &requires_clause("n >= 0")),
        "a counterexample the precondition admits must stay a genuine one: {:?}",
        rows[0].formula
    );
}

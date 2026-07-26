// trust_vcgen/specdb.rs: Cross-function spec composition
//
// SpecDatabase wraps FactMemory to retain cross-function proof metadata.
// Public facts and labels are non-authoritative: they neither discharge VCs nor
// become caller-wide assumptions without replayable, obligation-bound evidence.
//
// Three costs (from the design doc):
// 1. Known from notes (free) — callee postcondition discharges the requirement
// 2. Solver proves it (costs time) — standard verification path
// 3. Solver can't (runtime check or error) — unproved
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Trust: Database of proved function specs for cross-function composition.
///
/// Wraps `FactMemory` and tracks per-VC disposition metadata. Remembered
/// postconditions are available for diagnostics and future evidence transport;
/// current callers always retain solver-required dispositions.
#[derive(Debug, Clone, Default)]
pub struct SpecDatabase {
    /// The underlying fact memory storing proved postconditions.
    memory: FactMemory,
}

/// Trust: A verification condition annotated with its disposition.
///
/// Pairs a standard VC with metadata about how it was (or will be) resolved.
/// The public disposition is descriptive only. Solver filtering validates no
/// note as authoritative until an opaque replay capability exists.
#[derive(Debug, Clone)]
pub struct AnnotatedVc {
    /// The verification condition itself.
    pub vc: VerificationCondition,
    /// How this VC was resolved or should be handled.
    pub disposition: VcDisposition,
}

impl SpecDatabase {
    /// Create an empty spec database.
    pub fn new() -> Self {
        Self::default()
    }

    /// Access the underlying fact memory.
    pub fn memory(&self) -> &FactMemory {
        &self.memory
    }

    /// Returns the number of remembered facts.
    pub fn len(&self) -> usize {
        self.memory.len()
    }

    /// Returns true when no specs have been recorded.
    pub fn is_empty(&self) -> bool {
        self.memory.is_empty()
    }

    /// Record a proved postcondition from a verified function.
    ///
    /// After proving function B's postcondition, call this to make the
    /// postcondition available as an exact note for later requirements.
    pub fn record_proved_postcondition(
        &mut self,
        function: impl Into<String>,
        predicate: Formula,
        solver: impl Into<String>,
        strength: ProofStrength,
    ) -> FactId {
        self.memory.remember_proved_postcondition(function, predicate, solver, strength)
    }

    /// Record an explicit assumption.
    pub fn record_assumption(&mut self, predicate: Formula, label: impl Into<String>) -> FactId {
        self.memory.remember_assumption(predicate, label)
    }

    /// Check whether a call-site requirement can be satisfied from notes.
    pub fn check_call_site(
        &self,
        callee: impl Into<String>,
        requirement: &Formula,
    ) -> CallSiteSatisfaction {
        self.memory.satisfy_call_site(callee, requirement)
    }

    /// Look up all proved postconditions for a named function.
    ///
    /// Returns formulas that have been proved for the given function.
    pub fn postconditions_for(&self, function: &str) -> Vec<&KnownFact> {
        self.memory
            .facts()
            .iter()
            .filter(|fact| match &fact.source {
                FactSource::ProvedPostcondition(post) => post.function == function,
                _ => false,
            })
            .collect()
    }
}

/// Trust: Generate VCs with cross-function spec composition.
///
/// Like `generate_vcs`, but takes a `SpecDatabase` to enable conservative
/// cross-function reasoning. Proved callee postconditions are not injected as
/// solver premises or used to discharge ordinary body VCs until Trust has a
/// precise call-site substitution, callee identity, and dominance model.
///
/// Returns annotated VCs with disposition metadata:
/// - `RequiresSolver` — the standard path, no callee specs available
pub fn generate_vcs_with_specs(
    func: &VerifiableFunction,
    specs: &SpecDatabase,
) -> Vec<AnnotatedVc> {
    // Trust: Generate base VCs using the standard pipeline.
    let base_vcs = crate::generate_vcs(func);

    let _ = specs;

    // Trust: Annotate each base VC with a solver-required disposition. A base
    // VC is a property of the current function body, not a call-site
    // requirement for a named callee; exact note matching here would let a
    // postcondition recorded for `func.name` discharge unrelated safety VCs.
    base_vcs
        .into_iter()
        .map(|vc| AnnotatedVc { vc, disposition: VcDisposition::RequiresSolver })
        .collect()
}

/// Trust: Extract only VCs that require solver dispatch (filter out notes-satisfied).
///
/// Convenience function that strips the disposition metadata and returns only
/// the VCs that need solver attention.
///
/// This overload is deliberately conservative: without the `SpecDatabase` that
/// owns the fact id, an externally constructed `SatisfiedFromNotes` annotation
/// cannot be validated. Use [`solver_vcs_with_specs`] when note discharge should
/// be honored.
#[must_use]
pub fn solver_vcs(annotated: &[AnnotatedVc]) -> Vec<&VerificationCondition> {
    annotated.iter().map(|a| &a.vc).collect()
}

/// Return VCs requiring solver dispatch. Note dispositions are public metadata
/// and therefore currently cannot suppress a VC.
#[must_use]
pub fn solver_vcs_with_specs<'a>(
    annotated: &'a [AnnotatedVc],
    specs: &SpecDatabase,
) -> Vec<&'a VerificationCondition> {
    annotated.iter().filter(|a| !note_disposition_valid(a, specs)).map(|a| &a.vc).collect()
}

fn note_disposition_valid(annotated: &AnnotatedVc, specs: &SpecDatabase) -> bool {
    // `VcDisposition` and every fact/evidence field are public metadata. No
    // current value carries a replayed proof capability, so annotations cannot
    // suppress solver dispatch even when their strings and formulas match.
    let _ = (annotated, specs);
    false
}

/// Trust: Count VCs by disposition category.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DispositionSummary {
    /// VCs satisfied from compiler notes (free — no solver call).
    pub from_notes: usize,
    /// VCs requiring solver dispatch (standard path).
    pub require_solver: usize,
    /// VCs sent to solver with explicit assumptions.
    ///
    /// `generate_vcs_with_specs` currently never creates this category from
    /// callee postconditions; the field remains for externally annotated VCs.
    pub with_assumptions: usize,
}

impl DispositionSummary {
    /// Build a summary from a slice of annotated VCs.
    #[must_use]
    pub fn from_annotated(annotated: &[AnnotatedVc]) -> Self {
        let mut summary = Self::default();
        for a in annotated {
            match &a.disposition {
                VcDisposition::SatisfiedFromNotes { .. } => summary.from_notes += 1,
                VcDisposition::RequiresSolver => summary.require_solver += 1,
                VcDisposition::SolverWithAssumption { .. } => summary.with_assumptions += 1,
                _ => {}
            }
        }
        summary
    }

    /// Total VCs across all categories.
    #[must_use]
    pub fn total(&self) -> usize {
        self.from_notes + self.require_solver + self.with_assumptions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a function that calls `parse` and then uses the result.
    /// fn caller(input: &str) -> usize {
    ///     let n = parse(input);
    ///     let r = sqrt(n);
    ///     r
    /// }
    fn caller_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) }, // _1: input
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) }, // _2: n = parse(input)
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("r".into()) }, // _3: r = sqrt(n)
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "parse".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "sqrt".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Helper: build a simple function with an overflow-prone add.
    fn adder_function() -> VerifiableFunction {
        crate::tests::midpoint_function()
    }

    #[test]
    fn test_empty_spec_database_produces_standard_vcs() {
        let func = adder_function();
        let specs = SpecDatabase::new();

        let annotated = generate_vcs_with_specs(&func, &specs);
        // overflow checks now in trust-mc-lib. The midpoint function
        // (used as adder_function) produces 0 VCs from trust_vcgen.
        // Annotated VCs may be empty.
        for a in &annotated {
            assert_eq!(
                a.disposition,
                VcDisposition::RequiresSolver,
                "without specs, all VCs should require solver"
            );
        }
    }

    #[test]
    fn test_spec_database_records_and_retrieves_postconditions() {
        let mut specs = SpecDatabase::new();
        let formula =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        let fact_id = specs.record_proved_postcondition(
            "parse",
            formula.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(specs.len(), 1);
        assert!(!specs.is_empty());

        let facts = specs.postconditions_for("parse");
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].id, fact_id);
        assert_eq!(facts[0].predicate, formula);

        let no_facts = specs.postconditions_for("nonexistent");
        assert!(no_facts.is_empty());
    }

    #[test]
    fn test_callee_postconditions_are_not_injected_as_assumptions() {
        let func = adder_function();
        let mut specs = SpecDatabase::new();

        // Record a postcondition for some callee (won't match midpoint_function's
        // call sites since it has none, but we can still verify the mechanism with
        // a function that has calls).
        let formula =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition("parse", formula, "ay", ProofStrength::smt_unsat());

        let annotated = generate_vcs_with_specs(&func, &specs);

        // Midpoint function has no Call terminators, so specs won't apply.
        // All VCs should still require solver.
        for a in &annotated {
            assert_eq!(a.disposition, VcDisposition::RequiresSolver);
        }
    }

    #[test]
    fn test_caller_does_not_get_assumptions_from_callee_specs() {
        let func = caller_function();
        let mut specs = SpecDatabase::new();

        // parse() postcondition: n >= 0
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition(
            "parse",
            postcond.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        let annotated = generate_vcs_with_specs(&func, &specs);

        // caller_function has calls to parse and sqrt, but parse's postcondition
        // is not injected as a caller-wide solver premise.
        let summary = DispositionSummary::from_annotated(&annotated);
        // With no arithmetic operations in caller, no VCs are generated at all.
        assert_eq!(summary.total(), 0, "caller with only calls produces no L0 VCs");
    }

    #[test]
    fn test_caller_with_arithmetic_does_not_get_callee_assumptions() {
        // Build a function that calls parse() AND does arithmetic
        let func = VerifiableFunction {
            name: "compute".to_string(),
            def_path: "test::compute".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    // bb0: n = parse(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "parse".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: _3 = CheckedAdd(n, 1)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: return
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let mut specs = SpecDatabase::new();

        // parse() postcondition: n >= 0
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));
        specs.record_proved_postcondition(
            "parse",
            postcond.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        let annotated = generate_vcs_with_specs(&func, &specs);

        let summary = DispositionSummary::from_annotated(&annotated);
        assert_eq!(summary.with_assumptions, 0);
        for a in &annotated {
            assert!(!matches!(a.disposition, VcDisposition::SolverWithAssumption { .. }));
            assert!(
                !matches!(&a.vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "callee postcondition must not be injected as a global premise"
            );
        }
    }

    #[test]
    fn test_exact_formula_match_for_same_callee_requires_solver() {
        let overflow_formula = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);

        let mut specs = SpecDatabase::new();
        specs.record_proved_postcondition(
            "check_range",
            overflow_formula.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        // Public fact records are metadata, not replay-bound proof capabilities.
        // Even an exact formula/callee match must therefore reach the solver.
        let satisfaction = specs.check_call_site("check_range", &overflow_formula);
        assert_eq!(
            satisfaction,
            CallSiteSatisfaction::RequiresSolver { callee: "check_range".to_string() },
            "same-callee public note metadata must not discharge a VC"
        );
    }

    #[test]
    fn test_exact_formula_match_for_different_callee_requires_solver() {
        let overflow_formula = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]);

        let mut specs = SpecDatabase::new();
        specs.record_proved_postcondition(
            "check_range",
            overflow_formula.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );

        assert_eq!(
            specs.check_call_site("downstream", &overflow_formula),
            CallSiteSatisfaction::RequiresSolver { callee: "downstream".to_string() }
        );
    }

    #[test]
    fn test_solver_vcs_keeps_public_note_metadata() {
        let requirement = Formula::Bool(true);
        let mut specs = SpecDatabase::new();
        let fact_id = specs.record_proved_postcondition(
            "f",
            requirement.clone(),
            "ay",
            ProofStrength::smt_unsat(),
        );
        let source = specs.memory().fact(fact_id).expect("recorded fact").source.clone();
        let annotated = vec![
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::Precondition { callee: "f".to_string() },
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Not(Box::new(requirement)),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes { fact_id, source },
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                disposition: VcDisposition::RequiresSolver,
            },
        ];

        let solver_only = solver_vcs(&annotated);
        assert_eq!(solver_only.len(), 2, "annotations alone must not discharge VCs");

        let solver_only = solver_vcs_with_specs(&annotated, &specs);
        assert_eq!(
            solver_only.len(),
            2,
            "database-matching public note metadata must not discharge VCs"
        );
    }

    #[test]
    fn test_solver_vcs_keeps_weak_or_non_proof_notes() {
        let annotated = vec![
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes {
                    fact_id: FactId(0),
                    source: FactSource::Assumption { label: "manual".into() },
                },
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes {
                    fact_id: FactId(1),
                    source: FactSource::ProvedPostcondition(ProvedPostcondition {
                        function: "f".into(),
                        solver: "bmc".into(),
                        strength: ProofStrength::bounded(8),
                    }),
                },
            },
        ];

        let solver_only = solver_vcs(&annotated);
        assert_eq!(solver_only.len(), 2, "non-proof and weak notes must not discharge VCs");
    }

    #[test]
    fn test_disposition_summary() {
        let annotated = vec![
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SatisfiedFromNotes {
                    fact_id: FactId(0),
                    source: FactSource::Note { note: "manual".to_string() },
                },
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::RequiresSolver,
            },
            AnnotatedVc {
                vc: VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "test".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                disposition: VcDisposition::SolverWithAssumption {
                    fact_id: FactId(1),
                    source: FactSource::ProvedPostcondition(ProvedPostcondition {
                        function: "f".into(),
                        solver: "ay".into(),
                        strength: ProofStrength::smt_unsat(),
                    }),
                },
            },
        ];

        let summary = DispositionSummary::from_annotated(&annotated);
        assert_eq!(summary.from_notes, 1);
        assert_eq!(summary.require_solver, 1);
        assert_eq!(summary.with_assumptions, 1);
        assert_eq!(summary.total(), 3);
    }

    #[test]
    fn test_multiple_callee_postconditions() {
        let mut specs = SpecDatabase::new();

        let f1 =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let f2 =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        specs.record_proved_postcondition("parse", f1, "ay", ProofStrength::smt_unsat());
        specs.record_proved_postcondition("parse", f2, "ay", ProofStrength::smt_unsat());

        let facts = specs.postconditions_for("parse");
        assert_eq!(facts.len(), 2, "should remember both postconditions for parse");
    }

    #[test]
    fn test_generate_vcs_with_specs_empty_function() {
        // A function with an empty body produces no VCs.
        let func = VerifiableFunction {
            name: "empty".to_string(),
            def_path: "test::empty".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let specs = SpecDatabase::new();
        let annotated = generate_vcs_with_specs(&func, &specs);
        assert!(annotated.is_empty());
    }
}

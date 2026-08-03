// trust_vcgen/modular.rs: Modular verification with function summaries
//
// Extends SpecDatabase-based cross-function reasoning with a structured
// summary model. Each function summary captures pre/postconditions and
// proof status. At call sites:
// - Proved summary: verify preconditions
// - All return values/postconditions remain unmodeled until precise call-site
//   substitution and dominance are implemented.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::*;

use crate::specdb::SpecDatabase;

/// Trust: A function summary for modular verification.
///
/// Captures the contract (pre/postconditions) and proof status of a function.
/// When a callee has a proved summary, callers must verify the precondition at
/// the call site. Postconditions are retained as evidence only; callers must
/// not assume them without a precise call-site model.
#[derive(Debug, Clone)]
pub struct FunctionSummary {
    /// The function's name (matching `VerifiableFunction::name`).
    pub name: String,
    /// Formal parameter names in declaration order (e.g., `["x", "y"]`).
    /// Used by `wp_call` to substitute parameter names with actual argument
    /// expressions at call sites.
    pub param_names: Vec<String>,
    /// Trust (piece #8 — length-relationship preconditions): formal parameter
    /// TYPES in declaration order, parallel to `param_names`. Empty when the
    /// producer did not record them (every non-R1 caller). Used ONLY by
    /// `generate_callsite_precondition_vcs_attributed` to know WHICH formal is a
    /// slice/array — and thus needs a `<formal>__slice_len` σ length-replacement
    /// so a precondition like `n <= arr__slice_len` can discharge at the caller.
    /// Carries no proof authority; it is pure metadata for the σ renderer.
    pub param_types: Vec<Ty>,
    /// Preconditions that callers must satisfy at call sites.
    pub preconditions: Vec<Formula>,
    /// Postconditions proved for the callee. These are not automatically
    /// assumed by callers.
    pub postconditions: Vec<Formula>,
    /// F6 (float interval summaries): a signed interval containing every
    /// possible f64 return value of the callee UNDER ITS OWN preconditions,
    /// derived by the verifier's float tracer
    /// (`generate::derive_float_result_range` via `summaries::compute_summary`).
    /// `None` = no claim; every other producer — including the compiler's
    /// contract-summary builder — leaves it unset, so consumption is
    /// fail-closed there. Consumed ONLY by the float interval lane
    /// (`generate::float_summary_result_range`), which re-validates the
    /// interval shape and structurally re-establishes the callee's
    /// preconditions at the consuming call site (assume-guarantee) before
    /// honoring it.
    pub result_range: Option<(f64, f64)>,
    /// F6b (context-sensitive callee tracing): the callee's extracted body.
    ///
    /// Carries NO proof authority — it is an ANALYSIS INPUT the float tracer
    /// RE-TRACES per call site under caller-derived argument intervals
    /// (`generate` float lane): the caller first proves an interval for each
    /// actual, binds it as a parameter override on the callee's formal, and
    /// only then evaluates the requested return place inside this body. A
    /// static `result_range` is callee-global (valid only under the callee's
    /// own preconditions); this per-callsite re-trace is what makes chained
    /// magnitude reasoning (`a.add(b).scale(s)`) context-sensitive. The body's
    /// own gated preconditions ARE consumed by the re-trace, so the consumer
    /// structurally re-establishes them at the call site first
    /// (assume-guarantee, same discipline as `result_range`). Never
    /// serialized: an extracted body only means anything inside the verifier
    /// session that extracted it.
    pub extracted_body: Option<std::sync::Arc<trust_types::VerifiableFunction>>,
    /// Whether the summary has been proved.
    pub proved: bool,
    /// Evidence id that justifies reusing postconditions as proof facts.
    pub proof_evidence_id: Option<String>,
    /// Proof strength attached to `proof_evidence_id`.
    pub proof_strength: Option<ProofStrength>,
}

impl FunctionSummary {
    /// Create a new unproved summary with no conditions.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_names: Vec::new(),
            param_types: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            result_range: None,
            extracted_body: None,
            proved: false,
            proof_evidence_id: None,
            proof_strength: None,
        }
    }

    /// F6: attach a derived float result interval (see the field doc — only
    /// the verifier-owned derivation should call this outside tests).
    #[must_use]
    pub fn with_result_range(mut self, lo: f64, hi: f64) -> Self {
        self.result_range = Some((lo, hi));
        self
    }

    /// F6b: attach the callee's extracted body for context-sensitive
    /// re-tracing (see the field doc — an analysis input, not evidence; the
    /// consumer re-derives everything it claims from this body plus
    /// caller-proved actual intervals).
    #[must_use]
    pub fn with_extracted_body(
        mut self,
        body: std::sync::Arc<trust_types::VerifiableFunction>,
    ) -> Self {
        self.extracted_body = Some(body);
        self
    }

    /// Set formal parameter names (in declaration order).
    pub fn with_param_names(mut self, names: Vec<String>) -> Self {
        self.param_names = names;
        self
    }

    /// Trust (piece #8): set formal parameter TYPES (in declaration order,
    /// parallel to `with_param_names`). Only the R1 length-precondition path
    /// records these; other producers leave `param_types` empty (the σ renderer
    /// then emits no length replacement, unchanged behavior).
    pub fn with_param_types(mut self, types: Vec<Ty>) -> Self {
        self.param_types = types;
        self
    }

    /// Add a precondition.
    pub fn with_precondition(mut self, formula: Formula) -> Self {
        self.preconditions.push(formula);
        self
    }

    /// Add a postcondition.
    pub fn with_postcondition(mut self, formula: Formula) -> Self {
        self.postconditions.push(formula);
        self
    }

    /// Mark the summary as proved for modular precondition checking.
    ///
    /// This does not authorize exporting postconditions as reusable facts.
    /// Reusable fact export is reserved for verifier-owned checked evidence.
    pub fn proved(mut self) -> Self {
        self.proved = true;
        self
    }

    /// Attach external proof metadata to this summary.
    ///
    /// The identifier and strength are public, forgeable metadata. They are
    /// retained for reporting but never authorize postcondition injection or VC
    /// suppression.
    pub fn with_proof_evidence(
        mut self,
        evidence_id: impl Into<String>,
        strength: ProofStrength,
    ) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(strength);
        self
    }

    #[cfg(test)]
    /// Construct the strongest legacy metadata shape for negative authority
    /// tests. Despite the name, this does not carry or replay proof bytes.
    pub(crate) fn with_checked_proof_evidence(
        mut self,
        evidence_id: impl Into<String>,
        strength: ProofStrength,
    ) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(strength);
        self
    }

    /// Attach compiler contract metadata to this summary.
    ///
    /// A def-path string is not proof evidence. This builder deliberately keeps
    /// the old metadata shape for diagnostics while the authority gate below
    /// remains closed until the compiler can transport and replay an exact
    /// contract/obligation-bound proof artifact.
    #[must_use]
    pub fn with_verified_contract_evidence(mut self, evidence_id: impl Into<String>) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(ProofStrength::deductive());
        self
    }

    /// Whether this summary may authorize postcondition reuse.
    ///
    /// Hard-blocked: every field on `FunctionSummary` is publicly constructible,
    /// and `proof_evidence_id` is only an unbound string. Accepting it would let a
    /// caller stamp `Sound`/`Certified` and conjoin an arbitrary postcondition into
    /// a caller VC. Re-enable only with an opaque, replayed proof capability bound
    /// to the exact callee identity, contract digest, and instantiated obligation.
    pub(crate) fn has_reusable_postcondition_evidence(&self) -> bool {
        false
    }
}

/// Trust: Database of function summaries for modular verification.
///
/// Stores and retrieves function summaries keyed by function name.
/// Integrates with `SpecDatabase` to record proved postconditions as
/// reusable facts for cross-function spec composition.
#[derive(Debug, Clone, Default)]
pub struct SummaryDatabase {
    summaries: FxHashMap<String, FunctionSummary>,
}

impl SummaryDatabase {
    /// Create an empty summary database.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace a function summary.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.name.clone(), summary);
    }

    /// Look up a summary by function name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&FunctionSummary> {
        self.summaries.get(name)
    }

    /// Returns the number of stored summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Iterate the stored summary names (diagnostics).
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.summaries.keys().map(String::as_str)
    }

    /// Returns true when no summaries are stored.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// Preserve the former summary-to-fact synchronization API.
    ///
    /// Current summaries carry metadata only, so this is intentionally a no-op.
    pub fn sync_to_spec_db(&self, spec_db: &mut SpecDatabase) {
        // Preserve the API while the authority gate is closed. Iterating every
        // summary would be pure overhead: no public summary can carry the opaque,
        // replayed evidence required for authoritative export yet.
        let _ = spec_db;
    }
}

/// Trust: Result of modular VC generation for a single function.
#[derive(Debug, Clone)]
pub struct ModularVcResult {
    /// Standard safety VCs from the function body.
    pub body_vcs: Vec<VerificationCondition>,
    /// Precondition VCs: one per (call-site, precondition) pair.
    /// The caller must prove these hold at each call site.
    pub precondition_vcs: Vec<VerificationCondition>,
    /// Number of call sites where a proved callee postcondition was injected as an
    /// assumption (conjoined at the dominated successors, version-pinned to the
    /// call's post-SSA dest). Sound under the "SAT iff violation" convention because
    /// the fact is CONJOINED — never `post => vc` — and scoped by the establish-point
    /// versioning, so a stale/reassigned dest cannot false-PROVE (design 2026-06-25).
    pub assumptions_injected: usize,
    /// Number of call sites whose return values/postconditions were not modeled
    /// as caller assumptions.
    pub havoced_calls: usize,
}

/// Trust: Generate VCs for a function using modular verification.
///
/// For each call site in the function body:
/// - If the callee has a proved summary in `summaries`, generate a
///   `Precondition` VC for each precondition at the call site.
/// - Regardless of summary status, assume nothing about return values and
///   postconditions until a precise call-site model exists.
///
/// Body VCs are generated via the standard `generate_vcs` pipeline and are not
/// rewritten with callee postconditions.
#[must_use]
pub fn modular_vcgen(func: &VerifiableFunction, summaries: &SummaryDatabase) -> ModularVcResult {
    // The summary-aware lane retains the precise rebinding machinery, but its
    // authority gate is closed: public string/label metadata cannot inject a
    // postcondition. Body VCs therefore remain equivalent to the ordinary lane.
    let body_vcs = crate::generate::generate_vcs_with_summaries(func, summaries);

    // Trust: Walk call sites and build precondition VCs.
    let mut precondition_vcs = Vec::new();
    let mut assumptions_injected: usize = 0;
    let mut havoced_calls: usize = 0;

    // The body lane bails to an EMPTY guard map for over-budget functions, so NO
    // postcondition is actually injected there. Mirror that here so the reported
    // `assumptions_injected` count never claims an injection the body VCs did not
    // receive (audit R2 #5; telemetry consistency).
    let injection_active = !crate::generate::func_exceeds_vcgen_budget(func);

    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, args, dest, target, span, .. } =
            &block.terminator
        {
            let summary = summaries.get(callee_name);
            if let Some(summary) = summary {
                precondition_vcs.extend(callsite_precondition_vcs(
                    func,
                    callee_name,
                    args,
                    span,
                    summary,
                ));
            }
            // A proved postcondition that passes the injection gate is ASSUMED by
            // the summary-aware body lane above (conjoined at the dominated
            // successors); otherwise the call's result stays havoced. A DIVERGING
            // call (`target: None`) has no dominated successor, so the injection
            // never fires there — it is counted as havoced, matching the gate in
            // `build_semantic_guard_map_impl` (which is nested under `target: Some`).
            if injection_active
                && target.is_some()
                && summary.is_some_and(|s| {
                    crate::generate::callee_postcondition_is_injectable(func, dest, s, args.len())
                })
            {
                assumptions_injected += 1;
            } else {
                havoced_calls += 1;
            }
        }
    }

    ModularVcResult { body_vcs, precondition_vcs, assumptions_injected, havoced_calls }
}

/// Trust: Contract check kinds for modular verification.
///
/// Each variant represents a specific obligation generated at module boundaries
/// when verifying functions against their contracts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ContractCheck {
    /// Caller must establish callee's precondition at the call site.
    PreConditionAtCallSite {
        /// The callee function name.
        callee: String,
        /// Index of the precondition in the callee's contract.
        precondition_index: usize,
    },
    /// Callee must establish its own postcondition before returning.
    PostConditionOnReturn {
        /// Index of the postcondition in the function's contract.
        postcondition_index: usize,
    },
    /// Frame preservation: variables not mentioned in the contract are unchanged.
    FramePreservation {
        /// The variable that must be preserved.
        variable: String,
    },
}

/// Trust: Modular verifier that generates VCs using contracts at boundaries.
///
/// Uses function summaries and contracts to generate three kinds of VCs:
/// 1. Precondition VCs at call sites (caller must prove)
/// 2. Postcondition VCs at returns (callee must prove)
/// 3. Frame preservation VCs (modified variables must be declared)
#[derive(Debug)]
pub struct ModularVerifier {
    summaries: SummaryDatabase,
}

impl ModularVerifier {
    /// Create a new modular verifier with the given summary database.
    #[must_use]
    pub fn new(summaries: SummaryDatabase) -> Self {
        Self { summaries }
    }

    /// Access the underlying summary database.
    #[must_use]
    pub fn summaries(&self) -> &SummaryDatabase {
        &self.summaries
    }

    /// Generate modular VCs for a function using contracts at boundaries.
    ///
    /// Produces VCs for:
    /// - Each precondition of each callee at each call site
    /// - Each postcondition of the function itself (must hold at return)
    /// - Frame preservation for variables not in the modifies set
    #[must_use]
    pub fn verify(&self, func: &VerifiableFunction) -> Vec<VerificationCondition> {
        generate_modular_vcs(func, &self.summaries)
    }
}

/// Generate modular verification conditions for a function.
///
/// This produces contract-boundary VCs separate from the body safety VCs:
/// 1. `PreConditionAtCallSite`: for each call to a function with a proved
///    summary, the caller must prove each precondition holds.
/// 2. `PostConditionOnReturn`: the function must prove its own postconditions
///    hold at each return point.
/// 3. `FramePreservation`: (placeholder) variables not in the modifies clause
///    must remain unchanged.
#[must_use]
pub fn generate_modular_vcs(
    func: &VerifiableFunction,
    summaries: &SummaryDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // 1. Precondition checks at call sites
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee_name, args, span, .. } = &block.terminator
            && let Some(summary) = summaries.get(callee_name)
        {
            vcs.extend(callsite_precondition_vcs(func, callee_name, args, span, summary));
            for i in 0..summary.preconditions.len() {
                let _check = ContractCheck::PreConditionAtCallSite {
                    callee: callee_name.clone(),
                    precondition_index: i,
                };
            }
        }
    }

    // 2. Postcondition checks at return points
    for (i, post) in func.postconditions.iter().enumerate() {
        if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, post) {
            vcs.push(crate::contracts::spec_unverifiable_vc(
                func,
                func.span.clone(),
                "postcondition uses unmodeled fixed-width machine arithmetic",
                &format!("{post:?}"),
                None,
            ));
            let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
            continue;
        }
        // SOUNDNESS: a postcondition over SYNTHETIC spec-model terms
        // (`{base}_discr`/`{base}_value*`/`{base}_sign`/`.__trust_ok_i`) is
        // under-constrained here — nothing grounds those names, so `Not(post)`
        // is satisfiable by havoc regardless of the body (a minted, non-program
        // counterexample). Route it to the fail-closed NON-REFUTABLE Unknown
        // shape instead; see `contracts::spec_model_ungrounded_vc`.
        let ungrounded = crate::contracts::ungrounded_spec_model_vars(post);
        if !ungrounded.is_empty() {
            vcs.push(crate::contracts::spec_model_ungrounded_vc(
                func,
                func.span.clone(),
                &format!("{post:?}"),
                &ungrounded,
                None,
            ));
            let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
            continue;
        }
        vcs.push(VerificationCondition {
            kind: VcKind::Postcondition,
            function: func.name.as_str().into(),
            location: func.span.clone(),
            formula: Formula::Not(Box::new(post.clone())),
            contract_metadata: None,
            obligation: None,
        });
        let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
    }

    // Note: Contract structs carry string bodies, not parsed formulas.
    // The parsed postconditions are already in func.postconditions.

    vcs
}

fn callsite_precondition_vcs(
    caller: &VerifiableFunction,
    callee_name: &str,
    args: &[Operand],
    span: &SourceSpan,
    summary: &FunctionSummary,
) -> Vec<VerificationCondition> {
    if summary.preconditions.is_empty() {
        return Vec::new();
    }

    if summary.param_names.len() != args.len() {
        return vec![VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "SummaryArityMismatch".to_string(),
                detail: format!(
                    "callee `{callee_name}` summary has {} formal parameter(s), call has {} argument(s)",
                    summary.param_names.len(),
                    args.len()
                ),
            },
            function: caller.name.as_str().into(),
            location: span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }];
    }

    let replacements: Vec<(String, Formula)> = summary
        .param_names
        .iter()
        .zip(args.iter())
        .map(|(formal, actual)| (formal.clone(), crate::operand_to_formula(caller, actual)))
        .collect();

    summary
        .preconditions
        .iter()
        .map(|pre| {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic(pre) {
                return crate::contracts::spec_unverifiable_vc(
                    caller,
                    span.clone(),
                    &format!(
                        "callee `{callee_name}` requires uses unmodeled fixed-width machine arithmetic"
                    ),
                    &format!("{pre:?}"),
                    None,
                );
            }
            VerificationCondition {
                kind: VcKind::Precondition { callee: callee_name.to_string() },
                function: caller.name.as_str().into(),
                location: span.clone(),
                // Use the SINGLE, capture-avoiding rebinding point (audit R2 #1): the
                // former modular-local `substitute_summary_params` cloned quantifier
                // binders verbatim, so a callee `requires(forall x ..., a >= x)` called
                // with a caller local named `x` for formal `a` captured the argument
                // (`forall x, x >= x` = tautology) and vacuously discharged the
                // precondition — a false-PROVE. `generate::substitute_summary_params`
                // alpha-renames colliding binders (`capture_avoiding_rebind`).
                formula: Formula::Not(Box::new(crate::generate::substitute_summary_params(
                    pre,
                    &replacements,
                ))),
                contract_metadata: None,
                obligation: None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a caller that calls `parse(input)` then does `n + 1`.
    fn caller_with_arithmetic() -> VerifiableFunction {
        VerifiableFunction {
            name: "compute".to_string(),
            def_path: "test::compute".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
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
        }
    }

    // ---- separate-compilation postcondition assumption (design 2026-06-25) ----

    /// `parse`'s postcondition over its result symbol `_0`: `result <= 100`.
    fn parse_post_le_100() -> Formula {
        Formula::Le(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(100)))
    }

    /// Attack fixture carrying every former reuse label but no replayable proof.
    fn labeled_parse_summary() -> FunctionSummary {
        FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_postcondition(parse_post_le_100())
            .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat())
    }

    /// True iff `f` contains BOTH a version-pinned `Var` (name has `#`) and the
    /// integer literal `n` — i.e. the rebound, establish-versioned postcondition.
    fn has_versioned_var_and_int(f: &Formula, n: i128) -> bool {
        fn walk(f: &Formula, ver: &mut bool, int: &mut bool, n: i128) {
            match f {
                Formula::Var(name, _) if name.contains('#') => *ver = true,
                Formula::Int(v) if *v == n => *int = true,
                _ => {}
            }
            for c in f.children() {
                walk(c, ver, int, n);
            }
        }
        let (mut ver, mut int) = (false, false);
        walk(f, &mut ver, &mut int, n);
        ver && int
    }

    #[test]
    fn checked_label_does_not_inject_at_post_call_block() {
        use crate::generate::{build_semantic_guard_map, build_semantic_guard_map_with_summaries};
        // bb0: n = parse(input);  bb1 (the call target): n + 1;  bb2: return.
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(labeled_parse_summary());

        // Plain guard map: the post-call block carries NO callee postcondition fact.
        let plain = build_semantic_guard_map(&caller);
        let plain_bb1 = plain.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !plain_bb1.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "plain map must not assume the callee postcondition: {plain_bb1:?}"
        );

        // A summary carrying the old checked/string/strength metadata is still
        // non-authoritative, so the summary-aware lane must inject nothing.
        let aware = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = aware.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !bb1.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "label-only summary must not inject a postcondition: {bb1:?}"
        );
    }

    #[test]
    fn modular_vcgen_never_counts_label_only_postcondition_assumption() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(labeled_parse_summary());
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn proved_without_checked_evidence_is_not_assumed() {
        // `with_proof_evidence` preserves public metadata but cannot mint
        // reusable evidence. The postcondition must not be assumed.
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_proof_evidence("proof:parse:fake", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "proved-without-evidence must not be assumed");
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn verified_contract_string_is_reporting_only() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("contract:example::parse"),
        );
        let summary = db.get("parse").unwrap();
        assert_eq!(summary.proof_evidence_id.as_deref(), Some("contract:example::parse"));
        assert!(!summary.has_reusable_postcondition_evidence());
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn dyn_summary_names_cannot_bypass_evidence_gate() {
        let caller = caller_with_arithmetic(); // a single-arg `parse(input)` call site

        // Dyn shape WITHOUT param_names (the pre-fix bug): proved + reusable
        // evidence + a `_0`-only postcondition, but empty param_names -> arity gate
        // `0 == 1` is false -> nothing is injected (inert, the safe direction).
        let mut dead = SummaryDatabase::new();
        dead.insert(
            FunctionSummary::new("parse")
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("dyn-sealed:parse"),
        );
        assert!(dead.get("parse").unwrap().param_names.is_empty());
        assert_eq!(
            modular_vcgen(&caller, &dead).assumptions_injected,
            0,
            "empty param_names (the dyn deadness) must inject nothing"
        );

        // Even matching names/arity cannot turn an unbound string into proof.
        let mut live = SummaryDatabase::new();
        live.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["self".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("dyn-sealed:parse"),
        );
        assert_eq!(
            modular_vcgen(&caller, &live).assumptions_injected,
            0,
            "matching arity must not bypass the replay-evidence gate"
        );
    }

    /// A `_stray` callee symbol that is neither `_0` nor a formal parameter.
    fn post_eq_stray() -> Formula {
        Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("_stray".into(), Sort::Int)),
        )
    }

    #[test]
    fn postcondition_with_unrebindable_free_var_is_dropped() {
        // SOUNDNESS (audit F1): a postcondition free var outside {params, _0} is a
        // callee-internal symbol; left unrebound it would capture a same-named caller
        // local — a false-PROVE. It must be DROPPED, never injected.
        use crate::generate::build_semantic_guard_map_with_summaries;
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(post_eq_stray())
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        // The only clause is unrebindable -> nothing is injectable.
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "an unrebindable postcondition must not be assumed");
        // And no `_stray`-bearing fact reaches the post-call block.
        let map = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !bb1.iter().any(|f| mentions_var(f, "_stray")),
            "the stray callee symbol must not leak into the caller: {bb1:?}"
        );
    }

    #[test]
    fn rebindable_clause_still_needs_authoritative_evidence() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_postcondition(post_eq_stray())
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        let map = crate::generate::build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(!bb1.iter().any(|f| mentions_var(f, "_stray")), "stray sibling dropped: {bb1:?}");
        assert!(!bb1.iter().any(|f| has_versioned_var_and_int(f, 100)));
    }

    #[test]
    fn quantified_precondition_binder_does_not_capture_caller_arg() {
        // audit R2 #1 (CRITICAL false-PROVE): a callee precondition
        // `forall input in 0..2, p >= input` whose binder collides with the caller's
        // argument local `input` must NOT capture it. Capture would collapse the
        // body to `forall input, input >= input` (a tautology), making the
        // Precondition VC `Not(tautology)` = UNSAT = vacuously PROVED with no real
        // check. The fix routes through the capture-avoiding rebinder.
        use trust_types::Symbol;
        let caller = caller_with_arithmetic(); // bb0: _2 = parse(input)  [arg = local 1 "input"]
        let v = |n: &str| Formula::Var(n.into(), Sort::Int);
        let pre = Formula::Forall(
            vec![(Symbol::intern("input"), Sort::Int)],
            Box::new(Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Le(Box::new(Formula::Int(0)), Box::new(v("input"))),
                    Formula::Lt(Box::new(v("input")), Box::new(Formula::Int(2))),
                ])),
                Box::new(Formula::Ge(Box::new(v("p")), Box::new(v("input")))),
            )),
        );
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["p".to_string()])
                .with_precondition(pre),
        );
        let r = modular_vcgen(&caller, &db);
        let pre_vc = r
            .precondition_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .expect("a precondition VC");
        assert!(
            pre_vc.formula.free_variables().contains("input"),
            "the caller arg `input` must survive as a FREE var (not captured): {:?}",
            pre_vc.formula
        );
    }

    #[test]
    fn quantified_postcondition_still_needs_authoritative_evidence() {
        use trust_types::Symbol;
        let caller = caller_with_arithmetic();
        let post = Formula::Forall(
            vec![(Symbol::intern("i"), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Var("i".into(), Sort::Int)),
            )),
        );
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(post)
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "rebindability is not proof authority");
    }

    /// Helper: build a function with two calls — one with summary, one without.
    fn caller_two_callees() -> VerifiableFunction {
        VerifiableFunction {
            name: "process".to_string(),
            def_path: "test::process".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("parsed".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("result".into()) },
                    LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    // bb0: parsed = validate(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "validate".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: result = unknown_fn(parsed)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            is_foreign: false,
                            func: "unknown_fn".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb2: _4 = CheckedAdd(result, 1)
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(4, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
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

    #[test]
    fn test_summary_database_insert_and_get() {
        let mut db = SummaryDatabase::new();
        assert!(db.is_empty());

        let summary = FunctionSummary::new("parse")
            .with_precondition(Formula::Bool(true))
            .with_postcondition(Formula::Ge(
                Box::new(Formula::Var("result".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();

        db.insert(summary);
        assert_eq!(db.len(), 1);

        let found = db.get("parse").expect("should find parse");
        assert_eq!(found.name, "parse");
        assert!(found.proved);
        assert_eq!(found.preconditions.len(), 1);
        assert_eq!(found.postconditions.len(), 1);

        assert!(db.get("nonexistent").is_none());
    }

    #[test]
    fn test_modular_vcgen_no_summaries_produces_havoced_calls() {
        let func = caller_with_arithmetic();
        let db = SummaryDatabase::new();

        let result = modular_vcgen(&func, &db);

        // parse call should be havoced (no summary)
        assert_eq!(result.havoced_calls, 1);
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
        // overflow checks now in trust-mc-lib. CheckedBinaryOp no
        // longer generates ArithmeticOverflow VCs from trust_vcgen.
        // Body VCs may be empty (no overflow VCs produced by vcgen).
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "without summaries, VCs should not be wrapped in Implies"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_proved_summary_does_not_inject_assumptions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // safe-api: use the REAL lowering (`result` -> `_0`). parse's
        // postcondition `_0 >= 0` is a fact about parse's RESULT; at the call
        // site it must be rebound to the caller binding `n` (dest local 2), and
        // must NOT be left aliasing compute's OWN return local `_0` — the latter
        // is the false-PROVE closed by rebind_callee_postconditions.
        let postcond =
            Formula::Ge(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(0)));

        let summary = FunctionSummary::new("parse").with_postcondition(postcond.clone()).proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1);
        assert!(result.precondition_vcs.is_empty(), "no preconditions on parse");

        // Proved callee postconditions are stored as evidence but are not
        // injected as global premises into caller body VCs.
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs must not be wrapped with callee postconditions"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_generates_precondition_vcs() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let summary = FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_precondition(precond.clone())
            .with_postcondition(postcond)
            .proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        // Should generate 1 precondition VC for parse's precondition
        assert_eq!(result.precondition_vcs.len(), 1, "should generate one precondition VC");
        let pre_vc = &result.precondition_vcs[0];
        assert!(
            matches!(&pre_vc.kind, VcKind::Precondition { callee } if callee == "parse"),
            "precondition VC should reference parse"
        );
        assert_eq!(pre_vc.function, "compute", "VC should be in caller's context");
        // Formula is Not(precondition) — solver checks if negation is satisfiable
        assert!(
            matches!(&pre_vc.formula, Formula::Not(inner) if **inner == precond),
            "precondition VC formula should be Not(precondition)"
        );
    }

    #[test]
    fn test_modular_vcgen_unproved_summary_is_havoced() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // Insert unproved summary — should be treated as havoc
        let summary = FunctionSummary::new("parse").with_postcondition(Formula::Bool(true));
        // Note: not calling .proved()
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.havoced_calls, 1, "unproved summary should be havoced");
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
    }

    /// True if `name` appears as a Var/SymVar anywhere in `f`.
    fn mentions_var(f: &Formula, name: &str) -> bool {
        let mut found = false;
        f.visit(&mut |sub| {
            if sub.var_name() == Some(name) {
                found = true;
            }
        });
        found
    }

    // safe-api: callee postconditions must be REBOUND at the call site
    // (formals -> actual args, callee result `_0` -> caller destination), not
    // injected verbatim. Verbatim injection aliases the caller's own `_0` (a
    // false-PROVE) and never reaches the caller binding. These exercise
    // `rebind_callee_postconditions` directly so they are independent of which
    // body VCs the active pipeline emits.
    #[test]
    fn rebind_maps_result_to_dest_and_formals_to_actuals() {
        use crate::generate::rebind_callee_postconditions;
        // compute: local 0 unnamed ("_0" = its own return), local 1 = "input",
        // local 2 = "n" (the destination of `n = parse(input)`).
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::local(2);
        let summary = FunctionSummary::new("parse")
            .with_param_names(vec!["p0".into()])
            // `result > 0`
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            // `result == p0` (exercises result->dest AND formal->actual together)
            .with_postcondition(Formula::Eq(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Var("p0".into(), Sort::Int)),
            ))
            .proved();

        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert_eq!(rebound.len(), 2);

        // `_0` -> dest `n`, and crucially the caller's own `_0` does NOT survive.
        assert!(matches!(&rebound[0], Formula::Gt(l, _) if l.var_name() == Some("n")));
        assert!(!mentions_var(&rebound[0], "_0"), "false-PROVE: caller `_0` must not survive");

        // `_0` -> `n` AND formal `p0` -> actual arg local 1 ("input").
        assert!(matches!(&rebound[1], Formula::Eq(l, r)
                if l.var_name() == Some("n") && r.var_name() == Some("input")));
        assert!(!mentions_var(&rebound[1], "p0"), "formal must be rebound to the actual");
        assert!(!mentions_var(&rebound[1], "_0"), "false-PROVE: caller `_0` must not survive");
    }

    #[test]
    fn rebind_tail_call_identity_is_correct_not_a_bug() {
        use crate::generate::rebind_callee_postconditions;
        // `return f(x)` lowers the call dest to the caller's OWN return local 0.
        // Then the callee result genuinely IS the caller return, so `_0` -> `_0`
        // is the correct identity — a surviving `_0` here is NOT the bug.
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::local(0);
        let summary = FunctionSummary::new("parse")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert!(
            matches!(&rebound[0], Formula::Gt(l, _) if l.var_name() == Some("_0")),
            "tail-call dest = caller return: `_0` -> `_0` is the correct identity"
        );
    }

    #[test]
    fn rebind_distinct_dests_are_not_last_write_wins() {
        use crate::generate::rebind_callee_postconditions;
        // process: local 2 = "parsed", local 3 has the source debug name
        // "result". `result` is reserved by the contract surface for the return
        // place, so the distinct ordinary local must use its injective fallback
        // `_3` rather than aliasing `_0` through a source-level spelling.
        let func = caller_two_callees();
        let args = vec![Operand::Copy(Place::local(1))];
        let summary = FunctionSummary::new("validate")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let r2 = rebind_callee_postconditions(&func, &args, &Place::local(2), &summary);
        let r3 = rebind_callee_postconditions(&func, &args, &Place::local(3), &summary);
        assert!(matches!(&r2[0], Formula::Gt(l, _) if l.var_name() == Some("parsed")));
        assert!(matches!(&r3[0], Formula::Gt(l, _) if l.var_name() == Some("_3")));
    }

    #[test]
    fn rebind_projected_dest_binds_to_dest_not_caller_return() {
        use crate::generate::rebind_callee_postconditions;
        // Whole-`_0` postcondition with a projected destination must bind to the
        // projected dest place, never silently to an unrelated caller local
        // (above all, not the caller's own return `_0`).
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::field(3, 0);
        let summary = FunctionSummary::new("parse")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert!(
            !mentions_var(&rebound[0], "_0"),
            "projected dest must not leave the postcondition aliasing the caller return `_0`"
        );
    }

    #[test]
    fn test_modular_vcgen_mixed_proved_and_unknown() {
        let func = caller_two_callees();
        let mut db = SummaryDatabase::new();

        let postcond =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        // validate has a proved summary; unknown_fn does not
        let summary =
            FunctionSummary::new("validate").with_postcondition(postcond.clone()).proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 2, "both calls leave return postconditions unmodeled");
        assert!(result.precondition_vcs.is_empty(), "validate has no preconditions");

        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs must not assume validate's postcondition"
            );
        }
    }

    #[test]
    fn test_summary_sync_is_inert_without_replayable_evidence() {
        let mut db = SummaryDatabase::new();
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        // Even the old test-only "checked" label is just constructible metadata.
        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .with_checked_proof_evidence(
                    "proof:parse:postcondition",
                    ProofStrength::smt_unsat(),
                ),
        );

        // Unproved summary does NOT sync
        db.insert(FunctionSummary::new("unsafe_parse").with_postcondition(Formula::Bool(true)));

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0);
        let facts = spec_db.postconditions_for("parse");
        assert!(facts.is_empty());
    }

    #[test]
    fn test_summary_sync_rejects_proved_boolean_without_evidence() {
        let mut db = SummaryDatabase::new();
        db.insert(FunctionSummary::new("parse").with_postcondition(Formula::Bool(true)).proved());

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0, "plain proved flag is not reusable proof evidence");
    }

    #[test]
    fn test_summary_sync_rejects_public_fake_evidence() {
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(Formula::Bool(true))
                .with_proof_evidence("proof:parse:fake", ProofStrength::smt_unsat()),
        );

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0, "public evidence strings are not reusable proof evidence");
    }

    #[test]
    fn test_caller_callee_verification_chain() {
        // Scenario: parse() has proved summary with postcondition n >= 0.
        // compute() calls parse() then does n + 1.
        // overflow checks now in trust-mc-lib, so body_vcs may be empty.
        // We verify the modular infrastructure (no assumption injection, spec sync).

        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .with_checked_proof_evidence("proof:parse:chain", ProofStrength::smt_unsat()),
        );

        let result = modular_vcgen(&func, &db);

        // Step 1: postcondition facts are not injected as caller assumptions.
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1);

        // Step 2: if any body VCs exist, they must not be strengthened with
        // callee postconditions as global premises.
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "callee postcondition must not be a global premise"
            );
        }

        // Step 3: both authority consumers remain closed.
        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);
        let spec_facts = spec_db.postconditions_for("parse");
        assert!(spec_facts.is_empty());
    }

    #[test]
    fn extracted_body_is_inert_analysis_metadata() {
        // W3/F6b: attaching an extracted body is an ANALYSIS INPUT — it must
        // not flip any authority bit (proved / reusable evidence), and it
        // defaults to absent so every non-verifier producer stays fail-closed.
        let summary = FunctionSummary::new("f");
        assert!(summary.extracted_body.is_none(), "default: no body attached");
        let summary =
            summary.with_extracted_body(std::sync::Arc::new(caller_with_arithmetic()));
        assert!(summary.extracted_body.is_some());
        assert!(!summary.proved, "an extracted body must not mint proof status");
        assert!(!summary.has_reusable_postcondition_evidence());
    }

    #[test]
    fn test_function_summary_builder_pattern() {
        let summary = FunctionSummary::new("f")
            .with_precondition(Formula::Bool(true))
            .with_precondition(Formula::Bool(false))
            .with_postcondition(Formula::Int(42))
            .proved();

        assert_eq!(summary.name, "f");
        assert_eq!(summary.preconditions.len(), 2);
        assert_eq!(summary.postconditions.len(), 1);
        assert!(summary.proved);
    }

    #[test]
    fn test_modular_vcgen_empty_function() {
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

        let db = SummaryDatabase::new();
        let result = modular_vcgen(&func, &db);

        assert!(result.body_vcs.is_empty());
        assert!(result.precondition_vcs.is_empty());
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 0);
    }

    #[test]
    fn test_modular_vcgen_multiple_preconditions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let pre1 = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let pre2 = Formula::Le(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(1000)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(pre1.clone())
                .with_precondition(pre2.clone())
                .with_postcondition(Formula::Bool(true))
                .proved(),
        );

        let result = modular_vcgen(&func, &db);

        // Should generate 2 precondition VCs — one per precondition
        assert_eq!(result.precondition_vcs.len(), 2);
        assert!(matches!(
            &result.precondition_vcs[0].formula,
            Formula::Not(inner) if **inner == pre1
        ));
        assert!(matches!(
            &result.precondition_vcs[1].formula,
            Formula::Not(inner) if **inner == pre2
        ));
    }

    // --- Tests for ContractCheck, ModularVerifier, generate_modular_vcs ---

    #[test]
    fn test_contract_check_enum_variants() {
        let pre = ContractCheck::PreConditionAtCallSite {
            callee: "parse".to_string(),
            precondition_index: 0,
        };
        let post = ContractCheck::PostConditionOnReturn { postcondition_index: 1 };
        let frame = ContractCheck::FramePreservation { variable: "state".to_string() };

        assert_eq!(pre, pre.clone());
        assert_eq!(post, post.clone());
        assert_eq!(frame, frame.clone());
        // Ensure they're distinct
        assert_ne!(
            ContractCheck::PreConditionAtCallSite { callee: "a".into(), precondition_index: 0 },
            ContractCheck::PreConditionAtCallSite { callee: "b".into(), precondition_index: 0 },
        );
    }

    #[test]
    fn test_generate_modular_vcs_precondition_at_call_site() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(precond.clone())
                .proved(),
        );

        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 precondition VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Precondition { callee } if callee == "parse"
        ));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == precond
        ));
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_on_return() {
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let func = VerifiableFunction {
            name: "producer".to_string(),
            def_path: "test::producer".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 postcondition VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == postcond
        ));
        assert_eq!(vcs[0].function, "producer");
    }

    #[test]
    fn modular_ungrounded_spec_model_postcondition_is_unknown_not_refutable() {
        // A parsed ensures over SYNTHETIC spec-model terms (here the Result
        // model of ny-cert `check_farkas`: `is_ok ∧ payload_sign > 0`, negated)
        // is under-constrained in this lane — nothing grounds `_0_discr` /
        // `_0_value_sign` — so the old `Not(post)` VC was satisfiable by havoc
        // (Failed with a minted, non-program counterexample). It must emit the
        // fail-closed NON-REFUTABLE Unknown shape instead, and never vanish.
        let is_ok = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("_0_discr".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )));
        let sign_pos = Formula::Gt(
            Box::new(Formula::Var("_0_value_sign".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postcond = Formula::Not(Box::new(Formula::And(vec![is_ok, sign_pos])));

        let func = VerifiableFunction {
            name: "check_farkas".to_string(),
            def_path: "test::check_farkas".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "the obligation must not vanish: {vcs:#?}");
        assert!(
            matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND),
            "ungrounded postcondition must be the fail-closed Unknown shape: {:?}",
            vcs[0].kind
        );
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "no refutable Postcondition VC may be minted: {vcs:#?}"
        );
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_from_field() {
        let postcond =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        let func = VerifiableFunction {
            name: "bounded".to_string(),
            def_path: "test::bounded".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::usize(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "postcondition should generate 1 VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_generate_modular_vcs_no_contracts_no_vcs() {
        let func = VerifiableFunction {
            name: "plain".to_string(),
            def_path: "test::plain".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);
        assert!(vcs.is_empty(), "no contracts -> no modular VCs");
    }

    #[test]
    fn test_modular_verifier_delegates_to_generate() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Bool(true);
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(precond)
                .proved(),
        );

        let verifier = ModularVerifier::new(db);
        let vcs = verifier.verify(&func);

        assert_eq!(vcs.len(), 1);
        assert_eq!(verifier.summaries().len(), 1);
    }

    #[test]
    fn test_generate_modular_vcs_unproved_preconditions_are_enforced() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(Formula::Bool(true)),
        );

        let vcs = generate_modular_vcs(&func, &db);
        assert_eq!(vcs.len(), 1, "declared callee preconditions are caller obligations");
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "parse"));
    }
}

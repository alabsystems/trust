// trust_vcgen/contracts.rs: Contract-based VC generation
//
// Converts parsed function contracts into verification conditions.
// Extended to support trust-wp-style contracts (loop invariants,
// type refinements, modifies clauses) that lower to Horn clauses.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, ContractMetadata, Formula,
    LoopContractKind, LoopContractSpec, Operand, Projection, Rvalue, Sort, SourceSpan, Statement,
    Symbol, Terminator, Ty, UnOp, VcKind, VerifiableFunction, VerificationCondition,
    parse_spec_expr,
};
#[cfg(test)]
use trust_types::{LocalDecl, VerifiableBody};

/// `VcKind::UnsupportedMir` family tag for an `#[ensures]` predicate that
/// references synthetic spec-model terms no body fact grounds (see
/// [`ungrounded_spec_model_vars`]). Kept as one stable constant so the v2
/// contract lane can recognize (and de-duplicate) the rows this module and
/// `spec_parser` emit for the same contract.
pub(crate) const SPEC_MODEL_UNGROUNDED_KIND: &str = "SpecModelUngrounded";

/// `VcKind::UnsupportedMir` family tag for an `#[ensures]` whose predicate body
/// does not parse at all (e.g. a raw spec closure whose `matches!` never got
/// compiler-lowered). Distinct from [`SPEC_MODEL_UNGROUNDED_KIND`] so the v2
/// contract lane's de-duplication (which re-derives ungrounded rows from the
/// contract set) never drops an unparseable-ensures row it cannot re-derive.
pub(crate) const SPEC_ENSURES_UNPARSEABLE_KIND: &str = "SpecEnsuresUnparseable";

/// `VcKind::UnsupportedMir` family tag for a source contract that the active
/// formula frontend cannot elaborate. Such a clause is an explicit proof gap,
/// not a refutable program property and never something that may disappear.
pub(crate) const SPEC_UNVERIFIABLE_KIND: &str = "SpecUnverifiable";

/// The compiler lowers a contract predicate with this marker prefix
/// (`__trust_lowered_compiler_contract__:(x) < (100)`); strip it before
/// parsing the predicate. Shared by [`check_contracts`] and the v2 contract
/// lane's Requires de-duplication so both parse the same spelling.
pub(crate) const LOWERED_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";

const LOOP_CONTRACT_UNSUPPORTED_KIND: &str = "UserLoopContractUnsupported";
use trust_types::assumption::UNSUPPORTED_COMPILER_CONTRACT_PREFIX;
pub(crate) use trust_types::UNPAIRED_LOOP_CONTRACT_PREFIX;

/// Pair compiler-owned E4/E5 clauses with the natural-loop headers recovered
/// from the extracted MIR. Clauses are grouped by the compiler-minted source
/// loop id and the whole group is bound once, using its shared header span as
/// evidence. Source spans are never treated as identity keys and no individual
/// clause may select a different MIR header. The dense function-contract
/// vector in the compiler bundle is never perturbed.
///
/// Returns source indices that could not be paired.  The rustc caller turns
/// these into hard authored-spec errors; the generator also retains an
/// `UnsupportedMir` row for defense in depth.
pub fn bind_compiler_loop_contracts(
    func: &mut VerifiableFunction,
    specs: &[LoopContractSpec],
) -> Vec<(usize, String)> {
    let loops = crate::termination::detect_loops(&func.body);
    let mut failures = Vec::new();
    let mut bindings: FxHashMap<u32, Result<BlockId, String>> = FxHashMap::default();

    // Compute one binding decision per compiler-minted source-loop identity.
    // In particular, do not let invariant/decreases clauses independently use
    // source ordering to choose among headers: that could split one authored
    // loop across different MIR loops.
    for spec in specs {
        if bindings.contains_key(&spec.source_loop_id) {
            continue;
        }
        let group: Vec<_> = specs
            .iter()
            .filter(|candidate| candidate.source_loop_id == spec.source_loop_id)
            .collect();
        let evidence_is_consistent = group.iter().all(|candidate| {
            candidate.loop_head == spec.loop_head && candidate.header_span == spec.header_span
        });
        let binding = if !evidence_is_consistent {
            Err(format!(
                "source loop {} carries inconsistent loop/header span evidence across its clauses",
                spec.source_loop_id
            ))
        } else if !source_span_contains(&spec.loop_head, &spec.header_span) {
            Err(format!(
                "source loop {} carries a missing or out-of-loop header span",
                spec.source_loop_id
            ))
        } else {
            // `detect_loops` has one row per back-edge, so a multi-latch loop
            // can repeat the same header. De-duplicate by semantic MIR block
            // identity before requiring a unique match.
            let candidates: FxHashSet<_> = loops
                .iter()
                .filter_map(|loop_info| {
                    let header = func.body.blocks.get(loop_info.header.0)?;
                    let terminator_span = terminator_source_span(&header.terminator);
                    source_span_contains(&spec.header_span, &terminator_span)
                        .then_some(loop_info.header)
                })
                .collect();
            match candidates.len() {
                1 => Ok(*candidates.iter().next().expect("one candidate")),
                0 => pair_loop_from_body_source_evidence(func, &loops, spec),
                count => Err(format!(
                    "source loop {} ambiguously matched {count} MIR natural-loop headers using its header span",
                    spec.source_loop_id
                )),
            }
        };
        bindings.insert(spec.source_loop_id, binding);
    }

    for (index, spec) in specs.iter().enumerate() {
        if spec.body.starts_with(UNSUPPORTED_COMPILER_CONTRACT_PREFIX)
            || parse_spec_expr(&spec.body).is_none()
        {
            failures.push((
                index,
                format!(
                    "authored loop clause `{}` is not in the supported typed spec fragment",
                    spec.body
                ),
            ));
        }
        let kind = match spec.kind {
            LoopContractKind::Invariant => ContractKind::LoopInvariant,
            LoopContractKind::Decreases => ContractKind::Decreases,
        };
        let Some(binding) = bindings.get(&spec.source_loop_id) else {
            // Every non-empty input group is inserted above; retain a total,
            // fail-closed fallback for malformed internal state.
            failures.push((index, "source-loop binding decision is missing".to_string()));
            func.contracts.push(Contract {
                kind,
                span: spec.span.clone(),
                body: format!("{UNPAIRED_LOOP_CONTRACT_PREFIX}{}", spec.body),
            });
            continue;
        };
        let header = match binding {
            Ok(header) => *header,
            Err(reason) => {
                failures.push((index, reason.clone()));
                func.contracts.push(Contract {
                    kind,
                    span: spec.span.clone(),
                    body: format!("{UNPAIRED_LOOP_CONTRACT_PREFIX}{}", spec.body),
                });
                continue;
            }
        };
        func.contracts.push(Contract {
            kind,
            span: spec.span.clone(),
            body: format!("bb{}: {}", header.0, spec.body),
        });
    }

    failures
}

fn source_span_contains(outer: &SourceSpan, inner: &SourceSpan) -> bool {
    if outer.file.is_empty() || inner.file.is_empty() || outer.file != inner.file {
        return false;
    }
    let outer_lo = (outer.line_start, outer.col_start);
    let outer_hi = (outer.line_end, outer.col_end);
    let inner_lo = (inner.line_start, inner.col_start);
    let inner_hi = (inner.line_end, inner.col_end);
    outer_lo <= inner_lo && inner_hi <= outer_hi
}

/// SF-6 fallback for compiler `while` lowering whose natural-loop header has a
/// span-less terminator. Unique header-span evidence remains the primary lane.
/// For each natural loop this path uses the earliest span in the loop's own
/// blocks that is contained by the compiler-owned complete source-loop span.
/// Function-level spans that ride along in real natural-loop block sets are
/// ignored rather than poisoning the choice.
///
/// This fallback is deliberately restricted to a source span containing
/// exactly one distinct MIR natural-loop header. An outer natural-loop body
/// contains every inner-loop statement, so relative source order or structural
/// nesting cannot authenticate which header an authored HIR loop denotes. Any
/// second candidate therefore fails closed, even when one candidate has earlier
/// evidence or the two natural-loop bodies are nested. A compiler-owned
/// source-loop-to-MIR-header identity is required to authorize that case.
fn pair_loop_from_body_source_evidence(
    func: &VerifiableFunction,
    loops: &[crate::termination::LoopInfo],
    spec: &LoopContractSpec,
) -> Result<BlockId, String> {
    // `detect_loops` has one row per back-edge. Collapse multi-latch rows by
    // semantic header identity and retain the earliest contained evidence for
    // that header before checking uniqueness.
    let mut by_header: FxHashMap<BlockId, SourceSpan> = FxHashMap::default();
    for loop_info in loops {
        let Some(span) = earliest_contained_loop_span(func, loop_info, &spec.loop_head) else {
            continue;
        };
        by_header
            .entry(loop_info.header)
            .and_modify(|current| {
                if source_span_order_key(&span) < source_span_order_key(current) {
                    *current = span.clone();
                }
            })
            .or_insert(span);
    }
    let mut candidates = by_header.into_iter().collect::<Vec<_>>();
    candidates.sort_by_key(|(_, span)| source_span_order_key(span));
    match candidates.as_slice() {
        [] => Err(format!(
            "source loop {} could not be paired with a MIR natural-loop header using header or earliest contained in-loop source evidence",
            spec.source_loop_id
        )),
        [(header, _)] => Ok(*header),
        _ => Err(format!(
            "source loop {} ambiguously covered {} MIR natural-loop headers using contained source evidence; span fallback requires exactly one distinct header",
            spec.source_loop_id,
            candidates.len()
        )),
    }
}

fn source_span_order_key(span: &SourceSpan) -> (u32, u32, u32, u32) {
    (span.line_start, span.col_start, span.line_end, span.col_end)
}

/// The earliest source span within a natural loop's blocks (statement spans
/// plus span-bearing terminators) that is CONTAINED in `outer`. `None` when no
/// in-loop span falls inside `outer` — pairing then fails closed. Containment
/// is the pairing evidence itself: fn-signature-spanned argument copies and
/// other out-of-loop-source spans that ride along in the natural-loop block
/// set are simply skipped rather than poisoning the choice.
fn earliest_contained_loop_span(
    func: &VerifiableFunction,
    loop_info: &crate::termination::LoopInfo,
    outer: &SourceSpan,
) -> Option<SourceSpan> {
    let mut earliest: Option<SourceSpan> = None;
    let mut consider = |span: &SourceSpan| {
        if span.file.is_empty() || !source_span_contains(outer, span) {
            return;
        }
        if earliest
            .as_ref()
            .is_none_or(|current| source_span_order_key(span) < source_span_order_key(current))
        {
            earliest = Some(span.clone());
        }
    };
    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else { continue };
        for statement in &block.stmts {
            if let Statement::Assign { span, .. } = statement {
                consider(span);
            }
        }
        consider(&terminator_source_span(&block.terminator));
    }
    earliest
}

fn terminator_source_span(term: &Terminator) -> SourceSpan {
    match term {
        Terminator::SwitchInt { span, .. }
        | Terminator::Call { span, .. }
        | Terminator::Assert { span, .. }
        | Terminator::Drop { span, .. }
        | Terminator::Opaque { span, .. } => span.clone(),
        _ => SourceSpan::default(),
    }
}

/// True for the SYNTHETIC MODEL variable names the string spec parser
/// (`trust_types::spec_parse::map_method_call`) mints for Option/Result payload
/// and numeric sign predicates:
///
/// - `{base}_discr`  — `is_ok()` / `is_err()` / `is_some()` / `is_none()`
/// - `{base}_value`  (and any `.field` projection of it, including the
///   positional `.__trust_ok_<i>` tuple binds a lowered
///   `matches!(r, Ok((a, b)) if ..)` produces) — `unwrap()` / `matches!` payload
/// - `{base}_sign`   — `is_positive()` / `is_negative()` / `is_zero()`
///
/// NO VC-generation lane grounds these names to MIR facts today: nothing links
/// `_0_discr` to the return slot's discriminant (`_0.__tag`), or `_0_value*` /
/// `*_sign` to payload fields. They are free (havoc'd) in every emitted VC.
///
/// Matching is deliberately by NAME SHAPE (suffix / marker segment): a false
/// positive can only route an obligation to the fail-closed Unknown shape
/// (drop-only, sound); a false negative keeps today's behavior.
pub(crate) fn is_spec_model_var(name: &str) -> bool {
    // Strip a statement-version token (`x#s1_0`) defensively; these formulas
    // are inspected pre-versioning, but the check must stay stable if a
    // versioned copy is ever inspected.
    let base = name.split('#').next().unwrap_or(name);
    if base.contains(".__trust_ok_") {
        return true;
    }
    // A `{base}_value.field` projection keeps the `_value` marker in its first
    // path segment (spec_parse only projects fields off the payload term).
    let head = base.split('.').next().unwrap_or(base);
    head.ends_with("_discr") || head.ends_with("_sign") || head.ends_with("_value")
}

/// The synthetic spec-model variables (see [`is_spec_model_var`]) occurring
/// FREE in `formula`, sorted and de-duplicated. Non-empty means the formula is
/// an UNDER-CONSTRAINED encoding of its source predicate: its negation is
/// satisfiable by havoc regardless of the function body, so a solver "SAT"
/// over it mints an assignment that is NOT a program counterexample.
pub(crate) fn ungrounded_spec_model_vars(formula: &Formula) -> Vec<String> {
    let mut vars: Vec<String> =
        formula.free_variables().into_iter().filter(|name| is_spec_model_var(name)).collect();
    vars.sort();
    vars.dedup();
    vars
}

/// Build the fail-closed, NON-REFUTABLE obligation for an `#[ensures]` whose
/// predicate parses but cannot be grounded (it references synthetic spec-model
/// terms — see [`ungrounded_spec_model_vars`]).
///
/// SOUNDNESS: emitting the usual refutable `Not(post)` for such a predicate
/// reports Failed with a MINTED counterexample (an assignment to havoc'd model
/// variables, not a program trace) — a refutation of an under-constrained
/// encoding, not of the program. Silently dropping the contract would be a
/// false-PROVE. The honest verdict is UNKNOWN: `VcKind::UnsupportedMir` is the
/// codebase's non-refutable fail-closed shape — `generate_vcs_with_discharge`
/// preclassifies it to `VerificationResult::Unknown` (never solver-dispatched,
/// never Proved), and direct solver callers see the always-SAT `Bool(true)`
/// violation formula (never a proof).
pub(crate) fn spec_model_ungrounded_vc(
    func: &VerifiableFunction,
    span: SourceSpan,
    origin: &str,
    ungrounded: &[String],
    contract_metadata: Option<ContractMetadata>,
) -> VerificationCondition {
    fail_closed_ensures_vc(
        func,
        span,
        SPEC_MODEL_UNGROUNDED_KIND,
        format!(
            "postcondition references spec-model terms ({}) that no body fact grounds \
             (fail-closed Unknown, never a refutable under-constrained VC): {origin}",
            ungrounded.join(", ")
        ),
        contract_metadata,
    )
}

/// Build the fail-closed, NON-REFUTABLE obligation for an `#[ensures]` whose
/// predicate body does not parse. The obligation must not vanish (a
/// false-PROVE) and must not become an always-SAT refutable formula that
/// reports Failed for a contract the encoding simply cannot read — the honest
/// verdict is UNKNOWN, via the same preclassified `UnsupportedMir` shape as
/// [`spec_model_ungrounded_vc`]. Other contract kinds keep the
/// `spec_failure_vc` convention unchanged.
pub(crate) fn spec_ensures_unparseable_vc(
    func: &VerifiableFunction,
    span: SourceSpan,
    origin: &str,
) -> VerificationCondition {
    fail_closed_ensures_vc(
        func,
        span,
        SPEC_ENSURES_UNPARSEABLE_KIND,
        format!("unparseable `#[ensures]` predicate (fail-closed Unknown): {origin}"),
        None,
    )
}

fn fail_closed_ensures_vc(
    func: &VerifiableFunction,
    span: SourceSpan,
    kind: &str,
    detail: String,
    contract_metadata: Option<ContractMetadata>,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir { kind: kind.to_string(), detail },
        function: func.name.as_str().into(),
        location: span,
        // Fail closed for DIRECT solver callers too: VCs are violation
        // formulas, so `Bool(true)` is SAT and can never be reported as a
        // proof. The compiler path preclassifies `UnsupportedMir` to Unknown
        // before solver dispatch (`generate_vcs_with_discharge`).
        formula: Formula::Bool(true),
        contract_metadata,
    }
}

/// Exact, function-bound candidate for reusing one authored loop invariant as
/// a downstream loop-head fact.
///
/// This value proves only that the supplied E4 initiation and consecution rows
/// are exact production reconstructions for `func`; it carries **no proof
/// authority**. Its fields are deliberately private and it is not serializable,
/// so callers cannot alter its function/loop binding after validation. The
/// compiler must wrap a candidate in its own crate-private proof capability
/// only after checking private, row-aligned authority for both E4 rows: either
/// kernel-certified authority or S3's consumed affine exact-direct CHC/PDR
/// receipt. Public result labels and all other private authority variants are
/// deliberately ineligible.
#[derive(Debug, Clone, PartialEq)]
pub struct LoopInvariantFeedbackCandidate {
    function_digest: String,
    function_name: String,
    function_def_path: String,
    header_block: usize,
    source_text: String,
    source_span: SourceSpan,
    predicate: Formula,
}

impl LoopInvariantFeedbackCandidate {
    /// The MIR natural-loop header this fact is scoped to.
    #[must_use]
    pub fn header_block(&self) -> usize {
        self.header_block
    }

    /// The canonical authored predicate text carried by the E4 obligations.
    #[must_use]
    pub fn source_text(&self) -> &str {
        &self.source_text
    }
}

/// Opaque, function-bound reconstruction context for a batch of E4 candidates.
/// Preparing it computes the production interval fixpoint once; its fields are
/// private and the type is not serializable, so callers cannot manufacture an
/// environment that merely has the right formula shape.
#[derive(Debug, Clone)]
pub struct LoopInvariantFeedbackContext {
    function_payload: String,
    interval_environment: crate::abstract_interp::IntervalDomain,
}

fn proof_gated_function_digest(function_payload: &str) -> String {
    trust_types::stable_sha256_hex(
        format!("trust.e4.function-payload.v1:{}:{function_payload}", function_payload.len())
            .as_bytes(),
    )
}

/// Prepare exact production E4 reconstruction once for all invariant pairs in
/// one function. Work-budget exhaustion returns `None` and cannot produce a
/// partial context.
#[must_use]
pub fn prepare_loop_invariant_feedback_validation(
    func: &VerifiableFunction,
) -> Option<LoopInvariantFeedbackContext> {
    let _work_scope = crate::gen_work_scope();
    let function_payload = serde_json::to_string(func).ok()?;
    // Reconstruct the same production interval environment used by ordinary
    // VC generation. The context still seals the complete, unsanitized function
    // payload above; only unsafe parsed contract assumptions are removed from
    // abstract interpretation. Otherwise an unrelated unmodeled precondition
    // could make exact production E4 rows impossible to recognize.
    let arithmetic_safe_func = crate::generate::without_unmodeled_contract_arithmetic(func);
    let interval_environment =
        crate::abstract_interp::merged_interval_environment(arithmetic_safe_func.as_ref());
    if crate::gen_work_tripped() {
        return None;
    }
    Some(LoopInvariantFeedbackContext { function_payload, interval_environment })
}

/// Validate that an E4 pair is an exact production reconstruction and return a
/// function-bound, non-authoritative feedback candidate.
///
/// This function deliberately does not accept a proof-verdict callback. Such a
/// callback is forgeable at a public crate boundary (`|_| true`) and therefore
/// cannot mint authority. It reconstructs the authored E4 obligations from
/// `func` and requires byte-semantic equality of the pair:
/// function, kind, header, predicate text, source span, formula, and contract
/// routing metadata. Proof authority remains exclusively in the compiler crate.
#[must_use]
pub fn loop_invariant_feedback_candidate(
    func: &VerifiableFunction,
    initiation: &VerificationCondition,
    consecution: &VerificationCondition,
) -> Option<LoopInvariantFeedbackCandidate> {
    let context = prepare_loop_invariant_feedback_validation(func)?;
    loop_invariant_feedback_candidate_with_context(func, &context, initiation, consecution)
}

/// Batch form of [`loop_invariant_feedback_candidate`] that reuses one exact,
/// opaque production reconstruction context. The context is byte-bound to
/// `func`; cross-function or post-preparation mutation fails validation.
#[must_use]
pub fn loop_invariant_feedback_candidate_with_context(
    func: &VerifiableFunction,
    context: &LoopInvariantFeedbackContext,
    initiation: &VerificationCondition,
    consecution: &VerificationCondition,
) -> Option<LoopInvariantFeedbackCandidate> {
    let _work_scope = crate::gen_work_scope();
    if serde_json::to_string(func).ok()? != context.function_payload {
        return None;
    }
    // Match the exact production E4 view: VC generation removes unsafe parsed
    // machine-arithmetic assumptions before constructing initiation rows. The
    // context remains sealed to `func` above, so this projection cannot
    // be supplied or forged by the caller.
    let arithmetic_safe_func = crate::generate::without_unmodeled_contract_arithmetic(func);
    let reconstruction_func = arithmetic_safe_func.as_ref();
    for (contract_index, contract) in reconstruction_func.contracts.iter().enumerate() {
        if !matches!(contract.kind, ContractKind::LoopInvariant) {
            continue;
        }
        let Some((header_block, expr)) = loop_contract_body(&contract.body) else {
            continue;
        };
        let mut expected = Vec::with_capacity(2);
        generate_loop_invariant_vcs(
            reconstruction_func,
            contract_index,
            contract,
            header_block,
            expr.clone(),
            &mut expected,
        );
        let expected_initiation =
            expected.iter().find(|vc| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. }));
        let expected_consecution =
            expected.iter().find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }));
        let (Some(expected_initiation), Some(expected_consecution)) =
            (expected_initiation, expected_consecution)
        else {
            // Unsupported/ill-sorted E4 clauses produce no validatable pair.
            continue;
        };
        let augmented_initiation = crate::abstract_interp::augment_vc_with_abstract_state(
            expected_initiation,
            &context.interval_environment,
        );
        let augmented_consecution = crate::abstract_interp::augment_vc_with_abstract_state(
            expected_consecution,
            &context.interval_environment,
        );
        if crate::gen_work_tripped() {
            return None;
        }
        if !(exact_loop_invariant_vc_eq(initiation, expected_initiation)
            || exact_loop_invariant_vc_eq(initiation, &augmented_initiation))
            || !(exact_loop_invariant_vc_eq(consecution, expected_consecution)
                || exact_loop_invariant_vc_eq(consecution, &augmented_consecution))
        {
            continue;
        }
        let parsed = parse_spec_expr(&expr)?;
        let predicate = type_and_validate_loop_formula(reconstruction_func, parsed, Sort::Bool)?;
        return Some(LoopInvariantFeedbackCandidate {
            function_digest: proof_gated_function_digest(&context.function_payload),
            function_name: func.name.clone(),
            function_def_path: func.def_path.clone(),
            header_block,
            source_text: expr,
            source_span: contract.span.clone(),
            predicate,
        });
    }
    None
}

fn exact_loop_invariant_vc_eq(
    actual: &VerificationCondition,
    expected: &VerificationCondition,
) -> bool {
    let same_kind = match (&actual.kind, &expected.kind) {
        (
            VcKind::LoopInvariantInitiation {
                invariant: actual_invariant,
                header_block: actual_header,
            },
            VcKind::LoopInvariantInitiation {
                invariant: expected_invariant,
                header_block: expected_header,
            },
        )
        | (
            VcKind::LoopInvariantConsecution {
                invariant: actual_invariant,
                header_block: actual_header,
            },
            VcKind::LoopInvariantConsecution {
                invariant: expected_invariant,
                header_block: expected_header,
            },
        ) => actual_invariant == expected_invariant && actual_header == expected_header,
        _ => false,
    };
    same_kind
        && actual.function == expected.function
        && actual.location == expected.location
        && actual.formula == expected.formula
        && actual.contract_metadata == expected.contract_metadata
}

pub(crate) fn check_contracts(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
    check_contracts_with_loop_invariant_feedback(func, vcs, &[]);
}

/// Regenerate the complete set of loop-local E5 decreases rows with exact E4
/// invariant candidates.
///
/// This is the semantic mechanism used by the compiler's private, proof-gated
/// second pass. It emits one row for each bound or fail-closed loop-local
/// decreases clause, in contract order, and no E4 or unrelated function-body
/// rows. The caller must replace all first-pass loop-decreases rows with this
/// returned set (never append it), verify that row cardinality and source
/// routing remain one-to-one, and solve every changed formula anew. This
/// function does not inspect proof results; the compiler must admit candidates
/// only through its crate-private authority.
///
/// Function-recursion decreases metadata has no `bb<N>:` prefix and is not
/// part of this loop-local replacement set.
#[must_use]
pub fn regenerate_loop_decreases_with_invariant_feedback_vcs(
    func: &VerifiableFunction,
    feedback: &[LoopInvariantFeedbackCandidate],
) -> Vec<VerificationCondition> {
    if let Err(error) = crate::validate_function(func) {
        return vec![crate::generate::malformed_trust_ir_vc(func, &error)];
    }

    let mut vcs = Vec::new();
    for (contract_index, contract) in func.contracts.iter().enumerate() {
        if matches!(contract.kind, ContractKind::Decreases) {
            append_loop_decreases_contract_vc(func, contract_index, contract, feedback, &mut vcs);
        }
    }
    vcs
}

fn append_loop_decreases_contract_vc(
    func: &VerifiableFunction,
    contract_index: usize,
    contract: &Contract,
    feedback: &[LoopInvariantFeedbackCandidate],
    vcs: &mut Vec<VerificationCondition>,
) {
    if contract.body.starts_with(UNPAIRED_LOOP_CONTRACT_PREFIX) {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            "loop decreases clause was not paired with a unique MIR natural-loop header",
        ));
        return;
    }
    if let Some((header_block, expr)) = loop_contract_body(&contract.body) {
        generate_loop_decreases_vc(
            func,
            contract_index,
            contract,
            header_block,
            expr,
            feedback,
            vcs,
        );
    }
    // A decreases clause without a bb-prefix is function-recursion metadata
    // and is consumed by `termination::check_termination`.
}

/// Generate contract VCs while reusing exact E4 candidates. The ordinary first
/// pass calls this with an empty slice. This function is internal to vcgen; the
/// compiler may reach it only through a crate-private capability that binds
/// these candidates to proof authority.
pub(crate) fn check_contracts_with_loop_invariant_feedback(
    func: &VerifiableFunction,
    vcs: &mut Vec<VerificationCondition>,
    feedback: &[LoopInvariantFeedbackCandidate],
) {
    for (contract_index, contract) in func.contracts.iter().enumerate() {
        let kind = match &contract.kind {
            ContractKind::Requires => VcKind::Precondition { callee: func.name.clone() },
            ContractKind::Ensures => VcKind::Postcondition,
            ContractKind::Invariant => {
                VcKind::Assertion { message: format!("invariant: {}", contract.body) }
            }
            ContractKind::Decreases => {
                append_loop_decreases_contract_vc(func, contract_index, contract, feedback, vcs);
                continue;
            }
            // trust-wp-style contract VC generation.
            ContractKind::LoopInvariant => {
                let Some((header_block, expr)) = loop_contract_body(&contract.body) else {
                    vcs.push(loop_contract_unsupported_vc(
                        func,
                        contract,
                        "loop clause was not paired with a MIR natural-loop header",
                    ));
                    continue;
                };
                generate_loop_invariant_vcs(
                    func,
                    contract_index,
                    contract,
                    header_block,
                    expr,
                    vcs,
                );
                continue;
            }
            ContractKind::TypeRefinement => {
                // Parse "var: predicate" format
                let (variable, predicate_str) = parse_refinement_body(&contract.body);
                let Some(parsed) = parse_spec_expr(&predicate_str) else {
                    vcs.push(spec_failure_vc(func, contract, "unparseable type refinement"));
                    continue;
                };
                if formula_uses_unmodeled_machine_arithmetic_in_function(func, &parsed) {
                    vcs.push(spec_failure_vc(
                        func,
                        contract,
                        "type refinement uses unmodeled fixed-width machine arithmetic",
                    ));
                    continue;
                }
                vcs.push(VerificationCondition {
                    kind: VcKind::TypeRefinementViolation {
                        variable: variable.clone(),
                        predicate: predicate_str,
                    },
                    function: func.name.as_str().into(),
                    location: contract.span.clone(),
                    formula: Formula::Not(Box::new(parsed)),
                    contract_metadata: Some(trust_wp_metadata()),
                });
                continue;
            }
            ContractKind::Modifies => {
                // Parse comma-separated variable list, generate frame VCs
                let vars = parse_modifies_body(&contract.body);
                // Collect all function locals not in the modifies set
                for local in &func.body.locals {
                    let name = local.name.as_deref().unwrap_or("");
                    if !name.is_empty() && !vars.contains(&name.to_string()) {
                        // Trust #integrity: the frame VC compares old/new of an
                        // unmodified local and MUST use that local's real sort, not a
                        // hardcoded Int. A bool/typed local given Int sort yields an
                        // ill-typed `NOT(old == new)` that can suppress a real frame
                        // violation (a frame/modifies false-PROVE).
                        let sort = crate::sort_for_ty(&local.ty);
                        vcs.push(VerificationCondition {
                            kind: VcKind::FrameConditionViolation {
                                variable: name.to_string(),
                                function: func.name.as_str().into(),
                            },
                            function: func.name.as_str().into(),
                            location: contract.span.clone(),
                            // Frame condition: old(var) == new(var) for unmodified vars.
                            // Check negation: NOT(old == new) is SAT iff frame is violated.
                            formula: Formula::Not(Box::new(Formula::Eq(
                                Box::new(Formula::Var(format!("{name}__old"), sort.clone())),
                                Box::new(Formula::Var(name.to_string(), sort)),
                            ))),
                            contract_metadata: Some(trust_wp_metadata()),
                        });
                    }
                }
                continue;
            }
            // `ContractKind` is `#[non_exhaustive]`, so this
            // arm catches any future variant this crate has not been updated to
            // handle. It must fail closed (emit an explicit Unknown row) rather than
            // silently generating no obligation for the contract.
            _ => {
                vcs.push(spec_failure_vc(func, contract, "unhandled contract kind"));
                continue;
            }
        };

        // The compiler lowers a contract predicate with a marker prefix
        // (see `LOWERED_CONTRACT_PREFIX`); strip it before
        // parsing so the requires/ensures becomes a real obligation. Without this
        // EVERY `#[requires]`/`#[ensures]` parsed to an "unparseable contract"
        // fail-closed `Assertion(Bool(true))` that ALWAYS FAILS — so a function
        // with a perfectly valid, provable contract reported two spurious failed
        // obligations. (The Ensures Postcondition emitted here is later replaced
        // by the body-aware one in `generate_v2_contract_vcs_impl`; the Requires
        // becomes a trivially-discharged Precondition.)
        let body = contract.body.strip_prefix(LOWERED_CONTRACT_PREFIX).unwrap_or(&contract.body);
        let Some(parsed) = parse_spec_expr(body) else {
            // An UNPARSEABLE `#[ensures]` (e.g. a raw spec closure whose
            // `matches!` never got compiler-lowered) routes to the
            // NON-REFUTABLE Unknown shape: the encoding cannot read the
            // predicate, so refuting it would mint a counterexample for a
            // formula unrelated to the contract. Never dropped (that would be
            // a false-PROVE), never Proved (`Bool(true)` is SAT). Other
            // contract kinds use the same non-refutable unsupported convention.
            if matches!(kind, VcKind::Postcondition) {
                vcs.push(spec_ensures_unparseable_vc(func, contract.span.clone(), body));
            } else {
                vcs.push(spec_failure_vc(func, contract, "unparseable contract"));
            }
            continue;
        };

        // Ordinary source contracts parse integer expressions into mathematical
        // `Int`, while their Rust operands have fixed-width machine semantics.
        // Accepting arithmetic in that reading gives one predicate two
        // meanings: e.g. `result + 1 > result` is an `Int` tautology but false
        // for `u8::MAX`. An `ensures` clause the Machine{w} lane admits
        // (`machine_faithful_clause_admissible` — one shared declared width,
        // wrap-exact fragment) proceeds: the placeholder emitted below is
        // REPLACED by the body-aware per-Return VCs, which
        // `generate_v2_contract_vcs_impl` translates wholesale into
        // declared-width QF_BV (the ratified type-directed reading) before
        // anything can solve the `Int` spelling. Every other arithmetic clause
        // remains a visible fail-closed Unknown.
        if formula_uses_unmodeled_machine_arithmetic_in_function(func, &parsed) {
            let machine_admitted = matches!(kind, VcKind::Postcondition)
                && machine_faithful_clause_admissible(func, &parsed);
            if !machine_admitted {
                vcs.push(spec_failure_vc(
                    func,
                    contract,
                    "contract uses unmodeled fixed-width machine arithmetic",
                ));
                continue;
            }
        }

        // SOUNDNESS (ny selfcheck over-refutation): an `#[ensures]` whose parsed
        // predicate references synthetic spec-model terms (`{base}_discr` /
        // `{base}_value*` / `{base}_sign` / `.__trust_ok_i` — the lowered
        // `matches!(r, Ok(..) if ..)` / `is_ok` / `unwrap` / `is_positive`
        // idioms) is UNDER-CONSTRAINED: no lane grounds those names to MIR
        // facts, so `Not(parsed)` is satisfiable by havoc regardless of the
        // body and would be reported Failed with a minted counterexample that
        // is not a program trace. Route it to the fail-closed NON-REFUTABLE
        // Unknown shape instead (never Failed-with-spurious-cex, never Proved).
        if matches!(kind, VcKind::Postcondition) {
            let ungrounded = ungrounded_spec_model_vars(&parsed);
            if !ungrounded.is_empty() {
                vcs.push(spec_model_ungrounded_vc(
                    func,
                    contract.span.clone(),
                    body,
                    &ungrounded,
                    None,
                ));
                continue;
            }
        }

        // Trust: At the function's *definition* site, a Requires contract
        // is an assumption to be used as a hypothesis on other VCs (the
        // pipeline conjoins `func.preconditions` onto safety/postcondition
        // VCs). It is *not* an obligation to be proved here — that is the
        // caller's burden, generated at call sites by `modular.rs`. We
        // still emit one Precondition VC per Requires clause for tooling
        // that counts/reports them, but its formula is trivially UNSAT so
        // the verifier discharges it without forcing the precondition to
        // be a tautology over its free variables.
        //
        // Postcondition/Assertion VCs remain meaningful obligations.
        let formula = if matches!(kind, VcKind::Precondition { .. }) {
            Formula::Bool(false)
        } else {
            Formula::Not(Box::new(parsed))
        };

        vcs.push(VerificationCondition {
            kind,
            function: func.name.as_str().into(),
            location: contract.span.clone(),
            formula,
            // Definition-site `Requires` rows are bookkeeping assumptions, not
            // caller obligations.  Carry the exact dense source-clause index so
            // downstream code can re-generate and validate this origin instead
            // of guessing from `callee == function` (which also holds for a
            // recursive self-call).  Other ordinary clauses keep their prior
            // metadata shape; their body-aware rows attach source identity in
            // the dedicated generation paths below.
            contract_metadata: matches!(contract.kind, ContractKind::Requires).then(|| {
                ContractMetadata {
                    source_contract_index: Some(contract_index),
                    ..ContractMetadata::default()
                }
            }),
        });
    }
}

/// Build a fail-closed placeholder VC for a contract whose body could not be
/// parsed, or whose `ContractKind` is not yet handled. This is an encoding gap,
/// not evidence that the program violates the authored predicate, so it uses
/// the non-refutable `UnsupportedMir` shape and is preclassified `Unknown`.
///
/// An unparseable or unhandled spec must never be silently
/// dropped. Dropping it leaves the function with fewer obligations than its
/// source declares and lets it aggregate to `proved` without the spec ever
/// being checked — a false-PROVE.
fn spec_failure_vc(
    func: &VerifiableFunction,
    contract: &Contract,
    detail: &str,
) -> VerificationCondition {
    spec_unverifiable_vc(func, contract.span.clone(), detail, &contract.body, None)
}

/// Build the canonical non-refutable row for an unelaborated source spec.
pub(crate) fn spec_unverifiable_vc(
    func: &VerifiableFunction,
    span: SourceSpan,
    detail: &str,
    body: &str,
    contract_metadata: Option<ContractMetadata>,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: SPEC_UNVERIFIABLE_KIND.to_string(),
            detail: format!("unverifiable source specification ({detail}): {body}"),
        },
        function: func.name.as_str().into(),
        location: span,
        // Direct solver callers must not be able to report proof either.
        formula: Formula::Bool(true),
        contract_metadata,
    }
}

/// Return a visible fail-closed row when a functional-induction adapter would
/// otherwise consume a raw postcondition containing fixed-width arithmetic.
///
/// These adapters currently reason in mathematical `Int`. Reusing a source
/// `u8`/`usize`/signed arithmetic formula there would silently change wrapping
/// or panic semantics. A canonical `UnsupportedMir` VC keeps the gap in the
/// report and is intentionally non-provable even for direct solver callers.
pub(crate) fn functional_lane_unmodeled_postcondition_vc(
    func: &VerifiableFunction,
    lane: &str,
) -> Option<VerificationCondition> {
    let (index, postcondition) = func.postconditions.iter().enumerate().find(|(_, formula)| {
        formula_uses_unmodeled_machine_arithmetic_in_function(func, formula)
    })?;
    let detail = format!(
        "{lane} postcondition #{index} has lowering `unsupported_machine_arithmetic`; fixed-width source arithmetic cannot be consumed by the mathematical-integer induction adapter"
    );
    let body = format!("{postcondition:?}");
    Some(spec_unverifiable_vc(func, func.span.clone(), &detail, &body, None))
}

fn loop_contract_unsupported_vc(
    func: &VerifiableFunction,
    contract: &Contract,
    detail: impl Into<String>,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: LOOP_CONTRACT_UNSUPPORTED_KIND.to_string(),
            detail: detail.into(),
        },
        function: func.name.as_str().into(),
        location: contract.span.clone(),
        // Direct solver callers must not be able to prove the placeholder.
        formula: Formula::Bool(true),
        contract_metadata: Some(trust_wp_metadata()),
    }
}

fn generate_loop_invariant_vcs(
    func: &VerifiableFunction,
    contract_index: usize,
    contract: &Contract,
    header_block: usize,
    expr: String,
    vcs: &mut Vec<VerificationCondition>,
) {
    let Some(parsed) = parse_spec_expr(&expr) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!("unparseable loop invariant `{expr}`"),
        ));
        return;
    };
    let Some(invariant) = type_and_validate_loop_formula(func, parsed, Sort::Bool) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!("loop invariant `{expr}` references an unsupported or ambiguous MIR value"),
        ));
        return;
    };
    // Retype every assumption through the same environment as the invariant.
    // In particular, a source `xs[i]` precondition and an E4 `xs[i]`
    // invariant must denote the same canonical read-only sequence term.  Keeping
    // a parser-default Int-sorted `xs` in one side would either make the query
    // ill-sorted or, worse, leave the authored precondition disconnected from
    // the invariant it is meant to establish.
    let Some(typed_preconditions) = func
        .preconditions
        .iter()
        .cloned()
        .map(|precondition| type_loop_formula(func, precondition, Sort::Bool))
        .collect::<Option<Vec<_>>>()
    else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop invariant `{expr}` depends on a function precondition that cannot be rebound to the exact MIR/source state"
            ),
        ));
        return;
    };
    if typed_preconditions
        .iter()
        .any(|pre| formula_uses_unmodeled_machine_arithmetic_in_function(func, pre))
    {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop invariant `{expr}` depends on a function precondition with unmodeled machine arithmetic"
            ),
        ));
        return;
    }
    let header = BlockId(header_block);
    let Some(entry_state) = symbolic_state_at_loop_entry(func, header) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop invariant `{expr}` is outside the exact straight-line entry fragment at bb{header_block}"
            ),
        ));
        return;
    };
    let Some((post_state, guard)) = symbolic_single_path_loop_transition(func, header) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop invariant `{expr}` is outside the exact single-path loop-transition fragment at bb{header_block}"
            ),
        ));
        return;
    };

    let invariant_at_entry = substitute_formula_state(&invariant, &entry_state);
    let mut initiation = typed_preconditions;
    initiation.push(Formula::Not(Box::new(invariant_at_entry)));
    let initiation = conjunction(initiation);

    // The post-state is independently symbolically executed through one full
    // successful iteration.  This is deliberately NOT `P && !P`: a wrong
    // invariant whose body falsifies P leaves a satisfiable violation formula.
    let invariant_after = substitute_formula_state(&invariant, &post_state);
    let preservation =
        Formula::And(vec![invariant.clone(), guard, Formula::Not(Box::new(invariant_after))]);
    if !formula_has_sort(&initiation, Sort::Bool) || !formula_has_sort(&preservation, Sort::Bool) {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop invariant `{expr}` produced an ill-sorted symbolic transition at bb{header_block}"
            ),
        ));
        return;
    }
    vcs.push(VerificationCondition {
        kind: VcKind::LoopInvariantInitiation { invariant: expr.clone(), header_block },
        function: func.name.as_str().into(),
        location: contract.span.clone(),
        formula: initiation,
        contract_metadata: Some(trust_wp_metadata_for_source(contract_index)),
    });

    vcs.push(VerificationCondition {
        kind: VcKind::LoopInvariantConsecution { invariant: expr, header_block },
        function: func.name.as_str().into(),
        location: contract.span.clone(),
        formula: preservation,
        contract_metadata: Some(trust_wp_metadata_for_source(contract_index)),
    });
}

fn generate_loop_decreases_vc(
    func: &VerifiableFunction,
    contract_index: usize,
    contract: &Contract,
    header_block: usize,
    expr: String,
    feedback: &[LoopInvariantFeedbackCandidate],
    vcs: &mut Vec<VerificationCondition>,
) {
    let Some(parsed) = parse_spec_expr(&expr) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!("unparseable loop decreases measure `{expr}`"),
        ));
        return;
    };
    let Some(measure) = type_loop_formula(func, parsed, Sort::Int) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!("loop decreases measure `{expr}` references an unsupported MIR value"),
        ));
        return;
    };
    let header = BlockId(header_block);
    let Some((post_state, guard)) = symbolic_single_path_loop_transition(func, header) else {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop decreases measure `{expr}` is outside the exact single-path loop-transition fragment at bb{header_block}"
            ),
        ));
        return;
    };
    let after = substitute_formula_state(&measure, &post_state);
    if formula_uses_unmodeled_machine_arithmetic(&measure)
        && !guarded_unsigned_difference_is_exact(func, &measure, &after, &guard)
    {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop decreases measure `{expr}` uses machine arithmetic not justified by the taken-edge guard"
            ),
        ));
        return;
    }

    let mut assumptions = Vec::new();
    // Step (c): an authored invariant becomes a loop-head assumption only in
    // the explicit feedback mechanism. The compiler admits candidates to that
    // mechanism through a crate-private capability after proving BOTH E4
    // obligations; the default first pass supplies no candidates. Function
    // def-path + header + source span checks prevent loop/function leakage, and
    // de-duplication avoids changing the query for duplicate candidates.
    let current_function_digest =
        serde_json::to_string(func).ok().map(|payload| proof_gated_function_digest(&payload));
    for invariant in feedback.iter().filter(|invariant| {
        current_function_digest.as_ref() == Some(&invariant.function_digest)
            && invariant.function_name == func.name
            && invariant.function_def_path == func.def_path
            && invariant.header_block == header_block
            && func.contracts.iter().any(|candidate| {
                matches!(candidate.kind, ContractKind::LoopInvariant)
                    && candidate.span == invariant.source_span
                    && loop_contract_body(&candidate.body).is_some_and(|(header, text)| {
                        header == header_block && text == invariant.source_text
                    })
            })
    }) {
        if !assumptions.iter().any(|existing| existing == &invariant.predicate) {
            assumptions.push(invariant.predicate.clone());
        }
    }
    assumptions.push(guard);
    assumptions.push(Formula::Or(vec![
        Formula::Lt(Box::new(measure.clone()), Box::new(Formula::Int(0))),
        Formula::Ge(Box::new(after), Box::new(measure)),
    ]));
    let violation = conjunction(assumptions);
    if !formula_has_sort(&violation, Sort::Bool) {
        vcs.push(loop_contract_unsupported_vc(
            func,
            contract,
            format!(
                "loop decreases measure `{expr}` produced an ill-sorted symbolic transition at bb{header_block}"
            ),
        ));
        return;
    }
    vcs.push(VerificationCondition {
        kind: VcKind::NonTermination { context: "loop-decreases".to_string(), measure: expr },
        function: func.name.as_str().into(),
        location: contract.span.clone(),
        formula: violation,
        contract_metadata: Some(trust_wp_metadata_for_source(contract_index)),
    });
}

fn conjunction(mut formulas: Vec<Formula>) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(true),
        1 => formulas.pop().unwrap(),
        _ => Formula::And(formulas),
    }
}

fn type_and_validate_loop_formula(
    func: &VerifiableFunction,
    formula: Formula,
    expected_sort: Sort,
) -> Option<Formula> {
    let typed = type_loop_formula(func, formula, expected_sort)?;
    // E4 currently represents integer locals as mathematical Ints. Raw
    // comparisons over a machine value preserve their meaning, but authored
    // Int arithmetic does not preserve fixed-width overflow/wrap semantics.
    // Reject such clauses until this lane carries an exact BV encoding: e.g.
    // `x + 1 > x` is false for `u8::MAX` and must never become an E4 theorem.
    (!formula_uses_unmodeled_machine_arithmetic(&typed)).then_some(typed)
}

/// The deliberately narrow E4 collection model.
///
/// Only immutable shared-reference arguments to slices or fixed arrays of
/// scalar, Freeze elements enter this lane.  The one `base` Formula is used by
/// source `xs[i]`, symbolic MIR element reads, initiation, and consecution; the
/// one `length` Formula likewise joins source `xs.len()` to exact MIR `Len` (and
/// the exact slice `PtrMetadata` shape).  This is not the general array-theory
/// lane: mutable collections, local aliases/reseats, projected writes, and
/// collection-bearing calls remain an explicit `UserLoopContractUnsupported`
/// frontier.  Multi-path loops such as the full binary-search example remain
/// outside `symbolic_single_path_loop_transition` as well.
#[derive(Clone)]
struct ReadOnlyCollectionModel {
    local: usize,
    name: String,
    elem_sort: Sort,
    length: ReadOnlyCollectionLength,
}

#[derive(Clone)]
enum ReadOnlyCollectionLength {
    Slice,
    Fixed(u64),
}

impl ReadOnlyCollectionModel {
    fn array_sort(&self) -> Sort {
        Sort::Array(Box::new(Sort::Int), Box::new(self.elem_sort.clone()))
    }

    fn base_formula(&self) -> Formula {
        Formula::Var(self.name.clone(), self.array_sort())
    }

    fn length_name(&self) -> String {
        format!("{}_len", self.name)
    }

    fn length_formula(&self) -> Formula {
        match self.length {
            ReadOnlyCollectionLength::Slice => Formula::Var(self.length_name(), Sort::Int),
            ReadOnlyCollectionLength::Fixed(length) => Formula::Int(i128::from(length)),
        }
    }

    fn is_slice(&self) -> bool {
        matches!(self.length, ReadOnlyCollectionLength::Slice)
    }
}

fn read_only_collection_element_sort(ty: &Ty) -> Option<Sort> {
    // These are scalar + Freeze in Rust.  Floats/bitvectors and aggregate or
    // interior-mutable element types stay outside this first exact lane.
    match ty {
        Ty::Bool => Some(Sort::Bool),
        Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char => Some(Sort::Int),
        _ => None,
    }
}

fn body_locals_have_canonical_positions(func: &VerifiableFunction) -> bool {
    // Every MIR `Place.local` is a positional local index.  The public TrustIr
    // model also retains `LocalDecl.index`, and `place_to_var_name` now resolves
    // a unique explicit index. But the symbolic transition and type lookups
    // still perform direct positional `.get(Place.local)` operations. Accepting
    // a sparse or reordered hand-built body would therefore let those two
    // authorities disagree. Rustc extraction emits this dense invariant; fail
    // closed when a public caller does not, rather than binding an E4 source
    // name to a different local.
    func.body.locals.iter().enumerate().all(|(position, decl)| decl.index == position)
}

fn read_only_collection_shape_for_local(
    func: &VerifiableFunction,
    local: usize,
) -> Option<ReadOnlyCollectionModel> {
    if !body_locals_have_canonical_positions(func) || local == 0 || local > func.body.arg_count {
        return None;
    }
    let decl = func.body.locals.get(local)?;
    let Ty::Ref { mutable: false, inner } = &decl.ty else {
        return None;
    };
    let (elem, length) = match inner.as_ref() {
        Ty::Slice { elem } => (elem.as_ref(), ReadOnlyCollectionLength::Slice),
        Ty::Array { elem, len } => (elem.as_ref(), ReadOnlyCollectionLength::Fixed(*len)),
        _ => return None,
    };
    let elem_sort = read_only_collection_element_sort(elem)?;
    let name = crate::place_to_var_name(func, &trust_types::Place::local(local));
    Some(ReadOnlyCollectionModel { local, name, elem_sort, length })
}

fn operand_place(operand: &Operand) -> Option<&trust_types::Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

fn operand_mentions_local(operand: &Operand, local: usize) -> bool {
    operand_place(operand).is_some_and(|place| place.local == local)
}

fn read_only_collection_index_projection<'a>(
    place: &'a trust_types::Place,
    local: usize,
) -> Option<&'a Projection> {
    if place.local != local || place.projections.len() != 2 {
        return None;
    }
    if !matches!(place.projections.first(), Some(Projection::Deref)) {
        return None;
    }
    match place.projections.get(1)? {
        index @ Projection::Index(_) => Some(index),
        index @ Projection::ConstantIndex { from_end: false, .. } => Some(index),
        _ => None,
    }
}

fn operand_uses_collection_only_as_element_read(
    func: &VerifiableFunction,
    operand: &Operand,
    local: usize,
) -> bool {
    if !operand_mentions_local(operand, local) {
        return true;
    }
    // A scalar element behind an immutable shared reference is read with Copy
    // in valid rustc MIR.  Do not give a fabricated Move-out-of-borrow the same
    // semantics at the public TrustIr boundary.
    let Operand::Copy(place) = operand else { return false };
    match read_only_collection_index_projection(place, local) {
        Some(Projection::Index(index_local)) => {
            func.body.locals.get(*index_local).is_some_and(|decl| {
                decl.index == *index_local
                    && matches!(decl.ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
            })
        }
        Some(Projection::ConstantIndex { from_end: false, .. }) => true,
        _ => false,
    }
}

fn exact_read_only_collection_len_place(place: &trust_types::Place, local: usize) -> bool {
    place.local == local && place.projections.as_slice() == [Projection::Deref]
}

fn exact_read_only_collection_metadata_operand(
    func: &VerifiableFunction,
    operand: &Operand,
    local: usize,
) -> bool {
    let Some(model) = read_only_collection_shape_for_local(func, local) else {
        return false;
    };
    model.is_slice()
        && matches!(operand, Operand::Copy(place) if place.local == local && place.projections.is_empty())
}

/// Recognize rustc's exact `&[T; N] -> &[T]` unsizing rvalue.
///
/// TrustIr intentionally erases the rustc cast-kind enum, so this gate relies
/// only on a coercion that Rust's type system permits with these exact source
/// and target types.  The caller must additionally prove the resulting slice
/// view is consumed only by the adjacent `PtrMetadata` statement; otherwise it
/// would be a retained collection alias outside the bounded E4 model.
fn fixed_array_slice_view_cast_model(
    func: &VerifiableFunction,
    operand: &Operand,
    target_ty: &Ty,
    require_stable_source: bool,
) -> Option<ReadOnlyCollectionModel> {
    let Operand::Copy(source) = operand else { return None };
    if !source.projections.is_empty() {
        return None;
    }
    let model = if require_stable_source {
        read_only_collection_model_for_local(func, source.local)?
    } else {
        read_only_collection_shape_for_local(func, source.local)?
    };
    if !matches!(&model.length, ReadOnlyCollectionLength::Fixed(_)) {
        return None;
    }
    let source_decl = func.body.locals.get(source.local)?;
    let Ty::Ref { mutable: false, inner: source_inner } = &source_decl.ty else {
        return None;
    };
    let Ty::Array { elem: source_elem, .. } = source_inner.as_ref() else {
        return None;
    };
    let Ty::Ref { mutable: false, inner: target_inner } = target_ty else {
        return None;
    };
    let Ty::Slice { elem: target_elem } = target_inner.as_ref() else {
        return None;
    };
    (source_elem == target_elem).then_some(model)
}

fn place_mentions_local_anywhere(place: &trust_types::Place, local: usize) -> bool {
    place.local == local
        || place
            .projections
            .iter()
            .any(|projection| matches!(projection, Projection::Index(index) if *index == local))
}

fn operand_mentions_local_anywhere(operand: &Operand, local: usize) -> bool {
    operand_place(operand).is_some_and(|place| place_mentions_local_anywhere(place, local))
}

fn rvalue_mentions_local_anywhere(rvalue: &Rvalue, local: usize) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => operand_mentions_local_anywhere(operand, local),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_mentions_local_anywhere(lhs, local)
                || operand_mentions_local_anywhere(rhs, local)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_mentions_local_anywhere(place, local),
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|operand| operand_mentions_local_anywhere(operand, local))
        }
        // A future rvalue has not been audited for retained-local uses.
        _ => true,
    }
}

fn statement_mentions_local_anywhere(statement: &Statement, local: usize) -> bool {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            place_mentions_local_anywhere(place, local)
                || rvalue_mentions_local_anywhere(rvalue, local)
        }
        Statement::StorageLive(index) | Statement::StorageDead(index) => *index == local,
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => place_mentions_local_anywhere(place, local),
        Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
            args.iter().any(|operand| operand_mentions_local_anywhere(operand, local))
        }
        Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => false,
        // A future statement has not been audited for retained-local uses.
        _ => true,
    }
}

fn terminator_mentions_local_anywhere(terminator: &Terminator, local: usize) -> bool {
    match terminator {
        Terminator::SwitchInt { discr, .. } => operand_mentions_local_anywhere(discr, local),
        Terminator::Call { args, dest, .. } => {
            place_mentions_local_anywhere(dest, local)
                || args.iter().any(|operand| operand_mentions_local_anywhere(operand, local))
        }
        Terminator::Assert { cond, .. } => operand_mentions_local_anywhere(cond, local),
        Terminator::Drop { place, .. } => place_mentions_local_anywhere(place, local),
        Terminator::Goto(_)
        | Terminator::Return
        | Terminator::Opaque { .. }
        | Terminator::Unreachable
        | Terminator::Resume => false,
        // A future terminator has not been audited for retained-local uses.
        _ => true,
    }
}

/// Verify the exact two-statement compiler shape used by `[T; N]::len()`:
///
/// ```text
/// view = Copy(array_ref) as &[T];
/// len  = PtrMetadata(Move(view));
/// ```
///
/// The temporary view must occur nowhere else in the function.  This makes the
/// admission an exact length observation, never authority for a retained alias.
fn exact_fixed_array_slice_metadata_pair(
    func: &VerifiableFunction,
    collection_local: usize,
    block_index: usize,
    statement_index: usize,
) -> bool {
    let Some(block) = func.body.blocks.get(block_index) else { return false };
    let Some(Statement::Assign { place: view, rvalue: Rvalue::Cast(source, target_ty), .. }) =
        block.stmts.get(statement_index)
    else {
        return false;
    };
    if !view.projections.is_empty()
        || view.local == collection_local
        || fixed_array_slice_view_cast_model(func, source, target_ty, false)
            .is_none_or(|model| model.local != collection_local)
        || func
            .body
            .locals
            .get(view.local)
            .is_none_or(|decl| decl.index != view.local || decl.ty != *target_ty)
    {
        return false;
    }
    let Some(Statement::Assign {
        place: len_dest,
        rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Move(metadata_view)),
        ..
    }) = block.stmts.get(statement_index + 1)
    else {
        return false;
    };
    if len_dest.local == view.local
        || !len_dest.projections.is_empty()
        || metadata_view.local != view.local
        || !metadata_view.projections.is_empty()
        || func.body.locals.get(len_dest.local).is_none_or(|decl| {
            decl.index != len_dest.local
                || !matches!(
                    decl.ty,
                    Ty::PtrSizedInt { signed: false, .. } | Ty::Int { signed: false, .. }
                )
        })
    {
        return false;
    }

    for (candidate_block, body) in func.body.blocks.iter().enumerate() {
        for (candidate_statement, statement) in body.stmts.iter().enumerate() {
            if candidate_block == block_index
                && (candidate_statement == statement_index
                    || candidate_statement == statement_index + 1)
            {
                continue;
            }
            if statement_mentions_local_anywhere(statement, view.local) {
                return false;
            }
        }
        if terminator_mentions_local_anywhere(&body.terminator, view.local) {
            return false;
        }
    }
    true
}

fn rvalue_preserves_read_only_collection(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    local: usize,
) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_uses_collection_only_as_element_read(func, operand, local),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_uses_collection_only_as_element_read(func, lhs, local)
                && operand_uses_collection_only_as_element_read(func, rhs, local)
        }
        Rvalue::UnaryOp(UnOp::PtrMetadata, operand) if operand_mentions_local(operand, local) => {
            exact_read_only_collection_metadata_operand(func, operand, local)
        }
        Rvalue::UnaryOp(_, operand) | Rvalue::Cast(operand, _) | Rvalue::Repeat(operand, _) => {
            operand_uses_collection_only_as_element_read(func, operand, local)
        }
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .all(|operand| operand_uses_collection_only_as_element_read(func, operand, local)),
        Rvalue::Len(place) if place.local == local => {
            exact_read_only_collection_len_place(place, local)
        }
        Rvalue::Len(_) => true,
        Rvalue::Discriminant(place) => place.local != local,
        Rvalue::CopyForDeref(place) => {
            operand_uses_collection_only_as_element_read(func, &Operand::Copy(place.clone()), local)
        }
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => place.local != local,
        // An explicitly unsupported rvalue has not been audited for hidden
        // alias/write effects, even when its retained operand list looks
        // unrelated to this collection.
        Rvalue::Unsupported { .. } => false,
        // `Rvalue` is non-exhaustive across the crate boundary. A future shape
        // has not been audited for aliasing and therefore disables this lane.
        _ => false,
    }
}

fn read_only_collection_arg_is_stable(func: &VerifiableFunction, local: usize) -> bool {
    for (block_index, block) in func.body.blocks.iter().enumerate() {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Statement::Assign { place, rvalue, .. } => {
                    // Any whole-local reseat or projected write changes the source
                    // value denoted by the canonical base and is rejected.
                    if place.local == local {
                        return false;
                    }
                    // rustc lowers `&[T; N]::len()` through one ephemeral
                    // array-to-slice view followed immediately by PtrMetadata.
                    // Admit only that exact pair; the recognizer proves the view
                    // local has no retained/escaping use anywhere else.
                    if exact_fixed_array_slice_metadata_pair(
                        func,
                        local,
                        block_index,
                        statement_index,
                    ) {
                        continue;
                    }
                    if !rvalue_preserves_read_only_collection(func, rvalue, local) {
                        return false;
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if place.local == local =>
                {
                    return false;
                }
                Statement::Intrinsic { args, .. }
                    if args.iter().any(|operand| operand_mentions_local(operand, local)) =>
                {
                    return false;
                }
                Statement::Unsupported { .. } => return false,
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Intrinsic { .. }
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // Future statement shapes have not been audited for hidden writes.
                _ => return false,
            }
        }
        match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                // Passing the modeled sequence across a call would require an
                // interprocedural Freeze/alias proof; this narrow lane has none.
                if dest.local == local
                    || args.iter().any(|operand| operand_mentions_local(operand, local))
                {
                    return false;
                }
            }
            Terminator::SwitchInt { discr, .. }
                if !operand_uses_collection_only_as_element_read(func, discr, local) =>
            {
                return false;
            }
            Terminator::Assert { cond, .. }
                if !operand_uses_collection_only_as_element_read(func, cond, local) =>
            {
                return false;
            }
            Terminator::Drop { place, .. } if place.local == local => return false,
            Terminator::Opaque { .. } => return false,
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Drop { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            // Future terminators have not been audited for hidden calls/writes.
            _ => return false,
        }
    }
    true
}

fn read_only_collection_model_for_local(
    func: &VerifiableFunction,
    local: usize,
) -> Option<ReadOnlyCollectionModel> {
    let model = read_only_collection_shape_for_local(func, local)?;
    read_only_collection_arg_is_stable(func, local).then_some(model)
}

fn read_only_collection_model_for_name(
    func: &VerifiableFunction,
    name: &str,
) -> Option<ReadOnlyCollectionModel> {
    let mut matches = func.body.locals.iter().filter_map(|decl| {
        let model = read_only_collection_model_for_local(func, decl.index)?;
        (model.name == name).then_some(model)
    });
    let model = matches.next()?;
    matches.next().is_none().then_some(model)
}

/// Rebind the executable spec parser's canonical literal-index place spelling
/// (`xs[0]`) to the same array `Select` used by symbolic MIR element reads.
///
/// The general parser deliberately retains literal stable-place projections as
/// one injective variable name for non-collection lanes. E4 may reinterpret
/// only one exact, canonical nonnegative decimal suffix whose base is already a
/// unique, stable [`ReadOnlyCollectionModel`]. Nested/projected names, alternate
/// digit spellings, and unknown bases stay unbound and therefore fail closed.
fn read_only_collection_literal_index_for_name(
    func: &VerifiableFunction,
    name: &str,
) -> Option<Formula> {
    let without_close = name.strip_suffix(']')?;
    let (base, index_text) = without_close.rsplit_once('[')?;
    if base.is_empty()
        || base.contains('[')
        || base.contains(']')
        || index_text.is_empty()
        || !index_text.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let index = index_text.parse::<i128>().ok()?;
    if index.to_string() != index_text {
        return None;
    }
    let model = read_only_collection_model_for_name(func, base)?;
    Some(Formula::Select(Box::new(model.base_formula()), Box::new(Formula::Int(index))))
}

fn type_loop_formula(
    func: &VerifiableFunction,
    formula: Formula,
    expected_sort: Sort,
) -> Option<Formula> {
    // `Place.local` and `LocalDecl.index` must identify the same declaration
    // before either source rebinding or symbolic state construction is sound.
    if !body_locals_have_canonical_positions(func) {
        return None;
    }
    let mut replacements = FxHashMap::default();
    for name in formula.free_variables() {
        if let Some(model) = read_only_collection_model_for_name(func, &name) {
            replacements.insert(name, model.base_formula());
            continue;
        }
        if let Some(element) = read_only_collection_literal_index_for_name(func, &name) {
            replacements.insert(name, element);
            continue;
        }
        // Extraction canonicalizes an admitted source `xs.len()` precondition
        // to the same `xs__slice_len` leaf used by bounds VCs and modular σ
        // summaries. E4 has one narrower symbolic collection model whose length
        // term is `model.length_formula()`; bind the canonical leaf to that same
        // term just as source loop clauses' `xs_len` projection leaf is bound
        // below. Neither spelling remains an independent free variable here.
        if let Some(base) = name.strip_suffix("__slice_len")
            && let Some(model) = read_only_collection_model_for_name(func, base)
        {
            replacements.insert(name, model.length_formula());
            continue;
        }
        if let Some(base) = name.strip_suffix("_len")
            && let Some(model) = read_only_collection_model_for_name(func, base)
        {
            replacements.insert(name, model.length_formula());
            continue;
        }
        let mut matches = func.body.locals.iter().filter(|decl| {
            crate::place_to_var_name(func, &trust_types::Place::local(decl.index)) == name
        });
        let decl = matches.next()?;
        if matches.next().is_some()
            || !matches!(decl.ty, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)
        {
            return None;
        }
        replacements.insert(name.clone(), Formula::Var(name, crate::sort_for_ty(&decl.ty)));
    }
    let typed = substitute_formula_state(&formula, &replacements);
    formula_has_sort(&typed, expected_sort).then_some(typed)
}

/// Whether a parsed source formula contains arithmetic whose mathematical-Int
/// encoding is not equivalent to fixed-width Rust/MIR evaluation.
///
/// This is deliberately binder-agnostic and recursive: quantified arithmetic
/// is no safer than free-variable arithmetic, and a future wrapper node must
/// not hide an `Add`/`Neg` from the gate.
pub(crate) fn formula_uses_unmodeled_machine_arithmetic(formula: &Formula) -> bool {
    // The parser represents a negative integer literal as `Neg(Int(n))`.
    // That is a constant, not a machine operation, and rejecting it drops
    // ordinary range facts such as `x >= -1000` before the BV bridge sees
    // them. Nested constant negations are equally literal-only.
    if formula_integer_literal(formula).is_some() {
        return false;
    }
    matches!(
        formula,
        Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(..)
    ) || formula.children().into_iter().any(formula_uses_unmodeled_machine_arithmetic)
}

/// Function-aware version of [`formula_uses_unmodeled_machine_arithmetic`].
///
/// A small source arithmetic fragment is exact when the function contract
/// itself excludes the sole fixed-width exceptional value. In particular,
/// signed `0 - x` agrees with mathematical subtraction whenever a declared
/// precondition proves `x > MIN`. This is the shape emitted for a guarded
/// `wrapping_neg` contract; retaining it restores the body-aware obligation
/// without admitting unchecked machine arithmetic generally.
pub(crate) fn formula_uses_unmodeled_machine_arithmetic_in_function(
    func: &VerifiableFunction,
    formula: &Formula,
) -> bool {
    if formula_integer_literal(formula).is_some()
        || zero_subtraction_is_exact_under_preconditions(func, formula)
    {
        return false;
    }
    matches!(
        formula,
        Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(..)
    ) || formula
        .children()
        .into_iter()
        .any(|child| formula_uses_unmodeled_machine_arithmetic_in_function(func, child))
}

fn formula_integer_literal(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Int(value) => Some(*value),
        Formula::Neg(inner) => formula_integer_literal(inner)?.checked_neg(),
        _ => None,
    }
}

fn zero_subtraction_is_exact_under_preconditions(
    func: &VerifiableFunction,
    formula: &Formula,
) -> bool {
    let Formula::Sub(lhs, rhs) = formula else { return false };
    if formula_integer_literal(lhs) != Some(0) {
        return false;
    }
    let Formula::Var(name, _) = rhs.as_ref() else { return false };
    let Some(min) = signed_machine_local_min(func, name) else { return false };
    // Authorization must come from a precondition that independently survives
    // the context-free arithmetic filter. Calling the function-aware classifier
    // here would recurse through this same `0 - x` exception; inspecting only
    // independently exact predicates both avoids that cycle and prevents a
    // useful bound hidden inside an otherwise-unsafe conjunction from leaking
    // into the sanitized function view.
    func.preconditions.iter().any(|pre| {
        !formula_uses_unmodeled_machine_arithmetic(pre) && formula_establishes_above(pre, name, min)
    })
}

fn signed_machine_local_min(func: &VerifiableFunction, name: &str) -> Option<i128> {
    let mut matches = func.body.locals.iter().filter(|decl| {
        decl.name.as_deref() == Some(name)
            || crate::place_to_var_name(func, &trust_types::Place::local(decl.index)) == name
            || (decl.index == 0 && name == "_0")
    });
    let decl = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let Ty::Int { width, signed: true } = decl.ty else { return None };
    match width {
        1..=127 => Some(-(1_i128 << (width - 1))),
        128 => Some(i128::MIN),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Machine{w} declared-width elaboration of arithmetic-bearing contracts.
//
// Ratified L1 rule 4 (two-language spec surface §L1): the arithmetic domain of
// a spec expression is TYPE-DIRECTED — a machine-typed operand (`u64`, `i32`,
// …) gets Machine{w} wrapping-bitvector semantics at its DECLARED width and
// signedness, never unbounded `Int`. Reading `result + 1 > result` over `Int`
// is the confirmed false-proof vector (true over `Int`, false at `u64::MAX`
// under the wrap); reading it over a WIDENED non-wrapping bitvector re-derives
// the same false positive. The only sound static reading is the declared
// width, where the clause is refutable at exactly the values Rust wraps.
//
// These helpers admit an arithmetic-bearing `ensures` clause into the
// refutable body-aware postcondition lane by translating the WHOLE assembled
// VC formula (negated clause + block defs + return pins + hypotheses) into
// pure QF_BV at the one declared width shared by every integer variable in
// the formula. Translating the whole formula, rather than bridging an
// `Int`-modeled body to a BV-modeled clause through `int2bv`, keeps the goal
// inside the theory ay decides and certifies.
//
// SOUNDNESS (no false PROVE): every value a REAL execution reaching `Return`
// carries is in its type's range, where the declared-width BV reading of a
// variable, literal, comparison (signedness-corrected), `+`/`-`/`*` (exact
// when the executed checked op did not trap — and a trapping execution never
// reaches `Return`), and truncating `/`/`%` (bvsdiv/bvudiv match Rust `/`
// exactly; a zero divisor traps and never reaches `Return`) agrees exactly
// with the executed machine value. So every real violating state stays SAT
// and a real proof stays a proof: UNSAT over the BV model ⇒ no real trace
// violates the clause. The BV model may ADMIT wrap states no checked
// execution reaches (the model does not carry the checked-op trap
// obligations); those states can only ADD satisfying assignments — at worst a
// fail-closed spurious refutation, never a false proof. This is the same
// one-sided tolerance the widened transport lane documents
// (`try_widen_unsigned_relational_vc_to_bv`), at the OPPOSITE width choice:
// that lane widens so execution-domain arithmetic never wraps, which is
// exactly the reading a SPEC-domain clause must never get.
// ---------------------------------------------------------------------------

/// Resolve a formula variable name to the machine-integer `(width, signed)` of
/// the local (or checked-op tuple field) it denotes, `None` for every other
/// shape. Handles the postcondition lane's naming conventions: SSA version
/// tokens (`x#s1_0`), the return slot (`_0`), raw local names (`_3`), source
/// names, and single tuple-field projections (`_3.0`, the checked-op value).
fn machine_int_ty_for_var(func: &VerifiableFunction, name: &str) -> Option<(u32, bool)> {
    // Version tokens never change a variable's type; match on the base name.
    let base = name.split('#').next().unwrap_or(name);
    let (local_part, field) = match base.split_once('.') {
        Some((local_part, field)) => (local_part, Some(field.parse::<usize>().ok()?)),
        None => (base, None),
    };
    let mut matches = func.body.locals.iter().filter(|decl| {
        decl.name.as_deref() == Some(local_part)
            || crate::place_to_var_name(func, &trust_types::Place::local(decl.index)) == local_part
            || format!("_{}", decl.index) == local_part
    });
    let decl = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let ty = match field {
        None => &decl.ty,
        Some(index) => match &decl.ty {
            Ty::Tuple(fields) => fields.get(index)?,
            _ => return None,
        },
    };
    match ty {
        Ty::Int { width, signed } => Some((*width, *signed)),
        Ty::PtrSizedInt { signed } => Some((64, *signed)),
        _ => None,
    }
}

/// Whether the local (or tuple field) behind a variable name is `Bool`-typed.
fn var_is_bool_local(func: &VerifiableFunction, name: &str) -> bool {
    let base = name.split('#').next().unwrap_or(name);
    let (local_part, field) = match base.split_once('.') {
        Some((local_part, field)) => match field.parse::<usize>() {
            Ok(index) => (local_part, Some(index)),
            Err(_) => return false,
        },
        None => (base, None),
    };
    let mut matches = func.body.locals.iter().filter(|decl| {
        decl.name.as_deref() == Some(local_part)
            || crate::place_to_var_name(func, &trust_types::Place::local(decl.index)) == local_part
            || format!("_{}", decl.index) == local_part
    });
    let Some(decl) = matches.next() else { return false };
    if matches.next().is_some() {
        return false;
    }
    match field {
        None => matches!(decl.ty, Ty::Bool),
        Some(index) => matches!(&decl.ty, Ty::Tuple(fields)
            if matches!(fields.get(index), Some(Ty::Bool))),
    }
}

/// Whether an authored arithmetic-bearing clause is eligible for the
/// Machine{w} lane: every integer variable resolves to ONE shared
/// `(width, signed)` machine domain, every literal fits that domain, and the
/// clause stays inside the wrap-exact fragment (`+`/`-`/`*`/unary `-`,
/// comparisons, equality, boolean connectives). Spec-level `/`/`%` are
/// refused: SMT's total bvudiv/bvsdiv assign a zero divisor a value where the
/// authored Rust expression traps, so such a clause keeps its visible
/// `unsupported_machine_arithmetic` row until a definedness premise lane
/// lands. This predicate gates ADMISSION only; it grants nothing — the final
/// VC still has to translate (`machine_faithful_vc_formula`) and prove.
pub(crate) fn machine_faithful_clause_admissible(
    func: &VerifiableFunction,
    formula: &Formula,
) -> bool {
    let Some((width, signed)) = uniform_machine_domain(func, formula) else {
        return false;
    };
    clause_in_machine_fragment(func, formula, width, signed, /* allow_div_rem */ false)
}

/// The single `(width, signed)` machine domain shared by every integer
/// variable in the formula, `None` when any integer variable is unresolvable
/// or two variables disagree. Bool-typed variables and literals do not
/// constrain the domain.
fn uniform_machine_domain(func: &VerifiableFunction, formula: &Formula) -> Option<(u32, bool)> {
    let mut domain: Option<(u32, bool)> = None;
    let mut consistent = true;
    formula.visit(&mut |node| {
        let name = match node {
            Formula::Var(name, sort) => match sort {
                Sort::Bool => return,
                _ => name.as_str(),
            },
            Formula::SymVar(sym, sort) => match sort {
                Sort::Bool => return,
                _ => sym.as_str(),
            },
            _ => return,
        };
        if var_is_bool_local(func, name) {
            return;
        }
        match machine_int_ty_for_var(func, name) {
            Some(var_domain) => match domain {
                None => domain = Some(var_domain),
                Some(existing) if existing == var_domain => {}
                Some(_) => consistent = false,
            },
            None => consistent = false,
        }
    });
    if !consistent {
        return None;
    }
    domain
}

/// Whether every node of `formula` lowers into the declared-width machine
/// fragment. Mirrors `machine_faithful_vc_formula`'s coverage so admission
/// and translation can never disagree on the CLAUSE; the body-def side may
/// additionally carry `/`/`%` (`allow_div_rem`), which are wrap-exact for the
/// executions that reach `Return`.
fn clause_in_machine_fragment(
    func: &VerifiableFunction,
    formula: &Formula,
    width: u32,
    signed: bool,
    allow_div_rem: bool,
) -> bool {
    machine_faithful_translate(func, formula, width, signed, allow_div_rem, Polarity::Prop)
        .is_some()
}

/// Expected sort of a node during machine translation.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    /// The node must produce a proposition (`Bool`).
    Prop,
    /// The node must produce a `width`-bit machine value.
    Value,
}

/// The literal's `width`-bit two's-complement pattern, `None` when the value
/// does not fit the declared domain. The pattern is stored non-negative so the
/// downstream bridges (`Expr::bitvec_const`, `to_smtlib`) never see a sign.
fn machine_literal_pattern(value: i128, width: u32, signed: bool) -> Option<i128> {
    if width == 0 || width > 128 {
        return None;
    }
    if signed {
        let min = if width == 128 { i128::MIN } else { -(1_i128 << (width - 1)) };
        let max = if width == 128 { i128::MAX } else { (1_i128 << (width - 1)) - 1 };
        if value < min || value > max {
            return None;
        }
    } else {
        if value < 0 {
            return None;
        }
        if width < 128 && u128::try_from(value).ok()? >= (1_u128 << width) {
            return None;
        }
    }
    if value >= 0 {
        return Some(value);
    }
    // Two's complement of a negative in-range value; width < 128 here because
    // an i128::MIN pattern would not fit the non-negative i128 carrier.
    if width == 128 {
        return None;
    }
    Some(value + (1_i128 << width))
}

/// Translate a formula into pure declared-width QF_BV, `None` on any node
/// outside the machine fragment. Integer variables keep their NAMES (so the
/// translated goal stays aligned with the row's identity and diagnostics) but
/// are re-sorted `BitVec(width)`; comparisons pick the signed or unsigned BV
/// operator from the shared domain; `+`/`-`/`*` wrap at the declared width —
/// the ratified Machine{w} reading.
fn machine_faithful_translate(
    func: &VerifiableFunction,
    formula: &Formula,
    width: u32,
    signed: bool,
    allow_div_rem: bool,
    polarity: Polarity,
) -> Option<Formula> {
    let value =
        |f: &Formula| machine_faithful_translate(func, f, width, signed, allow_div_rem, Polarity::Value);
    let prop =
        |f: &Formula| machine_faithful_translate(func, f, width, signed, allow_div_rem, Polarity::Prop);
    let value_pair = |a: &Formula, b: &Formula| -> Option<(Box<Formula>, Box<Formula>)> {
        Some((Box::new(value(a)?), Box::new(value(b)?)))
    };
    // A comparison/equality operand is a proposition iff it is itself boolean
    // structure or names a Bool-typed local; otherwise it is a machine value.
    let operand_is_prop = |f: &Formula| -> bool {
        match f {
            Formula::Bool(_)
            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..) => true,
            Formula::Var(name, sort) => {
                matches!(sort, Sort::Bool) || var_is_bool_local(func, name)
            }
            Formula::SymVar(sym, sort) => {
                matches!(sort, Sort::Bool) || var_is_bool_local(func, sym.as_str())
            }
            _ => false,
        }
    };
    match polarity {
        Polarity::Prop => Some(match formula {
            Formula::Bool(b) => Formula::Bool(*b),
            Formula::Var(name, _) => {
                if !var_is_bool_local(func, name) {
                    return None;
                }
                Formula::Var(name.clone(), Sort::Bool)
            }
            Formula::SymVar(sym, _) => {
                if !var_is_bool_local(func, sym.as_str()) {
                    return None;
                }
                Formula::Var(sym.as_str().to_string(), Sort::Bool)
            }
            Formula::Not(a) => Formula::Not(Box::new(prop(a)?)),
            Formula::And(xs) => {
                Formula::And(xs.iter().map(prop).collect::<Option<Vec<_>>>()?)
            }
            Formula::Or(xs) => Formula::Or(xs.iter().map(prop).collect::<Option<Vec<_>>>()?),
            Formula::Implies(a, b) => Formula::Implies(Box::new(prop(a)?), Box::new(prop(b)?)),
            Formula::Eq(a, b) => {
                if operand_is_prop(a) || operand_is_prop(b) {
                    Formula::Eq(Box::new(prop(a)?), Box::new(prop(b)?))
                } else {
                    let (a, b) = value_pair(a, b)?;
                    Formula::Eq(a, b)
                }
            }
            Formula::Lt(a, b) => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSLt(a, b, width) } else { Formula::BvULt(a, b, width) }
            }
            Formula::Le(a, b) => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSLe(a, b, width) } else { Formula::BvULe(a, b, width) }
            }
            // `a > b` ⟺ `b < a`; `a >= b` ⟺ `b <= a`.
            Formula::Gt(a, b) => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSLt(b, a, width) } else { Formula::BvULt(b, a, width) }
            }
            Formula::Ge(a, b) => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSLe(b, a, width) } else { Formula::BvULe(b, a, width) }
            }
            _ => return None,
        }),
        Polarity::Value => Some(match formula {
            // The body encoder's wrapping bridge (`wrapping_machine_binop_to_formula`,
            // `binop_to_formula`) spells a machine result as
            // `BvToInt(op(IntToBv(a), IntToBv(b)))` — an Int-sorted read of the
            // wrapped pattern. In the pure declared-width reading both bridges
            // are the identity: `IntToBv` of an in-range value IS its pattern
            // and `BvToInt` reads that same pattern back (a bijection for every
            // value a real execution carries), so each folds away into its
            // operand's translation. Only the EXACT declared width/signedness
            // folds; any other width is a genuine domain change and refuses.
            Formula::IntToBv(inner, w) if *w == width => value(inner)?,
            Formula::BvToInt(inner, w, s) if *w == width && *s == signed => value(inner)?,
            Formula::BvAdd(a, b, w) if *w == width => {
                Formula::BvAdd(Box::new(value(a)?), Box::new(value(b)?), width)
            }
            Formula::BvSub(a, b, w) if *w == width => {
                Formula::BvSub(Box::new(value(a)?), Box::new(value(b)?), width)
            }
            Formula::BvMul(a, b, w) if *w == width => {
                Formula::BvMul(Box::new(value(a)?), Box::new(value(b)?), width)
            }
            Formula::BitVec { value, width: w } if *w == width => {
                Formula::BitVec { value: *value, width }
            }
            Formula::Var(name, Sort::BitVec(w)) if *w == width => {
                machine_int_ty_for_var(func, name).filter(|d| *d == (width, signed))?;
                Formula::Var(name.clone(), Sort::BitVec(width))
            }
            Formula::Var(name, _) => {
                machine_int_ty_for_var(func, name).filter(|d| *d == (width, signed))?;
                Formula::Var(name.clone(), Sort::BitVec(width))
            }
            Formula::SymVar(sym, _) => {
                machine_int_ty_for_var(func, sym.as_str()).filter(|d| *d == (width, signed))?;
                Formula::Var(sym.as_str().to_string(), Sort::BitVec(width))
            }
            Formula::Int(n) => Formula::BitVec {
                value: machine_literal_pattern(*n, width, signed)?,
                width,
            },
            Formula::UInt(n) => Formula::BitVec {
                value: machine_literal_pattern(i128::try_from(*n).ok()?, width, signed)?,
                width,
            },
            Formula::Add(a, b) => {
                let (a, b) = value_pair(a, b)?;
                Formula::BvAdd(a, b, width)
            }
            Formula::Sub(a, b) => {
                let (a, b) = value_pair(a, b)?;
                Formula::BvSub(a, b, width)
            }
            Formula::Mul(a, b) => {
                let (a, b) = value_pair(a, b)?;
                Formula::BvMul(a, b, width)
            }
            // Two's-complement negation: `0 - x` at the declared width.
            Formula::Neg(a) => Formula::BvSub(
                Box::new(Formula::BitVec { value: 0, width }),
                Box::new(value(a)?),
                width,
            ),
            Formula::Div(a, b) if allow_div_rem => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSDiv(a, b, width) } else { Formula::BvUDiv(a, b, width) }
            }
            Formula::Rem(a, b) if allow_div_rem => {
                let (a, b) = value_pair(a, b)?;
                if signed { Formula::BvSRem(a, b, width) } else { Formula::BvURem(a, b, width) }
            }
            _ => return None,
        }),
    }
}

/// Translate the fully assembled body-aware postcondition VC of a
/// Machine{w}-admitted clause into pure declared-width QF_BV. `None` (the
/// caller emits the visible fail-closed row) when any conjunct steps outside
/// the fragment — mixed integer widths in the body, collection/float/pointer
/// facts, quantifiers. Body-def `/`/`%` are allowed (wrap-exact on every
/// execution that reaches `Return`); the CLAUSE was already admitted without
/// them.
pub(crate) fn machine_faithful_vc_formula(
    func: &VerifiableFunction,
    formula: &Formula,
) -> Option<Formula> {
    let (width, signed) = uniform_machine_domain(func, formula)?;
    machine_faithful_translate(func, formula, width, signed, true, Polarity::Prop)
}

fn formula_establishes_above(formula: &Formula, name: &str, minimum: i128) -> bool {
    let is_name =
        |formula: &Formula| matches!(formula, Formula::Var(candidate, _) if candidate == name);
    match formula {
        Formula::Gt(lhs, rhs) if is_name(lhs) => {
            formula_integer_literal(rhs).is_some_and(|bound| bound >= minimum)
        }
        Formula::Ge(lhs, rhs) if is_name(lhs) => {
            formula_integer_literal(rhs).is_some_and(|bound| bound > minimum)
        }
        Formula::Lt(lhs, rhs) if is_name(rhs) => {
            formula_integer_literal(lhs).is_some_and(|bound| bound >= minimum)
        }
        Formula::Le(lhs, rhs) if is_name(rhs) => {
            formula_integer_literal(lhs).is_some_and(|bound| bound > minimum)
        }
        Formula::And(parts) => {
            parts.iter().any(|part| formula_establishes_above(part, name, minimum))
        }
        _ => false,
    }
}
fn formula_has_sort(formula: &Formula, expected: Sort) -> bool {
    trust_types::check_formula_sort(formula).is_ok_and(|actual| actual == expected)
}

fn initial_symbolic_state(func: &VerifiableFunction) -> FxHashMap<String, Formula> {
    let mut state = FxHashMap::default();
    for decl in &func.body.locals {
        let name = crate::place_to_var_name(func, &trust_types::Place::local(decl.index));
        if let Some(model) = read_only_collection_model_for_local(func, decl.index) {
            state.insert(model.name.clone(), model.base_formula());
            state.insert(model.length_name(), model.length_formula());
        } else {
            state.insert(name.clone(), Formula::Var(name, crate::sort_for_ty(&decl.ty)));
        }
    }
    state
}

/// Simultaneous, capture-avoiding substitution of the current symbolic MIR
/// state into a source formula.
///
/// State values are inserted atomically — a replacement is never recursively
/// rewritten by another state entry. Quantifier binders shadow same-named MIR
/// locals, and a binder is alpha-renamed before descending whenever it would
/// capture a free variable in any replacement. The prior bottom-up `Formula::map`
/// replaced bound occurrences and could turn `forall i. P(i)` into a claim about
/// a same-named MIR local.
fn substitute_formula_state(formula: &Formula, state: &FxHashMap<String, Formula>) -> Formula {
    let mut occupied = formula_symbol_names(formula);
    occupied.extend(state.keys().cloned());
    for replacement in state.values() {
        occupied.extend(formula_symbol_names(replacement));
    }
    let mut fresh_counter = 0usize;
    substitute_formula_state_rec(formula, state, &mut occupied, &mut fresh_counter)
}

fn substitute_formula_state_rec(
    formula: &Formula,
    state: &FxHashMap<String, Formula>,
    occupied: &mut FxHashSet<String>,
    fresh_counter: &mut usize,
) -> Formula {
    match formula {
        Formula::Var(name, _) => state.get(name).cloned().unwrap_or_else(|| formula.clone()),
        Formula::SymVar(name, _) => {
            state.get(name.as_str()).cloned().unwrap_or_else(|| formula.clone())
        }
        Formula::Forall(bindings, body) => substitute_formula_state_quantifier(
            true,
            bindings,
            body,
            state,
            occupied,
            fresh_counter,
        ),
        Formula::Exists(bindings, body) => substitute_formula_state_quantifier(
            false,
            bindings,
            body,
            state,
            occupied,
            fresh_counter,
        ),
        _ => formula.clone().map_children(&mut |child| {
            substitute_formula_state_rec(&child, state, occupied, fresh_counter)
        }),
    }
}

fn substitute_formula_state_quantifier(
    is_forall: bool,
    bindings: &[(Symbol, Sort)],
    body: &Formula,
    state: &FxHashMap<String, Formula>,
    occupied: &mut FxHashSet<String>,
    fresh_counter: &mut usize,
) -> Formula {
    let replacement_free: FxHashSet<String> =
        state.values().flat_map(|replacement| replacement.free_variables()).collect();
    let original_binding_names: Vec<String> =
        bindings.iter().map(|(name, _)| name.as_str().to_string()).collect();
    let mut renamed_bindings = bindings.to_vec();
    let mut renamed_body = body.clone();
    let mut renamed = FxHashSet::default();
    for original in &original_binding_names {
        if replacement_free.contains(original) && renamed.insert(original.clone()) {
            let fresh = fresh_loop_state_binder(occupied, fresh_counter);
            for (binding, _) in &mut renamed_bindings {
                if binding.as_str() == original {
                    *binding = Symbol::intern(&fresh);
                }
            }
            renamed_body =
                alpha_rename_loop_state_bound_occurrences(&renamed_body, original, &fresh);
        }
    }

    // Original binder spellings shadow same-named state entries even when the
    // binder was alpha-renamed above. Fresh spellings are removed as a defensive
    // guard too, although the allocator makes a state-key collision impossible.
    let mut visible_state = state.clone();
    for name in &original_binding_names {
        visible_state.remove(name);
    }
    for (name, _) in &renamed_bindings {
        visible_state.remove(name.as_str());
    }
    let substituted =
        substitute_formula_state_rec(&renamed_body, &visible_state, occupied, fresh_counter);
    if is_forall {
        Formula::Forall(renamed_bindings, Box::new(substituted))
    } else {
        Formula::Exists(renamed_bindings, Box::new(substituted))
    }
}

fn alpha_rename_loop_state_bound_occurrences(formula: &Formula, from: &str, to: &str) -> Formula {
    match formula {
        Formula::Var(name, sort) if name == from => Formula::Var(to.to_string(), sort.clone()),
        Formula::SymVar(name, sort) if name.as_str() == from => {
            Formula::SymVar(Symbol::intern(to), sort.clone())
        }
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _)
            if bindings.iter().any(|(name, _)| name.as_str() == from) =>
        {
            formula.clone()
        }
        _ => formula
            .clone()
            .map_children(&mut |child| alpha_rename_loop_state_bound_occurrences(&child, from, to)),
    }
}

fn fresh_loop_state_binder(occupied: &mut FxHashSet<String>, fresh_counter: &mut usize) -> String {
    loop {
        *fresh_counter = fresh_counter.saturating_add(1);
        let candidate =
            crate::generated_formula_symbol("loop_state_binder", &fresh_counter.to_string());
        if occupied.insert(candidate.clone()) {
            return candidate;
        }
    }
}

fn formula_symbol_names(formula: &Formula) -> FxHashSet<String> {
    let mut names = FxHashSet::default();
    formula.visit(&mut |node| match node {
        Formula::Var(name, _) => {
            names.insert(name.clone());
        }
        Formula::SymVar(name, _) => {
            names.insert(name.as_str().to_string());
        }
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
            names.extend(bindings.iter().map(|(name, _)| name.as_str().to_string()));
        }
        Formula::Pred(name, _) => {
            names.insert(name.as_str().to_string());
        }
        Formula::FnApp { func, .. } => {
            names.insert(func.clone());
        }
        Formula::Ctor { ctor, .. } => {
            names.insert(ctor.clone());
        }
        Formula::Sel { datatype, field, .. } => {
            names.insert(datatype.clone());
            names.insert(field.clone());
        }
        Formula::IsCtor { datatype, ctor, .. } => {
            names.insert(datatype.clone());
            names.insert(ctor.clone());
        }
        _ => {}
    });
    names
}

fn symbolic_state_at_loop_entry(
    func: &VerifiableFunction,
    header: BlockId,
) -> Option<FxHashMap<String, Formula>> {
    let mut state = initial_symbolic_state(func);
    if header == BlockId(0) {
        return Some(state);
    }
    let mut current = BlockId(0);
    let mut seen = FxHashSet::default();
    while current != header {
        // Fail closed on per-function budget overrun: bail the symbolic
        // entry-state walk to an Unsupported loop-invariant VC (drop-only,
        // never a proof). Trip count is seen-bounded, but repeated symbolic
        // substitution can grow each state formula exponentially, so poll the
        // ambient deadline before every step.
        if trust_types::verify_budget::budget_exhausted() {
            return None;
        }
        if !seen.insert(current) {
            return None;
        }
        let block = func.body.blocks.get(current.0)?;
        apply_symbolic_statements(func, &block.stmts, &mut state, None)?;
        current = match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => *target,
            _ => return None,
        };
    }
    Some(state)
}

fn symbolic_single_path_loop_transition(
    func: &VerifiableFunction,
    header: BlockId,
) -> Option<(FxHashMap<String, Formula>, Formula)> {
    let loop_info: Vec<_> = crate::termination::detect_loops(&func.body)
        .into_iter()
        .filter(|info| info.header == header)
        .collect();
    let [loop_info] = loop_info.as_slice() else { return None };
    let in_loop: FxHashSet<_> = loop_info.body_blocks.iter().copied().collect();
    let header_block = func.body.blocks.get(header.0)?;
    let mut state = initial_symbolic_state(func);
    apply_symbolic_statements(func, &header_block.stmts, &mut state, None)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &header_block.terminator else {
        return None;
    };
    let mut body_targets: Vec<BlockId> = targets
        .iter()
        .map(|(_, target)| *target)
        .chain(std::iter::once(*otherwise))
        .filter(|target| *target != header && in_loop.contains(target))
        .collect();
    body_targets.sort_by_key(|target| target.0);
    body_targets.dedup();
    let [body_target] = body_targets.as_slice() else { return None };
    let guard = switch_edge_formula(func, discr, targets, *otherwise, *body_target, &state)?;

    let transition_blocks =
        single_path_loop_transition_blocks(func, header, *body_target, &in_loop)?;
    if !checked_update_shapes_are_authenticated(func, &transition_blocks) {
        return None;
    }
    for current in transition_blocks {
        let block = func.body.blocks.get(current.0)?;
        apply_symbolic_statements(func, &block.stmts, &mut state, Some(&guard))?;
    }
    Some((state, guard))
}

/// Collect the exact body path for one successful loop iteration before any
/// symbolic state is mutated. Besides making the single-path premise explicit,
/// this gives checked-arithmetic authentication the complete transition rather
/// than only the block currently being interpreted.
fn single_path_loop_transition_blocks(
    func: &VerifiableFunction,
    header: BlockId,
    body_target: BlockId,
    in_loop: &FxHashSet<BlockId>,
) -> Option<Vec<BlockId>> {
    let mut current = body_target;
    let mut seen = FxHashSet::default();
    let mut blocks = Vec::new();
    loop {
        // Fail closed on per-function budget overrun: bail the symbolic
        // loop-transition walk to an Unsupported loop-invariant/decreases VC
        // (drop-only, never a proof). Trip count is seen-bounded, but repeated
        // symbolic substitution can grow each state formula exponentially, so
        // poll the ambient deadline before every step.
        if trust_types::verify_budget::budget_exhausted() {
            return None;
        }
        if current == header {
            break;
        }
        if !seen.insert(current) || !in_loop.contains(&current) {
            return None;
        }
        let block = func.body.blocks.get(current.0)?;
        blocks.push(current);
        current = match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => *target,
            _ => return None,
        };
    }
    Some(blocks)
}

fn switch_edge_formula(
    func: &VerifiableFunction,
    discr: &Operand,
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
    target: BlockId,
    state: &FxHashMap<String, Formula>,
) -> Option<Formula> {
    let discr_formula = symbolic_operand(func, discr, state)?;
    let discr_ty = crate::operand_ty_cow(func, discr)?;
    if machine_integer_ty(discr_ty.as_ref()) && discr_ty.is_signed() {
        // SwitchInt targets are raw u128 bit patterns. Until this lane decodes
        // them through the discriminant's signed width, comparing them as Int
        // would turn negative cases into huge positive constants.
        return None;
    }
    let constant = |value: u128| -> Option<Formula> {
        if matches!(discr_ty.as_ref(), Ty::Bool) {
            Some(Formula::Bool(value != 0))
        } else {
            Some(Formula::Int(i128::try_from(value).ok()?))
        }
    };
    let explicit: Vec<Formula> = targets
        .iter()
        .filter(|(_, edge_target)| *edge_target == target)
        .map(|(value, _)| {
            Some(Formula::Eq(Box::new(discr_formula.clone()), Box::new(constant(*value)?)))
        })
        .collect::<Option<_>>()?;
    let mut cases = explicit;
    if otherwise == target {
        let excluded: Vec<Formula> = targets
            .iter()
            .map(|(value, _)| {
                Some(Formula::Eq(Box::new(discr_formula.clone()), Box::new(constant(*value)?)))
            })
            .collect::<Option<_>>()?;
        cases.push(Formula::Not(Box::new(disjunction(excluded))));
    }
    Some(disjunction(cases))
}

fn disjunction(mut formulas: Vec<Formula>) -> Formula {
    match formulas.len() {
        0 => Formula::Bool(false),
        1 => formulas.pop().unwrap(),
        _ => Formula::Or(formulas),
    }
}

/// Authenticate the only checked-machine-arithmetic shape admitted by the
/// E4/E5 symbolic transition lane.
///
/// `symbolic_binop` independently proves that an unsigned unit update is exact
/// under the taken loop guard.  That arithmetic fact is not permission to
/// treat an arbitrary `CheckedBinaryOp` tuple as a scalar definition, however:
/// the public MIR carrier must also preserve rustc's typed checked tuple, its
/// matching no-overflow assertion, and the exact value copy-back.  Requiring
/// the complete local shape keeps malformed or stale serialized MIR out of the
/// fresh-production lane.  Any miss returns `false`; the caller emits the
/// ordinary visible `UserLoopContractUnsupported` row.
fn checked_update_shapes_are_authenticated(
    func: &VerifiableFunction,
    transition_blocks: &[BlockId],
) -> bool {
    transition_blocks.iter().all(|block_id| {
        func.body.blocks.get(block_id.0).is_some_and(|block| {
            checked_update_shape_is_authenticated(func, block, transition_blocks)
        })
    })
}

fn checked_update_shape_is_authenticated(
    func: &VerifiableFunction,
    block: &BasicBlock,
    transition_blocks: &[BlockId],
) -> bool {
    let checked =
        block
            .stmts
            .iter()
            .filter_map(|statement| match statement {
                Statement::Assign {
                    place, rvalue: Rvalue::CheckedBinaryOp(op, lhs, rhs), ..
                } if place.projections.is_empty() => Some((place.local, op, lhs, rhs)),
                _ => None,
            })
            .collect::<Vec<_>>();
    if checked.is_empty() {
        return true;
    }
    let [(tuple_local, op, lhs, rhs)] = checked.as_slice() else {
        return false;
    };
    let tuple_local = *tuple_local;
    let op = *op;

    // The checked result local has one live definition over the COMPLETE loop
    // transition. In particular, an overwrite in a later body block must not
    // leave the symbolic `.0` entry pointing at the stale checked value.
    if transition_blocks
        .iter()
        .filter_map(|block_id| func.body.blocks.get(block_id.0))
        .flat_map(|transition_block| transition_block.stmts.iter())
        .filter(|statement| {
            matches!(statement, Statement::Assign { place, .. } if place.local == tuple_local)
        })
        .count()
        != 1
    {
        return false;
    }

    let Some(lhs_ty) = crate::operand_ty_cow(func, lhs).map(|ty| ty.into_owned()) else {
        return false;
    };
    let Some(rhs_ty) = crate::operand_ty_cow(func, rhs).map(|ty| ty.into_owned()) else {
        return false;
    };
    if lhs_ty != rhs_ty {
        return false;
    }
    let Some(tuple_decl) = func.body.locals.iter().find(|decl| decl.index == tuple_local) else {
        return false;
    };
    let Ty::Tuple(fields) = &tuple_decl.ty else {
        return false;
    };
    if fields.as_slice() != [lhs_ty, Ty::Bool] {
        return false;
    }

    let unit_constant = |operand: &Operand| {
        matches!(
            operand,
            Operand::Constant(
                trust_types::ConstValue::Int(1) | trust_types::ConstValue::Uint(1, _)
            )
        )
    };
    let bare_local = |operand: &Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            Some(place.local)
        }
        _ => None,
    };
    let subject_local = match op {
        BinOp::Sub if unit_constant(rhs) => bare_local(lhs),
        BinOp::Add if unit_constant(rhs) => bare_local(lhs),
        BinOp::Add if unit_constant(lhs) => bare_local(rhs),
        _ => None,
    };
    let Some(subject_local) = subject_local else {
        return false;
    };

    let Terminator::Assert { cond, expected: false, msg, target, .. } = &block.terminator else {
        return false;
    };
    let cond_matches = matches!(
        cond,
        Operand::Copy(place) | Operand::Move(place)
            if place.local == tuple_local
                && place.projections.as_slice() == [trust_types::Projection::Field(1)]
    );
    if !cond_matches || !matches!(msg, AssertMessage::Overflow(assert_op) if assert_op == op) {
        return false;
    }

    // The asserted-success target must be the next block that this exact path
    // interprets. A copy-back placed in the loop header is not part of the
    // post-state constructed below and therefore cannot authenticate the tuple.
    let Some(block_position) = transition_blocks.iter().position(|id| *id == block.id) else {
        return false;
    };
    if transition_blocks.get(block_position + 1) != Some(target) {
        return false;
    }

    let Some(target_block) = func.body.blocks.get(target.0) else {
        return false;
    };
    let subject_writes = transition_blocks
        .iter()
        .filter_map(|block_id| func.body.blocks.get(block_id.0))
        .flat_map(|transition_block| transition_block.stmts.iter())
        .filter(|statement| {
            matches!(statement, Statement::Assign { place, .. } if place.local == subject_local)
        })
        .collect::<Vec<_>>();
    let [subject_write] = subject_writes.as_slice() else {
        return false;
    };
    if !target_block.stmts.iter().any(|statement| std::ptr::eq(statement, *subject_write)) {
        return false;
    }
    let Statement::Assign { place, rvalue, .. } = *subject_write else {
        return false;
    };
    place.projections.is_empty()
        && matches!(
            rvalue,
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source))
                if source.local == tuple_local
                    && source.projections.as_slice() == [trust_types::Projection::Field(0)]
        )
}

fn symbolic_state_key_belongs_to_local(key: &str, base: &str) -> bool {
    if key == base {
        return true;
    }
    key.strip_prefix(base)
        .is_some_and(|suffix| matches!(suffix.as_bytes().first(), Some(b'.' | b'[' | b'*' | b'@')))
}

/// A whole-local write invalidates every cached projection of the previous
/// value. Projected writes are outside this exact transition fragment, but we
/// still invalidate the complete base before declining so no future extension
/// can accidentally retain a stale sibling field.
fn invalidate_symbolic_local(
    func: &VerifiableFunction,
    local: usize,
    state: &mut FxHashMap<String, Formula>,
) {
    let base = crate::place_to_var_name(func, &trust_types::Place::local(local));
    state.retain(|key, _| !symbolic_state_key_belongs_to_local(key, &base));
}

fn apply_symbolic_statements(
    func: &VerifiableFunction,
    statements: &[Statement],
    state: &mut FxHashMap<String, Formula>,
    machine_arithmetic_guard: Option<&Formula>,
) -> Option<()> {
    for statement in statements {
        match statement {
            Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                let dest = crate::place_to_var_name(func, place);
                if let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue {
                    let value =
                        symbolic_binop(func, *op, lhs, rhs, state, machine_arithmetic_guard)?;
                    invalidate_symbolic_local(func, place.local, state);
                    let field = trust_types::Place {
                        local: place.local,
                        projections: vec![trust_types::Projection::Field(0)],
                    };
                    state.insert(crate::place_to_var_name(func, &field), value);
                    // The tuple itself has no scalar Formula denotation.
                } else {
                    let value = symbolic_rvalue(func, rvalue, state, machine_arithmetic_guard)?;
                    invalidate_symbolic_local(func, place.local, state);
                    state.insert(dest, value);
                }
            }
            Statement::Assign { place, .. } => {
                invalidate_symbolic_local(func, place.local, state);
                return None;
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                invalidate_symbolic_local(func, place.local, state);
                return None;
            }
            _ => return None,
        }
    }
    Some(())
}

fn symbolic_read_only_collection_select(
    func: &VerifiableFunction,
    operand: &Operand,
    state: &FxHashMap<String, Formula>,
) -> Option<Formula> {
    let Operand::Copy(place) = operand else { return None };
    let model = read_only_collection_model_for_local(func, place.local)?;
    let index_projection = read_only_collection_index_projection(place, model.local)?;
    let index = match index_projection {
        Projection::Index(local) => {
            let decl = func.body.locals.get(*local)?;
            if decl.index != *local {
                return None;
            }
            if !matches!(decl.ty, Ty::Int { .. } | Ty::PtrSizedInt { .. }) {
                return None;
            }
            let name = crate::place_to_var_name(func, &trust_types::Place::local(*local));
            state.get(&name).cloned().unwrap_or_else(|| Formula::Var(name, Sort::Int))
        }
        Projection::ConstantIndex { offset, from_end: false, .. } => {
            Formula::Int(i128::try_from(*offset).ok()?)
        }
        _ => return None,
    };
    if !formula_has_sort(&index, Sort::Int) {
        return None;
    }
    let expected_base = model.base_formula();
    let base = state.get(&model.name)?.clone();
    if base != expected_base {
        return None;
    }
    Some(Formula::Select(Box::new(base), Box::new(index)))
}

fn symbolic_read_only_collection_len(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    state: &FxHashMap<String, Formula>,
) -> Option<Formula> {
    let model = read_only_collection_model_for_local(func, place.local)?;
    if !exact_read_only_collection_len_place(place, model.local) {
        return None;
    }
    let expected = model.length_formula();
    let current = state.get(&model.length_name())?.clone();
    (current == expected).then_some(current)
}

fn symbolic_fixed_array_slice_view_cast(
    func: &VerifiableFunction,
    operand: &Operand,
    target_ty: &Ty,
) -> Option<Formula> {
    // Requiring the source model to be stable is what connects this local
    // rvalue recognition to `exact_fixed_array_slice_metadata_pair`: a cast
    // whose view is retained or escapes makes the source model unavailable.
    let model = fixed_array_slice_view_cast_model(func, operand, target_ty, true)?;
    Some(model.base_formula())
}

fn symbolic_read_only_collection_metadata_len(
    func: &VerifiableFunction,
    operand: &Operand,
    state: &FxHashMap<String, Formula>,
) -> Option<Formula> {
    let place = operand_place(operand)?;
    if let Some(model) = read_only_collection_model_for_local(func, place.local) {
        if !exact_read_only_collection_metadata_operand(func, operand, model.local) {
            return None;
        }
        let expected = model.length_formula();
        let current = state.get(&model.length_name())?.clone();
        return (current == expected).then_some(current);
    }

    // Fixed-array `.len()` is lowered by rustc through an ephemeral `&[T]`
    // local.  Its symbolic value is the exact source array base installed by
    // `symbolic_fixed_array_slice_view_cast`; recover the unique stable fixed
    // model and return its type-level length.  Only `Move(view)` is admitted,
    // matching the exact pair recognizer and preventing a generic alias lane.
    let Operand::Move(view) = operand else { return None };
    if !view.projections.is_empty() {
        return None;
    }
    let view_decl = func.body.locals.get(view.local)?;
    let Ty::Ref { mutable: false, inner: view_inner } = &view_decl.ty else {
        return None;
    };
    let Ty::Slice { elem: view_elem } = view_inner.as_ref() else { return None };
    let view_name = crate::place_to_var_name(func, view);
    let current_view = state.get(&view_name)?;
    let mut matches = func.body.locals.iter().filter_map(|decl| {
        let model = read_only_collection_model_for_local(func, decl.index)?;
        if !matches!(&model.length, ReadOnlyCollectionLength::Fixed(_))
            || model.base_formula() != *current_view
        {
            return None;
        }
        let Ty::Ref { mutable: false, inner: source_inner } = &decl.ty else {
            return None;
        };
        let Ty::Array { elem: source_elem, .. } = source_inner.as_ref() else {
            return None;
        };
        (source_elem == view_elem).then_some(model)
    });
    let model = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    Some(model.length_formula())
}

fn symbolic_rvalue(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    state: &FxHashMap<String, Formula>,
    machine_arithmetic_guard: Option<&Formula>,
) -> Option<Formula> {
    match rvalue {
        Rvalue::Use(operand) => symbolic_operand(func, operand, state),
        Rvalue::Len(place) => symbolic_read_only_collection_len(func, place, state),
        Rvalue::Cast(operand, target_ty) => {
            symbolic_fixed_array_slice_view_cast(func, operand, target_ty)
        }
        Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
            symbolic_read_only_collection_metadata_len(func, operand, state)
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            symbolic_binop(func, *op, lhs, rhs, state, machine_arithmetic_guard)
        }
        Rvalue::UnaryOp(UnOp::Neg, operand)
            if crate::operand_ty_cow(func, operand).as_deref().is_some_and(machine_integer_ty) =>
        {
            // Mathematical negation does not model fixed-width MIN overflow or
            // wrapping. Keep the entire loop contract fail-closed.
            None
        }
        Rvalue::UnaryOp(UnOp::Not, operand)
            if crate::operand_ty_cow(func, operand).as_deref().is_some_and(machine_integer_ty) =>
        {
            // Formula::Not is Boolean negation, not a fixed-width bitwise
            // complement.  Mapping an integer `!x` to it is both ill-sorted and
            // semantically wrong, so the exact transition lane rejects it.
            None
        }
        Rvalue::UnaryOp(UnOp::Neg, operand) => {
            Some(Formula::Neg(Box::new(symbolic_operand(func, operand, state)?)))
        }
        Rvalue::UnaryOp(UnOp::Not, operand) => {
            Some(Formula::Not(Box::new(symbolic_operand(func, operand, state)?)))
        }
        _ => None,
    }
}

fn symbolic_binop(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    state: &FxHashMap<String, Formula>,
    machine_arithmetic_guard: Option<&Formula>,
) -> Option<Formula> {
    let lhs_formula = symbolic_operand(func, lhs, state)?;
    let rhs_formula = symbolic_operand(func, rhs, state)?;
    let ty = crate::operand_ty_cow(func, lhs);
    if ty.as_deref().is_some_and(machine_integer_ty)
        && matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Rem
                | BinOp::Shl
                | BinOp::Shr
        )
        && !machine_arithmetic_guard.is_some_and(|guard| {
            guarded_unsigned_unit_update_is_exact(
                func,
                op,
                lhs,
                rhs,
                &lhs_formula,
                &rhs_formula,
                guard,
            )
        })
    {
        // `try_binop_to_formula` lowers arithmetic to unbounded Int operations;
        // shifts likewise do not preserve MIR's fixed-width/out-of-range shift
        // behavior in this lane.  Neither is an exact transition for a Rust
        // machine integer, so E4/E5 must wait for an exact BV encoding.
        return None;
    }
    let width = ty.as_deref().and_then(Ty::int_width);
    let signed = ty.as_deref().is_some_and(Ty::is_signed);
    crate::chc::try_binop_to_formula(op, lhs_formula, rhs_formula, width, signed).ok()
}

/// Admit the two unit updates whose taken-edge guard proves that the
/// mathematical-Int transition is byte-for-byte equivalent to unsigned MIR:
///
/// * `i + 1` under `i < upper`, where `upper` is an in-range value of the same
///   unsigned width. Since `upper <= MAX`, the addition cannot wrap.
/// * `i - 1` under a taken guard proving `i > 0`. Since unsigned values are
///   non-negative, the subtraction cannot underflow.
///
/// Both subjects must be bare unsigned locals. Wider steps, reversed
/// subtraction, and guards that merely prove `i >= 0` remain fail-closed.
fn guarded_unsigned_unit_update_is_exact(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    lhs_formula: &Formula,
    rhs_formula: &Formula,
    guard: &Formula,
) -> bool {
    match op {
        BinOp::Add => {
            let (subject_operand, subject_formula) =
                if formula_integer_literal(rhs_formula) == Some(1) {
                    (lhs, lhs_formula)
                } else if formula_integer_literal(lhs_formula) == Some(1) {
                    (rhs, rhs_formula)
                } else {
                    return false;
                };
            let Some(width) = bare_unsigned_operand_width(func, subject_operand) else {
                return false;
            };
            if !matches!(subject_formula, Formula::Var(..)) {
                return false;
            }
            let Some(upper) = strict_upper_bound_from_true_guard(guard, subject_formula) else {
                return false;
            };
            unsigned_formula_is_in_range(func, upper, width)
        }
        BinOp::Sub => {
            formula_integer_literal(rhs_formula) == Some(1)
                && bare_unsigned_operand_width(func, lhs).is_some()
                && matches!(lhs_formula, Formula::Var(..))
                && unsigned_positive_from_true_guard(guard, lhs_formula)
        }
        _ => false,
    }
}

/// The matching authored E5 measure is exact for the same reason: under
/// `i < upper`, both unsigned `upper - i` and `upper - (i + 1)` agree with
/// their mathematical-Int encodings. Requiring the exact post-state shape
/// also proves that the body left `upper` unchanged; otherwise a valid
/// pre-state subtraction could silently authorize an underflowing post-state
/// subtraction.
fn guarded_unsigned_difference_is_exact(
    func: &VerifiableFunction,
    measure: &Formula,
    after: &Formula,
    guard: &Formula,
) -> bool {
    let Formula::Sub(upper, subject) = measure else { return false };
    let Formula::Sub(after_upper, after_subject) = after else { return false };
    let (Some(subject_width), Some(upper_width)) =
        (bare_unsigned_formula_width(func, subject), bare_unsigned_formula_width(func, upper))
    else {
        return false;
    };
    subject_width == upper_width
        && after_upper == upper
        && guarded_unit_increment(subject, after_subject)
        && strict_upper_bound_from_true_guard(guard, subject)
            .is_some_and(|guard_upper| guard_upper == upper.as_ref())
}

fn guarded_unit_increment(before: &Formula, after: &Formula) -> bool {
    let Formula::Add(lhs, rhs) = after else { return false };
    (lhs.as_ref() == before && formula_integer_literal(rhs) == Some(1))
        || (rhs.as_ref() == before && formula_integer_literal(lhs) == Some(1))
}

fn bare_unsigned_operand_width(func: &VerifiableFunction, operand: &Operand) -> Option<u32> {
    let place = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place,
        _ => return None,
    };
    let decl = func.body.locals.iter().find(|decl| decl.index == place.local)?;
    match decl.ty {
        Ty::Int { width, signed: false } => Some(width),
        _ => None,
    }
}

fn bare_unsigned_formula_width(func: &VerifiableFunction, formula: &Formula) -> Option<u32> {
    let Formula::Var(name, _) = formula else { return None };
    let mut matching = func.body.locals.iter().filter(|decl| {
        decl.name.as_deref() == Some(name)
            || crate::place_to_var_name(func, &trust_types::Place::local(decl.index)) == *name
    });
    let decl = matching.next()?;
    if matching.next().is_some() {
        return None;
    }
    match decl.ty {
        Ty::Int { width, signed: false } => Some(width),
        _ => None,
    }
}

fn unsigned_formula_is_in_range(func: &VerifiableFunction, formula: &Formula, width: u32) -> bool {
    if bare_unsigned_formula_width(func, formula) == Some(width) {
        return true;
    }
    let Some(value) = formula_integer_literal(formula) else { return false };
    if value < 0 || width == 0 || width > 128 {
        return false;
    }
    width == 128 || (value as u128) <= ((1_u128 << width) - 1)
}

fn strict_upper_bound_from_true_guard<'a>(
    guard: &'a Formula,
    subject: &Formula,
) -> Option<&'a Formula> {
    let predicate = predicate_asserted_by_true_guard(guard);
    match predicate {
        Formula::Lt(lhs, upper) if lhs.as_ref() == subject => Some(upper),
        Formula::And(parts) => {
            parts.iter().find_map(|part| strict_upper_bound_from_true_guard(part, subject))
        }
        _ => None,
    }
}

/// Peel the Boolean encoding produced by `SwitchInt` for a taken `while`
/// edge. Depending on whether the body is an explicit case or the `otherwise`
/// edge, the same source predicate arrives as `p == true` or `!(p == false)`.
/// This helper only removes those truth-preserving wrappers; it never rewrites
/// an arbitrary negation into a positive fact.
fn predicate_asserted_by_true_guard(guard: &Formula) -> &Formula {
    match guard {
        Formula::Eq(lhs, rhs) if matches!(rhs.as_ref(), Formula::Bool(true)) => lhs,
        Formula::Eq(lhs, rhs) if matches!(lhs.as_ref(), Formula::Bool(true)) => rhs,
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Eq(lhs, rhs) if matches!(rhs.as_ref(), Formula::Bool(false)) => lhs,
            Formula::Eq(lhs, rhs) if matches!(lhs.as_ref(), Formula::Bool(false)) => rhs,
            _ => guard,
        },
        _ => guard,
    }
}

fn unsigned_positive_from_true_guard(guard: &Formula, subject: &Formula) -> bool {
    let predicate = predicate_asserted_by_true_guard(guard);
    match predicate {
        Formula::Gt(lhs, lower) if lhs.as_ref() == subject => {
            formula_integer_literal(lower).is_some_and(|bound| bound >= 0)
        }
        Formula::Lt(lower, rhs) if rhs.as_ref() == subject => {
            formula_integer_literal(lower).is_some_and(|bound| bound >= 0)
        }
        Formula::Ge(lhs, lower) if lhs.as_ref() == subject => {
            formula_integer_literal(lower).is_some_and(|bound| bound >= 1)
        }
        Formula::Le(lower, rhs) if rhs.as_ref() == subject => {
            formula_integer_literal(lower).is_some_and(|bound| bound >= 1)
        }
        Formula::And(parts) => {
            parts.iter().any(|part| unsigned_positive_from_true_guard(part, subject))
        }
        _ => false,
    }
}

fn machine_integer_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
}

fn symbolic_operand(
    func: &VerifiableFunction,
    operand: &Operand,
    state: &FxHashMap<String, Formula>,
) -> Option<Formula> {
    if let Some(select) = symbolic_read_only_collection_select(func, operand, state) {
        return Some(select);
    }
    match operand {
        Operand::Copy(_) | Operand::Move(_) => {
            Some(substitute_formula_state(&crate::operand_to_formula(func, operand), state))
        }
        Operand::Constant(trust_types::ConstValue::OpaqueScalar { .. })
        | Operand::Symbolic(_)
        | Operand::Unsupported { .. } => None,
        Operand::Constant(_) => {
            Some(substitute_formula_state(&crate::operand_to_formula(func, operand), state))
        }
        // This exact transition subset is closed: future operand variants must
        // be reviewed instead of silently becoming unconstrained formulae.
        _ => None,
    }
}

/// Parse a loop invariant body in "bb<N>: <expr>" format.
/// Missing/malformed prefixes fail closed: authored native loop clauses are
/// paired explicitly and may never inherit a stale/default block identity.
pub(crate) fn loop_contract_body(body: &str) -> Option<(usize, String)> {
    if let Some(rest) = body.strip_prefix("bb")
        && let Some((block_str, expr)) = rest.split_once(':')
        && let Ok(block) = block_str.trim().parse::<usize>()
        && !expr.trim().is_empty()
    {
        return Some((block, expr.trim().to_string()));
    }
    None
}

/// Parse a type refinement body in "var: predicate" format.
/// Falls back to "v" as the variable name if no colon is found.
fn parse_refinement_body(body: &str) -> (String, String) {
    if let Some((var, pred)) = body.split_once(':') {
        (var.trim().to_string(), pred.trim().to_string())
    } else {
        ("v".to_string(), body.to_string())
    }
}

/// Parse a modifies clause body as a comma-separated variable list.
fn parse_modifies_body(body: &str) -> Vec<String> {
    body.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect()
}

/// Build a `ContractMetadata` indicating trust_wp contract presence.
fn trust_wp_metadata() -> ContractMetadata {
    ContractMetadata { has_loop_invariant: true, ..ContractMetadata::default() }
}

fn trust_wp_metadata_for_source(source_contract_index: usize) -> ContractMetadata {
    ContractMetadata { source_contract_index: Some(source_contract_index), ..trust_wp_metadata() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{ConstValue, Place};

    fn contract_test_function(contracts: Vec<Contract>) -> VerifiableFunction {
        VerifiableFunction {
            name: "contract_fn".to_string(),
            def_path: "test::contract_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::usize(),
            },
            contracts,
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn symbolic_base_writes_invalidate_cached_projections() {
        let mut func = contract_test_function(Vec::new());
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: Some("checked".into()),
            },
            LocalDecl {
                index: 2,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: Some("replacement".into()),
            },
        ];
        let checked_base = crate::place_to_var_name(&func, &Place::local(1));
        let checked_value = crate::place_to_var_name(&func, &Place::field(1, 0));
        let checked_flag = crate::place_to_var_name(&func, &Place::field(1, 1));

        let mut state = initial_symbolic_state(&func);
        state.insert(checked_value.clone(), Formula::Int(7));
        state.insert(checked_flag.clone(), Formula::Bool(false));
        assert!(
            apply_symbolic_statements(
                &func,
                &[Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                }],
                &mut state,
                None,
            )
            .is_some()
        );
        assert!(state.contains_key(&checked_base));
        assert!(!state.contains_key(&checked_value));
        assert!(!state.contains_key(&checked_flag));

        state.insert(checked_value.clone(), Formula::Int(9));
        state.insert(checked_flag.clone(), Formula::Bool(true));
        assert!(
            apply_symbolic_statements(
                &func,
                &[Statement::Assign {
                    place: Place::field(1, 0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
                    span: SourceSpan::default(),
                }],
                &mut state,
                None,
            )
            .is_none(),
            "projected writes remain outside the exact transition fragment",
        );
        assert!(!state.contains_key(&checked_base));
        assert!(!state.contains_key(&checked_value));
        assert!(!state.contains_key(&checked_flag));
    }

    fn feedback_loop_function() -> VerifiableFunction {
        // n = 10; i = n; while i > 0 { i = n; }
        //
        // This deliberately exercises only comparisons, logical connectives,
        // copies, and constants. Those operations are exact in the E4/E5 Int
        // representation; fixed-width arithmetic is covered by fail-closed
        // negative tests below.
        let clause_span = SourceSpan {
            file: "feedback.rs".to_string(),
            line_start: 8,
            col_start: 4,
            line_end: 8,
            col_end: 20,
        };
        VerifiableFunction {
            name: "feedback_loop".to_string(),
            def_path: "test::feedback_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Int(0)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![
                Contract {
                    kind: ContractKind::LoopInvariant,
                    span: clause_span.clone(),
                    body: "bb1: n <= 10 && i <= 10".to_string(),
                },
                Contract {
                    kind: ContractKind::Decreases,
                    span: clause_span,
                    body: "bb1: i".to_string(),
                },
            ],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn read_only_collection_loop_function(inner: Ty) -> VerifiableFunction {
        let xs_ty = Ty::Ref { mutable: false, inner: Box::new(inner) };
        let indexed_xs = Place {
            local: 1,
            projections: vec![
                Projection::Deref,
                Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
            ],
        };
        VerifiableFunction {
            name: "read_only_collection_loop".to_string(),
            def_path: "test::read_only_collection_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: xs_ty, name: Some("xs".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("keep".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("n".into()) },
                    LocalDecl { index: 4, ty: Ty::u32(), name: Some("value".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Len(Place {
                                local: 1,
                                projections: vec![Projection::Deref],
                            }),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(indexed_xs)),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![Contract {
                kind: ContractKind::LoopInvariant,
                span: SourceSpan::default(),
                body: "bb1: n == xs.len() && xs[0] == xs[0] && forall j: usize, j < xs.len() ==> xs[j] == xs[j]"
                    .to_string(),
            }],
            preconditions: vec![
                parse_spec_expr("forall j: usize, j < xs.len() ==> xs[j] == xs[j]")
                    .expect("read-only collection precondition parses"),
            ],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn use_rustc_fixed_array_len_lowering(func: &mut VerifiableFunction) -> usize {
        let Ty::Ref { mutable: false, inner } = &func.body.locals[1].ty else {
            panic!("fixture source must be an immutable fixed-array reference")
        };
        let Ty::Array { elem, .. } = inner.as_ref() else {
            panic!("fixture source must be a fixed array")
        };
        let slice_ref =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: elem.clone() }) };
        let view_local = func.body.locals.len();
        func.body.locals.push(LocalDecl {
            index: view_local,
            ty: slice_ref.clone(),
            name: Some("_array_slice_view".into()),
        });
        func.body.blocks[0].stmts.splice(
            0..1,
            [
                Statement::Assign {
                    place: Place::local(view_local),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), slice_ref),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::UnaryOp(
                        UnOp::PtrMetadata,
                        Operand::Move(Place::local(view_local)),
                    ),
                    span: SourceSpan::default(),
                },
            ],
        );
        view_local
    }

    fn assert_collection_loop_is_explicitly_unsupported(func: &VerifiableFunction) {
        let mut vcs = Vec::new();
        check_contracts(func, &mut vcs);
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == LOOP_CONTRACT_UNSUPPORTED_KIND)),
            "collection shape must fail closed visibly: {vcs:#?}",
        );
        assert!(
            !vcs.iter().any(|vc| matches!(
                vc.kind,
                VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
            )),
            "an unsupported collection must not mint E4 rows: {vcs:#?}",
        );
    }

    #[test]
    fn read_only_slice_uses_one_source_mir_sequence_and_length_identity() {
        let func = read_only_collection_loop_function(Ty::Slice { elem: Box::new(Ty::u32()) });
        let mut vcs = Vec::new();
        check_contracts(&func, &mut vcs);
        assert_eq!(vcs.len(), 2, "the supported invariant emits exactly its E4 pair: {vcs:#?}");
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
            "the exact immutable slice lane must not degrade: {vcs:#?}",
        );
        let (initiation, consecution) = e4_pair(&vcs);
        assert!(formula_has_sort(&initiation.formula, Sort::Bool));
        assert!(formula_has_sort(&consecution.formula, Sort::Bool));

        let model = read_only_collection_model_for_local(&func, 1).expect("stable slice model");
        let canonical_base = model.base_formula();
        let model_length = model.length_formula();
        assert!(formula_contains(&initiation.formula, &canonical_base));
        assert!(formula_contains(&consecution.formula, &canonical_base));
        let typed_precondition =
            type_loop_formula(&func, func.preconditions[0].clone(), Sort::Bool)
                .expect("precondition rebinds through the same model");
        assert!(
            formula_contains(&initiation.formula, &typed_precondition),
            "initiation must consume the exact typed source precondition",
        );
        let canonical_length_precondition = Formula::Gt(
            Box::new(Formula::Var("xs__slice_len".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(
            type_loop_formula(&func, canonical_length_precondition, Sort::Bool),
            Some(Formula::Gt(Box::new(model_length.clone()), Box::new(Formula::Int(0)))),
            "the canonical bounds/summary length leaf must rebind to E4's one collection length",
        );

        let entry = symbolic_state_at_loop_entry(&func, BlockId(1)).expect("exact preheader");
        let length = Formula::Var("xs_len".into(), Sort::Int);
        assert_eq!(length, model_length);
        assert_eq!(entry.get("n"), Some(&length));
        assert_eq!(entry.get("xs"), Some(&canonical_base));
        let indexed = Operand::Copy(Place {
            local: 1,
            projections: vec![
                Projection::Deref,
                Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
            ],
        });
        assert_eq!(
            symbolic_operand(&func, &indexed, &entry),
            Some(Formula::Select(Box::new(canonical_base), Box::new(Formula::Int(0)),)),
        );
        assert_eq!(
            symbolic_rvalue(
                &func,
                &Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                &entry,
                None,
            ),
            Some(length),
            "only the exact slice-fat-pointer metadata shares the length term",
        );

        let mut metadata_func = func.clone();
        let Statement::Assign { rvalue, .. } = &mut metadata_func.body.blocks[0].stmts[0] else {
            unreachable!()
        };
        *rvalue = Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1)));
        let mut metadata_vcs = Vec::new();
        check_contracts(&metadata_func, &mut metadata_vcs);
        assert_eq!(
            metadata_vcs.len(),
            2,
            "exact slice metadata must retain the E4 pair: {metadata_vcs:#?}",
        );
        let metadata_entry =
            symbolic_state_at_loop_entry(&metadata_func, BlockId(1)).expect("exact metadata entry");
        assert_eq!(metadata_entry.get("n"), Some(&Formula::Var("xs_len".into(), Sort::Int)));
    }

    #[test]
    fn read_only_fixed_array_length_is_the_exact_type_constant() {
        let mut func =
            read_only_collection_loop_function(Ty::Array { elem: Box::new(Ty::u32()), len: 4 });
        let view_local = use_rustc_fixed_array_len_lowering(&mut func);
        assert!(
            exact_fixed_array_slice_metadata_pair(&func, 1, 0, 0),
            "the fixture must retain rustc's exact adjacent Cast + PtrMetadata shape",
        );
        assert!(
            read_only_collection_arg_is_stable(&func, 1),
            "the metadata-only slice view must not count as a retained alias",
        );
        let mut vcs = Vec::new();
        check_contracts(&func, &mut vcs);
        assert_eq!(
            vcs.len(),
            2,
            "rustc's array-to-slice metadata shape should emit its E4 pair: {vcs:#?}",
        );
        let entry = symbolic_state_at_loop_entry(&func, BlockId(1)).expect("exact preheader");
        assert_eq!(entry.get("n"), Some(&Formula::Int(4)));
        assert_eq!(entry.get("xs_len"), Some(&Formula::Int(4)));
        assert_eq!(
            entry.get("_array_slice_view"),
            Some(
                &Formula::Var("xs".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),)
            ),
        );
        assert!(
            symbolic_rvalue(
                &func,
                &Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                &entry,
                None,
            )
            .is_none(),
            "a sized-array pointer has no slice-length metadata",
        );

        let mut retained_view = func.clone();
        retained_view.body.blocks[0].stmts.push(Statement::PlaceMention(Place::local(view_local)));
        assert_collection_loop_is_explicitly_unsupported(&retained_view);

        let mut mutable_source = func;
        let Ty::Ref { mutable, .. } = &mut mutable_source.body.locals[1].ty else { unreachable!() };
        *mutable = true;
        assert_collection_loop_is_explicitly_unsupported(&mutable_source);
    }

    #[test]
    fn read_only_collection_literal_index_rebinding_is_exact_and_fail_closed() {
        for inner in [
            Ty::Slice { elem: Box::new(Ty::u32()) },
            Ty::Array { elem: Box::new(Ty::u32()), len: 4 },
        ] {
            let func = read_only_collection_loop_function(inner);
            let model =
                read_only_collection_model_for_local(&func, 1).expect("stable collection model");
            let element =
                Formula::Select(Box::new(model.base_formula()), Box::new(Formula::Int(0)));
            let parsed = parse_spec_expr("xs[0] == xs[0]")
                .expect("literal collection projection must parse canonically");
            assert_eq!(
                type_loop_formula(&func, parsed, Sort::Bool),
                Some(Formula::Eq(Box::new(element.clone()), Box::new(element))),
                "literal source indexing must share the symbolic MIR array term",
            );
        }

        let func = read_only_collection_loop_function(Ty::Slice { elem: Box::new(Ty::u32()) });
        for name in ["ghost[0]", "xs[00]", "xs[0][1]", "xs[]", "xs[-1]", "[0]"] {
            assert!(
                read_only_collection_literal_index_for_name(&func, name).is_none(),
                "noncanonical or unbound literal projection must fail closed: {name}",
            );
            let forged = Formula::Eq(
                Box::new(Formula::Var(name.to_string(), Sort::Int)),
                Box::new(Formula::Var(name.to_string(), Sort::Int)),
            );
            assert!(
                type_loop_formula(&func, forged, Sort::Bool).is_none(),
                "a forged literal projection must not acquire collection authority: {name}",
            );
        }
    }

    #[test]
    fn read_only_collection_lane_rejects_mutation_alias_and_untyped_index_shapes() {
        let base = || read_only_collection_loop_function(Ty::Slice { elem: Box::new(Ty::u32()) });

        let mut mutable = base();
        let Ty::Ref { mutable: is_mutable, .. } = &mut mutable.body.locals[1].ty else {
            unreachable!()
        };
        *is_mutable = true;
        assert_collection_loop_is_explicitly_unsupported(&mutable);

        let mut reseated = base();
        reseated.body.blocks[2].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            },
        );
        assert_collection_loop_is_explicitly_unsupported(&reseated);

        let mut aliased = base();
        aliased.body.locals[4].ty = aliased.body.locals[1].ty.clone();
        aliased.body.blocks[2].stmts[0] = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        };
        assert_collection_loop_is_explicitly_unsupported(&aliased);

        let mut projected_write = base();
        projected_write.body.blocks[2].stmts.insert(
            0,
            Statement::Assign {
                place: Place {
                    local: 1,
                    projections: vec![
                        Projection::Deref,
                        Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
                    ],
                },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                span: SourceSpan::default(),
            },
        );
        assert_collection_loop_is_explicitly_unsupported(&projected_write);

        let mut collection_call = base();
        collection_call.body.blocks[2].terminator = Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            func: "inspect".into(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(4),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
        };
        assert_collection_loop_is_explicitly_unsupported(&collection_call);

        let mut wrong_len = base();
        let Statement::Assign { rvalue, .. } = &mut wrong_len.body.blocks[0].stmts[0] else {
            unreachable!()
        };
        *rvalue = Rvalue::Len(Place::local(1));
        assert_collection_loop_is_explicitly_unsupported(&wrong_len);

        let mut bool_index = base();
        let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(place)), .. } =
            &mut bool_index.body.blocks[2].stmts[0]
        else {
            unreachable!()
        };
        place.projections = vec![Projection::Deref, Projection::Index(2)];
        assert_collection_loop_is_explicitly_unsupported(&bool_index);

        let mut moved_out_of_borrow = base();
        let Statement::Assign { rvalue: Rvalue::Use(operand), .. } =
            &mut moved_out_of_borrow.body.blocks[2].stmts[0]
        else {
            unreachable!()
        };
        let Operand::Copy(place) = operand else { unreachable!() };
        *operand = Operand::Move(place.clone());
        assert_collection_loop_is_explicitly_unsupported(&moved_out_of_borrow);

        let mut reordered_locals = base();
        reordered_locals.body.locals.swap(1, 4);
        assert!(!body_locals_have_canonical_positions(&reordered_locals));
        assert_collection_loop_is_explicitly_unsupported(&reordered_locals);

        let nonscalar = read_only_collection_loop_function(Ty::Slice {
            elem: Box::new(Ty::Tuple(vec![Ty::u32()])),
        });
        assert_collection_loop_is_explicitly_unsupported(&nonscalar);
    }

    #[test]
    fn symbolic_state_substitution_is_simultaneous_and_capture_avoiding() {
        let quantified = Formula::Forall(
            vec![(Symbol::intern("i"), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("i".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            )),
        );
        let mut state = FxHashMap::default();
        state.insert("i".into(), Formula::Int(7));
        state.insert("x".into(), Formula::Var("i".into(), Sort::Int));
        let substituted = substitute_formula_state(&quantified, &state);
        assert_eq!(substituted.free_variables(), FxHashSet::from_iter(["i".to_string()]));
        let Formula::Forall(bindings, body) = substituted else { panic!("expected forall") };
        assert_ne!(bindings[0].0.as_str(), "i", "binder must be alpha-renamed");
        assert!(formula_contains(&body, &Formula::Var("i".into(), Sort::Int)));
        assert!(formula_contains(
            &body,
            &Formula::Var(bindings[0].0.as_str().to_string(), Sort::Int),
        ));

        let simultaneous = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let mut state = FxHashMap::default();
        state.insert("x".into(), Formula::Var("y".into(), Sort::Int));
        state.insert("y".into(), Formula::Int(1));
        assert_eq!(
            substitute_formula_state(&simultaneous, &state),
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(1)),),
            "a replacement must not be rewritten by a later state entry",
        );
    }

    fn e4_pair(vcs: &[VerificationCondition]) -> (VerificationCondition, VerificationCondition) {
        let initiation = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::LoopInvariantInitiation { .. }))
            .expect("E4 initiation")
            .clone();
        let consecution = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
            .expect("E4 consecution")
            .clone();
        (initiation, consecution)
    }

    fn e5_formula(vcs: &[VerificationCondition]) -> Formula {
        vcs.iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::NonTermination { context, .. }
                    if context == "loop-decreases")
            })
            .expect("E5 loop-decreases VC")
            .formula
            .clone()
    }

    #[test]
    fn authored_body_vcs_carry_exact_source_contract_indices() {
        let loop_vcs = crate::generate_vcs(&feedback_loop_function());
        let (initiation, consecution) = e4_pair(&loop_vcs);
        for vc in [&initiation, &consecution] {
            assert_eq!(
                vc.contract_metadata.and_then(|metadata| metadata.source_contract_index),
                Some(0),
                "both E4 rows must bind to the invariant clause: {vc:#?}"
            );
        }
        let e5 = loop_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::NonTermination { context, .. }
                    if context == "loop-decreases")
            })
            .expect("E5 row");
        assert_eq!(
            e5.contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(1),
            "E5 must bind to the decreases clause"
        );

        let post = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);
        let post_vcs = crate::generate_vcs(&post);
        let body_post = post_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Postcondition))
            .expect("body-aware postcondition");
        assert_eq!(
            body_post.contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0)
        );
    }

    fn formula_contains(formula: &Formula, needle: &Formula) -> bool {
        formula == needle
            || formula.children().into_iter().any(|child| formula_contains(child, needle))
    }

    #[test]
    fn test_requires_generates_precondition_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "contract_fn"));
        // Trust: definition-site Precondition VCs are trivially provable
        // (`Bool(false)` means the negated obligation is UNSAT). The
        // precondition expression itself is preserved in `func.preconditions`
        // (and the underlying `contracts` vec) and conjoined onto other VCs
        // as a hypothesis where it can be useful.
        assert_eq!(vcs[0].formula, Formula::Bool(false));
        assert_eq!(
            vcs[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0),
            "definition-site requires rows must retain their exact source-clause identity"
        );
    }

    #[test]
    fn test_requires_in_both_contracts_and_preconditions_emits_one_vc() {
        // Trust (Requires dedup): `trust-mir-extract` carries every declared
        // `#[requires]` TWICE — as the raw `Contract` string AND as its parsed
        // `func.preconditions` formula. The v2 lane used to emit one
        // trivially-discharged Precondition VC per SIDE, double-counting each
        // `#[requires]` in the report. The production shape must yield exactly
        // ONE row per declared precondition (mirroring the `seen_posts` dedup
        // on the Ensures side).
        let mut func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);
        func.preconditions = vec![parse_spec_expr("x > 0").expect("spec should parse")];

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1, "one declared #[requires] must yield one Precondition VC");
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "contract_fn"));
        assert_eq!(vcs[0].formula, Formula::Bool(false));
        assert_eq!(
            vcs[0].contract_metadata.and_then(|metadata| metadata.source_contract_index),
            Some(0)
        );
    }

    #[test]
    fn test_lowered_compiler_requires_dedups_against_preconditions() {
        // Same dedup with the compiler-lowered spelling: the raw contract body
        // carries `LOWERED_CONTRACT_PREFIX` while the parsed `preconditions`
        // entry (via `normalized_contract_spec_body`) does not.
        let mut func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: format!("{LOWERED_CONTRACT_PREFIX}x > 0"),
        }]);
        func.preconditions = vec![parse_spec_expr("x > 0").expect("spec should parse")];

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { .. }));
    }

    #[test]
    fn test_non_contract_precondition_is_context_only() {
        // A `preconditions` entry with NO matching Requires provenance (the
        // synthetic type-range / `generate_vcs_with_extra_precondition` shape)
        // remains a body hypothesis but must not fabricate a definition-entry
        // bookkeeping row. Only the authored Requires owns such a row.
        let mut func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);
        func.preconditions = vec![
            parse_spec_expr("x > 0").expect("spec should parse"),
            parse_spec_expr("x <= 100").expect("spec should parse"),
        ];

        let vcs = crate::generate_vcs(&func);

        let precondition_rows =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count();
        assert_eq!(
            precondition_rows, 1,
            "only the authored Requires may emit a definition-entry row"
        );
    }

    #[test]
    fn test_ensures_generates_postcondition_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Postcondition));
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(parse_spec_expr("result >= 0").expect("spec should parse"))),
        );
    }

    #[test]
    fn test_invariant_generates_assertion_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Invariant,
            span: SourceSpan::default(),
            body: "n > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(
            matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "invariant: n > 0")
        );
        assert_eq!(
            vcs[0].formula,
            Formula::Not(Box::new(parse_spec_expr("n > 0").expect("spec should parse"))),
        );
    }

    // === Fail-closed UNKNOWN routing for un-encodable `#[ensures]` ===
    //
    // The ny-cert selfcheck postconditions (`check_entailment` / `check_chain` /
    // `check_farkas`) lower to Result-model predicates over SYNTHETIC spec-model
    // terms (`_0_discr`, `_0_value*`, `*_sign`, `.__trust_ok_i`) that no body
    // fact grounds. The old encoding emitted the refutable `Not(post)` whose
    // negation is satisfiable by havoc — reported Failed with a counterexample
    // minted over the under-constrained encoding, NOT a program trace. These
    // tests pin the soundness-restoring routing: such an ensures lands as ONE
    // non-refutable `UnsupportedMir` row that preclassifies to Unknown — never
    // Failed-with-spurious-cex, never Proved, never silently dropped.

    fn spec_model_unknown_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
        vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_MODEL_UNGROUNDED_KIND)
            })
            .collect()
    }

    #[test]
    fn ny_farkas_style_ensures_lands_unknown_not_refutable() {
        // Compiler-lowered text of ny-cert `check_farkas`'s
        // `#[ensures(|r: &Result<Rat, CheckError>| !matches!(r, Ok(c) if c.is_positive()))]`.
        // It PARSES (into `_0_discr` / `_0_value_sign` atoms) but cannot be
        // grounded: `Rat` is an opaque interned handle, so the sign term has no
        // MIR carrier and the discriminant term is never linked to `_0`.
        let body = "!((result.is_ok()) && (result.unwrap().is_positive()))";
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: body.to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "an ungrounded ensures must not emit a refutable Postcondition VC: {vcs:#?}"
        );
        let rows = spec_model_unknown_rows(&vcs);
        assert_eq!(rows.len(), 1, "exactly one fail-closed row (never dropped): {vcs:#?}");
        let VcKind::UnsupportedMir { detail, .. } = &rows[0].kind else { unreachable!() };
        assert!(
            detail.contains("_0_discr") && detail.contains("_0_value_sign"),
            "the row must name the ungrounded model terms: {detail}"
        );

        // Verdict routing: preclassified to Unknown, never solver-dispatched —
        // so it can never come back as Failed (SAT) or Proved (UNSAT).
        let (solver_vcs, preclassified) = crate::generate_vcs_with_discharge(&func);
        assert!(
            !solver_vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)
                || matches!(vc.kind, VcKind::UnsupportedMir { .. })),
            "the fail-closed row must not reach a solver: {solver_vcs:#?}"
        );
        assert!(
            preclassified.iter().any(|(vc, result)| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_MODEL_UNGROUNDED_KIND)
                    && matches!(result, trust_types::VerificationResult::Unknown { .. })
            }),
            "the ensures must land as a preclassified UNKNOWN: {preclassified:#?}"
        );
    }

    #[test]
    fn ny_entailment_style_tuple_ensures_lands_unknown_not_refutable() {
        // Compiler-lowered text of ny-cert `check_entailment`/`check_chain`'s
        // `#[ensures(|r: &Result<(Rat, Rat), CheckError>| !matches!(r, Ok((d, c)) if d > c))]`.
        // The tuple binds become `.__trust_ok_i` projections of the Ok payload
        // (`Rat` arena handles — comparing them as Ints would be unsound), so
        // the predicate is un-groundable and must land UNKNOWN.
        let body = "!((result.is_ok()) && \
                    ((result.unwrap().__trust_ok_0) > (result.unwrap().__trust_ok_1)))";
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: body.to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "an ungrounded tuple ensures must not emit a refutable Postcondition VC: {vcs:#?}"
        );
        let rows = spec_model_unknown_rows(&vcs);
        assert_eq!(rows.len(), 1, "exactly one fail-closed row: {vcs:#?}");
        let VcKind::UnsupportedMir { detail, .. } = &rows[0].kind else { unreachable!() };
        assert!(
            detail.contains("__trust_ok_0") && detail.contains("__trust_ok_1"),
            "the row must name the ungrounded payload binds: {detail}"
        );
    }

    #[test]
    fn mixed_grounded_and_ungrounded_ensures_split() {
        // A groundable ensures keeps its body-aware Postcondition VC; the
        // ungrounded one becomes exactly one Unknown row; and NO emitted VC may
        // leak a free synthetic spec-model variable (a refutable
        // under-constrained encoding).
        let func = contract_test_function(vec![
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "!((result.is_ok()) && (result.unwrap().is_positive()))".to_string(),
            },
        ]);

        let vcs = crate::generate_vcs(&func);
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "the groundable ensures must keep its Postcondition VC: {vcs:#?}"
        );
        assert_eq!(spec_model_unknown_rows(&vcs).len(), 1);
        for vc in &vcs {
            assert!(
                ungrounded_spec_model_vars(&vc.formula).is_empty(),
                "no emitted VC may leak ungrounded spec-model terms: {vc:#?}"
            );
        }
    }

    #[test]
    fn ungrounded_ensures_in_contracts_and_spec_emits_one_row() {
        // The real extraction pipeline mirrors every contract into
        // `FunctionSpec`, so BOTH `check_contracts` and `generate_spec_vcs`
        // see the same ensures. The v2 contract lane must de-duplicate their
        // fail-closed rows to exactly one (never zero — that would drop the
        // obligation; never two — that would double-report it).
        let body = "!((result.is_ok()) && (result.unwrap().is_positive()))";
        let mut func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: body.to_string(),
        }]);
        func.spec = trust_types::FunctionSpec {
            requires: vec![],
            ensures: vec![body.to_string()],
            invariants: vec![],
        };

        let vcs = crate::generate_vcs(&func);
        assert_eq!(
            spec_model_unknown_rows(&vcs).len(),
            1,
            "contracts-lane + spec-lane rows for the SAME ensures must dedup to one: {vcs:#?}"
        );
        assert!(!vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)));
    }

    #[test]
    fn unparseable_ensures_lands_unknown_not_failed() {
        // The RAW (unlowered) ny spec-closure text does not tokenize (`|`,
        // `&`, `matches!`). It must land as the fail-closed NON-REFUTABLE
        // Unknown row — not the always-SAT "unverifiable spec" Assertion
        // (reported Failed) — and never be dropped. Other unelaborated contract
        // kinds use the generic non-refutable Unknown row.
        let body = "|r: &Result<(Rat, Rat), CheckError>| !matches!(r, Ok((d, c)) if d > c)";
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: body.to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);
        assert_eq!(vcs.len(), 1, "unparseable ensures must emit exactly one VC: {vcs:#?}");
        assert!(
            matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
                if kind == SPEC_ENSURES_UNPARSEABLE_KIND),
            "unparseable ensures must be the fail-closed Unknown shape: {:?}",
            vcs[0].kind
        );

        let (solver_vcs, preclassified) = crate::generate_vcs_with_discharge(&func);
        assert!(solver_vcs.is_empty(), "nothing to solve: {solver_vcs:#?}");
        assert!(
            matches!(
                preclassified.as_slice(),
                [(_, trust_types::VerificationResult::Unknown { .. })]
            ),
            "unparseable ensures must preclassify to UNKNOWN: {preclassified:#?}"
        );
    }

    #[test]
    fn spec_model_var_name_shape_is_precise() {
        // Positives: exactly the synthetic names spec_parse mints (plus their
        // projections / version tokens). A false positive is drop-only (routes
        // to Unknown — sound); a false negative keeps the refutable encoding,
        // so the positive set must cover every minted shape.
        for name in [
            "_0_discr",
            "result_discr",
            "_0_value",
            "_0_value_sign",
            "_0_value.__trust_ok_0",
            "c_sign",
            "_0_discr#s1_0",
            "my_value",
        ] {
            assert!(is_spec_model_var(name), "{name} must classify as a spec-model term");
        }
        // Negatives: ordinary locals, params, field projections (`p.value` is
        // the FIELD-projection spec var, grounded by MIR Adt-field extraction),
        // and near-miss suffixes.
        for name in ["_0", "x", "arr_len", "design", "signal", "discriminant", "p.value", "x_signs"]
        {
            assert!(!is_spec_model_var(name), "{name} must NOT classify as a spec-model term");
        }
    }

    #[test]
    fn test_unparseable_spec_fails_closed() {
        // an unparseable spec must NOT be silently dropped
        // (dropping it would let the function aggregate to `proved` without the
        // spec ever being checked — a false-PROVE). It fails closed as exactly
        // one non-refutable UnsupportedMir row (preclassified Unknown).
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "???".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1, "unparseable spec must emit a fail-closed VC, not be dropped");
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, detail }
            if kind == SPEC_UNVERIFIABLE_KIND && detail.contains("unverifiable source specification")));
        assert_eq!(vcs[0].formula, Formula::Bool(true));

        let (solver_vcs, preclassified) = crate::generate_vcs_with_discharge(&func);
        assert!(solver_vcs.is_empty(), "encoding gaps are never solver-dispatched");
        assert!(matches!(
            preclassified.as_slice(),
            [(_, trust_types::VerificationResult::Unknown { .. })]
        ));
    }

    #[test]
    fn test_unparseable_loop_invariant_fails_closed() {
        // A loop invariant that cannot be parsed must remain visible as the
        // loop lane's fail-closed Unknown row.
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "bb1: ???".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1, "unparseable loop invariant must fail closed, not vanish");
        // The dedicated E4 loop lane owns this row and stamps its own
        // `UnsupportedMir` family tag; the shape stays non-refutable
        // (`Bool(true)` can never be reported as a proof).
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
            if kind == LOOP_CONTRACT_UNSUPPORTED_KIND));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_unparseable_type_refinement_fails_closed() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::TypeRefinement,
            span: SourceSpan::default(),
            body: "x: ???".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1, "unparseable type refinement must fail closed, not vanish");
        assert!(matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
            if kind == SPEC_UNVERIFIABLE_KIND));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_loop_invariant_without_real_header_fails_closed() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "bb1: x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, .. } if kind == LOOP_CONTRACT_UNSUPPORTED_KIND
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    #[test]
    fn test_multiple_contracts() {
        let func = contract_test_function(vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= 0".to_string(),
            },
        ]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 2);
        assert_eq!(
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count(),
            1
        );
        assert_eq!(vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).count(), 1);
    }

    // trust_wp contract extension tests.

    #[test]
    fn test_loop_invariant_cannot_claim_a_nonexistent_header() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "bb1: x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }));
    }

    #[test]
    fn test_loop_invariant_has_no_default_block() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }));
    }

    #[test]
    fn exact_feedback_candidate_strengthens_only_the_explicit_second_pass() {
        let func = feedback_loop_function();
        let mut first_pass = Vec::new();
        check_contracts(&func, &mut first_pass);
        let (initiation, consecution) = e4_pair(&first_pass);

        let feedback = loop_invariant_feedback_candidate(&func, &initiation, &consecution)
            .expect("the exact production E4 pair should validate");
        assert_eq!(feedback.header_block(), 1);
        assert_eq!(feedback.source_text(), "n <= 10 && i <= 10");

        let replacement = regenerate_loop_decreases_with_invariant_feedback_vcs(
            &func,
            std::slice::from_ref(&feedback),
        );
        assert_eq!(replacement.len(), 1, "the narrow public lane emits only E5 rows");

        let mut second_pass = Vec::new();
        check_contracts_with_loop_invariant_feedback(
            &func,
            &mut second_pass,
            std::slice::from_ref(&feedback),
        );

        let predicate = type_and_validate_loop_formula(
            &func,
            parse_spec_expr("n <= 10 && i <= 10").expect("predicate parses"),
            Sort::Bool,
        )
        .expect("predicate types");
        assert!(
            !formula_contains(&e5_formula(&first_pass), &predicate),
            "the first-pass E5 VC must not assume an authored invariant"
        );
        assert!(
            formula_contains(&e5_formula(&replacement), &predicate),
            "the explicit second-pass E5 VC must assume the same-header invariant"
        );
        assert_eq!(e5_formula(&replacement), e5_formula(&second_pass));

        // Feedback changes no obligation cardinality and never rewrites its own
        // proof premises.  Only downstream formulas may be replaced/re-solved.
        assert_eq!(first_pass.len(), second_pass.len());
        let (second_init, second_step) = e4_pair(&second_pass);
        assert_eq!(initiation.formula, second_init.formula);
        assert_eq!(consecution.formula, second_step.formula);
    }

    #[test]
    fn feedback_candidate_accepts_only_exact_production_interval_augmentation() {
        let func = feedback_loop_function();
        let mut raw = Vec::new();
        check_contracts(&func, &mut raw);
        let (raw_initiation, raw_consecution) = e4_pair(&raw);

        let (solver_vcs, discharged) = crate::generate_vcs_with_discharge(&func);
        let mut production = solver_vcs;
        production.extend(discharged.into_iter().map(|(vc, _)| vc));
        let (initiation, consecution) = e4_pair(&production);

        let environment = crate::abstract_interp::merged_interval_environment(&func);
        let augmented_initiation =
            crate::abstract_interp::augment_vc_with_abstract_state(&raw_initiation, &environment);
        let augmented_consecution =
            crate::abstract_interp::augment_vc_with_abstract_state(&raw_consecution, &environment);
        assert!(
            exact_loop_invariant_vc_eq(&initiation, &raw_initiation)
                || exact_loop_invariant_vc_eq(&initiation, &augmented_initiation)
        );
        assert!(
            exact_loop_invariant_vc_eq(&consecution, &raw_consecution)
                || exact_loop_invariant_vc_eq(&consecution, &augmented_consecution)
        );
        assert!(
            !exact_loop_invariant_vc_eq(&initiation, &raw_initiation)
                || !exact_loop_invariant_vc_eq(&consecution, &raw_consecution),
            "the fixture must exercise the production abstract-state wrapper"
        );

        assert!(
            loop_invariant_feedback_candidate(&func, &initiation, &consecution).is_some(),
            "the exact production-shaped E4 pair should validate"
        );

        let mut forged_initiation = raw_initiation;
        forged_initiation.formula =
            Formula::And(vec![Formula::Bool(false), forged_initiation.formula.clone()]);
        assert!(
            loop_invariant_feedback_candidate(&func, &forged_initiation, &consecution).is_none(),
            "an arbitrary environment wrapper must be rejected"
        );
    }

    #[test]
    fn e5_production_variants_match_dispatch_and_sanitize_contract_arithmetic() {
        let func = feedback_loop_function();
        let (raw, augmented) =
            crate::regenerate_loop_decreases_with_invariant_feedback_production_variants(
                &func,
                &[],
            )
            .expect("exact production E5 variants");
        assert_eq!(raw.len(), 1);
        assert_eq!(augmented.len(), raw.len());

        let (solver_vcs, discharged) = crate::generate_vcs_with_discharge(&func);
        let production_e5 = solver_vcs
            .iter()
            .chain(discharged.iter().map(|(vc, _)| vc))
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::NonTermination { context, .. } if context == "loop-decreases"
                )
            })
            .expect("production E5 row");
        let exact_vc = |left: &VerificationCondition, right: &VerificationCondition| {
            serde_json::to_string(left).expect("left VC serializes")
                == serde_json::to_string(right).expect("right VC serializes")
        };
        assert!(
            exact_vc(production_e5, &raw[0]) || exact_vc(production_e5, &augmented[0]),
            "the helper must reconstruct the exact raw/augmented production carrier",
        );

        // This authored fixed-width arithmetic is deliberately unsafe to use
        // as an Int premise.  The public E5 reconstruction boundary must see
        // the same sanitized function view as ordinary VC generation.
        let mut arithmetic_poisoned = func;
        arithmetic_poisoned.preconditions.push(Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
        ));
        let poisoned_variants =
            crate::regenerate_loop_decreases_with_invariant_feedback_production_variants(
                &arithmetic_poisoned,
                &[],
            )
            .expect("unsafe authored arithmetic is dropped, not consumed");
        assert_eq!(
            serde_json::to_string(&poisoned_variants).expect("poisoned variants serialize"),
            serde_json::to_string(&(raw, augmented)).expect("baseline variants serialize"),
            "unmodeled contract arithmetic must not alter E5 raw rows or interval assumptions",
        );

        // The sanitization projection is not source drift. An exact E4 candidate
        // remains sealed to the complete original payload while reconstruction
        // uses the same sanitized interval environment as production.
        let (poisoned_solver, poisoned_discharged) =
            crate::generate_vcs_with_discharge(&arithmetic_poisoned);
        let mut poisoned_production = poisoned_solver;
        poisoned_production.extend(poisoned_discharged.into_iter().map(|(vc, _)| vc));
        let (poisoned_initiation, poisoned_consecution) = e4_pair(&poisoned_production);
        let feedback = loop_invariant_feedback_candidate(
            &arithmetic_poisoned,
            &poisoned_initiation,
            &poisoned_consecution,
        )
        .expect("exact production E4 pair survives the arithmetic-safety projection");
        let (feedback_raw, feedback_augmented) =
            crate::regenerate_loop_decreases_with_invariant_feedback_production_variants(
                &arithmetic_poisoned,
                std::slice::from_ref(&feedback),
            )
            .expect("fresh-context feedback reconstruction");
        let predicate = type_and_validate_loop_formula(
            &arithmetic_poisoned,
            parse_spec_expr("n <= 10 && i <= 10").expect("predicate parses"),
            Sort::Bool,
        )
        .expect("predicate types");
        assert!(formula_contains(&e5_formula(&feedback_raw), &predicate));
        assert!(formula_contains(&e5_formula(&feedback_augmented), &predicate));
    }

    #[test]
    fn u8_wraparound_arithmetic_cannot_enter_e4_or_feedback() {
        fn assert_no_e4(func: &VerifiableFunction, context: &str) {
            let mut vcs = Vec::new();
            check_contracts(func, &mut vcs);
            assert!(
                !vcs.iter().any(|vc| matches!(
                    vc.kind,
                    VcKind::LoopInvariantInitiation { .. }
                        | VcKind::LoopInvariantConsecution { .. }
                )),
                "{context}: fixed-width arithmetic must not mint an E4 pair: {vcs:#?}"
            );
            assert!(
                vcs.iter().any(|vc| {
                    matches!(vc.kind, VcKind::UnsupportedMir { .. })
                        && vc.formula == Formula::Bool(true)
                }),
                "{context}: rejection must remain an explicit fail-closed row"
            );
        }

        let mut authored = feedback_loop_function();
        authored.body.locals[1].ty = Ty::u8();
        authored.body.locals[2].ty = Ty::u8();
        authored.contracts[0].body = "bb1: i + 1 > i".to_string();
        assert_no_e4(&authored, "the mathematical claim `i + 1 > i` is false at u8::MAX");

        let mut transition = feedback_loop_function();
        transition.body.locals[1].ty = Ty::u8();
        transition.body.locals[2].ty = Ty::u8();
        transition.body.blocks[2].stmts = vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        }];
        assert_no_e4(
            &transition,
            "a wrapping u8 loop transition cannot be modeled as unbounded addition",
        );

        let mut precondition = feedback_loop_function();
        precondition.body.locals[1].ty = Ty::u8();
        precondition.body.locals[2].ty = Ty::u8();
        let quantified = Symbol::intern("quantified_machine_value");
        precondition.preconditions = vec![Formula::Forall(
            vec![(quantified, Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Add(
                    Box::new(Formula::SymVar(quantified, Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
                Box::new(Formula::SymVar(quantified, Sort::Int)),
            )),
        )];
        assert_no_e4(
            &precondition,
            "bound arithmetic cannot smuggle Int semantics into E4 through a precondition",
        );

        let mut symbolic = feedback_loop_function();
        symbolic.body.blocks[2].stmts = vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Symbolic(Formula::Add(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            ))),
            span: SourceSpan::default(),
        }];
        assert_no_e4(
            &symbolic,
            "a symbolic operand cannot bypass the reviewed transition operators",
        );

        let mut opaque = feedback_loop_function();
        opaque.body.blocks[2].stmts = vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::OpaqueScalar {
                width: 32,
                signed: false,
            })),
            span: SourceSpan::default(),
        }];
        assert_no_e4(&opaque, "an opaque scalar cannot become an exact loop-transition value");

        let mut signed_switch = feedback_loop_function();
        signed_switch.body.locals[1].ty = Ty::i8();
        signed_switch.body.locals[2].ty = Ty::i8();
        signed_switch.body.blocks[1].stmts.clear();
        signed_switch.body.blocks[1].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: vec![(u128::from(u8::MAX), BlockId(2))],
            otherwise: BlockId(3),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        assert_no_e4(&signed_switch, "signed SwitchInt targets require width-aware decoding");

        for (ty, op, context) in [
            (Ty::u8(), BinOp::Shl, "a u8 shift is not an exact Int transition"),
            (Ty::usize(), BinOp::Shr, "a pointer-width shift is not an exact Int transition"),
        ] {
            let mut shift = feedback_loop_function();
            shift.body.locals[1].ty = ty.clone();
            shift.body.locals[2].ty = ty;
            shift.body.blocks[2].stmts = vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    op,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(ConstValue::Int(8)),
                ),
                span: SourceSpan::default(),
            }];
            assert_no_e4(&shift, context);
        }

        for (ty, context) in [
            (Ty::u8(), "u8 bitwise Not must not become Boolean Not"),
            (Ty::isize(), "pointer-width integer Not must fail closed"),
        ] {
            let mut bit_not = feedback_loop_function();
            bit_not.body.locals[1].ty = ty.clone();
            bit_not.body.locals[2].ty = ty;
            bit_not.body.blocks[2].stmts = vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            }];
            assert_no_e4(&bit_not, context);
        }

        let bool_not = feedback_loop_function();
        let bool_state = initial_symbolic_state(&bool_not);
        assert_eq!(
            symbolic_rvalue(
                &bool_not,
                &Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(3))),
                &bool_state,
                None,
            ),
            Some(Formula::Not(Box::new(Formula::Var("cond".to_string(), Sort::Bool)))),
            "Boolean Not remains in the exact transition fragment",
        );
    }

    fn u8_contract_arithmetic_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "u8_contract_arithmetic".to_string(),
            def_path: "test::u8_contract_arithmetic".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u8(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 8)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u8(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn formula_only_preconditions_strengthen_body_without_fabricating_entry_rows() {
        let x = || Formula::Var("x".into(), Sort::Int);
        let type_range = Formula::And(vec![
            Formula::Ge(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(x()), Box::new(Formula::Int(u8::MAX.into()))),
        ]);
        let mut synthetic = u8_contract_arithmetic_function();
        synthetic.preconditions.push(type_range.clone());
        let synthetic_vcs = crate::generate_vcs(&synthetic);
        assert!(
            !synthetic_vcs.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })),
            "a compiler type invariant has no authored Requires identity: {synthetic_vcs:#?}",
        );
        let synthetic_overflow = synthetic_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("the body still has its overflow obligation");
        assert!(
            formula_contains(&synthetic_overflow.formula, &type_range),
            "the synthetic fact must remain in the body context: {synthetic_overflow:#?}",
        );

        let inferred = Formula::Le(Box::new(x()), Box::new(Formula::Int(254)));
        let strengthened = crate::generate_vcs_with_extra_precondition(
            &u8_contract_arithmetic_function(),
            &inferred,
        );
        assert!(
            !strengthened.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })),
            "an inferred hypothesis is proved by its separate caller gate, not a vacuous self row",
        );
        let strengthened_overflow = strengthened
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("the strengthened body still has its overflow obligation");
        assert!(
            formula_contains(&strengthened_overflow.formula, &inferred),
            "the extra precondition must still strengthen the target body VC: {strengthened_overflow:#?}",
        );
    }

    #[test]
    fn nested_neg_integer_literals_use_checked_constant_semantics() {
        let nested = Formula::Neg(Box::new(Formula::Neg(Box::new(Formula::Int(7)))));
        assert_eq!(formula_integer_literal(&nested), Some(7));
        assert!(
            !formula_uses_unmodeled_machine_arithmetic(&nested),
            "nested literal negation is a checked constant, not a machine operation",
        );

        let overflowing = Formula::Neg(Box::new(Formula::Int(i128::MIN)));
        assert_eq!(formula_integer_literal(&overflowing), None);
        assert!(
            formula_uses_unmodeled_machine_arithmetic(&overflowing),
            "an overflowing literal negation must not be folded or admitted",
        );

        let symbolic = Formula::Neg(Box::new(Formula::Var("x".into(), Sort::Int)));
        assert!(
            formula_uses_unmodeled_machine_arithmetic(&symbolic),
            "symbolic negation remains fixed-width machine arithmetic",
        );
    }

    #[test]
    fn ordinary_u8_contract_arithmetic_is_unknown_and_never_assumed() {
        let requires = parse_spec_expr("x + 1 <= 255").expect("requires parses");
        let mut baseline = u8_contract_arithmetic_function();
        let baseline_vcs = crate::generate_vcs(&baseline);
        let baseline_overflow = baseline_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("u8 add has an overflow obligation")
            .formula
            .clone();

        baseline.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "x + 1 <= 255".to_string(),
        });
        baseline.preconditions.push(requires);
        baseline.spec.requires.push("x + 1 <= 255".to_string());
        let vcs = crate::generate_vcs(&baseline);

        let overflow = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("unsafe requires must not suppress the body overflow");
        assert_eq!(
            overflow.formula, baseline_overflow,
            "the wrapping Requires must never be admitted as a body assumption",
        );
        let unknowns: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_UNVERIFIABLE_KIND)
            })
            .collect();
        assert_eq!(unknowns.len(), 1, "mirrored Requires yields one visible Unknown: {vcs:#?}");
        assert_eq!(unknowns[0].formula, Formula::Bool(true));
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })),
            "unsafe Requires must not retain a trivially-Proved bookkeeping row",
        );

        let ensures = parse_spec_expr("result + 1 > result").expect("ensures parses");
        let mut post = u8_contract_arithmetic_function();
        post.body.blocks[0].stmts = vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(u8::MAX.into(), 8))),
            span: SourceSpan::default(),
        }];
        post.contracts.push(Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result + 1 > result".to_string(),
        });
        post.postconditions.push(ensures);
        post.spec.ensures.push("result + 1 > result".to_string());
        let post_vcs = crate::generate_vcs(&post);
        // Machine{w} lane (ratified L1 rule 4): the u8 clause is admitted as a
        // REFUTABLE row in the declared-width wrapping reading — `bvadd(255,1)
        // = 0` keeps `¬(result + 1 > result)` satisfiable, so the false clause
        // is refuted honestly instead of parked as Unknown. The protected
        // invariant is unchanged and pinned structurally: the row must carry
        // NO mathematical-integer arithmetic (the `Int` tautology reading that
        // would have PROVED the false clause) and must wrap at width 8.
        let post_rows: Vec<_> = post_vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
            .collect();
        assert_eq!(
            post_rows.len(),
            1,
            "the u8 clause enters the refutable machine lane exactly once: {post_vcs:#?}",
        );
        let mut int_arith = 0_usize;
        let mut declared_width_adds = 0_usize;
        post_rows[0].formula.visit(&mut |f| {
            int_arith += usize::from(matches!(
                f,
                Formula::Add(..)
                    | Formula::Sub(..)
                    | Formula::Mul(..)
                    | Formula::Div(..)
                    | Formula::Rem(..)
                    | Formula::Neg(..)
            ));
            declared_width_adds += usize::from(matches!(f, Formula::BvAdd(_, _, 8)));
        });
        assert_eq!(
            int_arith, 0,
            "the Int tautology reading must never survive: {:?}",
            post_rows[0].formula,
        );
        assert!(
            declared_width_adds >= 1,
            "the clause `+` must wrap at the DECLARED width 8: {:?}",
            post_rows[0].formula,
        );
        assert!(
            !post_vcs.iter().any(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_UNVERIFIABLE_KIND)
            }),
            "an admitted clause does not also keep a fail-closed row: {post_vcs:#?}",
        );
    }

    #[test]
    fn dropped_arithmetic_precondition_cannot_authorize_signed_zero_subtraction() {
        let x = || Formula::Var("x".into(), Sort::Int);
        let lower_bound = Formula::Gt(
            Box::new(x()),
            Box::new(Formula::Neg(Box::new(Formula::Int(2_147_483_648)))),
        );
        let wrapping_tautology = Formula::Gt(
            Box::new(Formula::Add(Box::new(x()), Box::new(Formula::Int(1)))),
            Box::new(x()),
        );
        let requires = Formula::And(vec![lower_bound, wrapping_tautology]);
        let ensures = Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Sub(Box::new(Formula::Int(0)), Box::new(x()))),
        );

        let mut func = contract_test_function(vec![]);
        func.body.locals[0].ty = Ty::i32();
        func.body.locals[0].name = Some("_0".into());
        func.body.locals[1].ty = Ty::i32();
        func.body.return_ty = Ty::i32();
        func.preconditions.push(requires);
        func.postconditions.push(ensures.clone());

        assert!(
            formula_uses_unmodeled_machine_arithmetic_in_function(&func, &ensures),
            "a useful bound inside a dropped arithmetic conjunction must not authorize `0 - x`",
        );
        let vcs = crate::generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "the unauthorized signed subtraction must never reach a solver-capable postcondition: {vcs:#?}",
        );
        let unknowns: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_UNVERIFIABLE_KIND)
            })
            .collect();
        assert_eq!(
            unknowns.len(),
            2,
            "both formula-only clauses rejected by sanitization must remain visible: {vcs:#?}",
        );
        assert!(unknowns.iter().all(|vc| vc.formula == Formula::Bool(true)));
    }

    #[test]
    fn formula_only_arithmetic_contract_carriers_remain_visible() {
        let mut func = u8_contract_arithmetic_function();
        func.preconditions.push(parse_spec_expr("x + 1 <= 255").expect("requires parses"));
        func.postconditions.push(parse_spec_expr("result + 1 > result").expect("ensures parses"));

        let vcs = crate::generate_vcs(&func);
        let unknowns: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind == SPEC_UNVERIFIABLE_KIND)
            })
            .collect();
        assert_eq!(
            unknowns.len(),
            2,
            "formula-only Requires and Ensures must not disappear during sanitization: {vcs:#?}",
        );
        assert!(unknowns.iter().all(|vc| vc.formula == Formula::Bool(true)));
        assert!(
            !vcs.iter().any(|vc| {
                matches!(vc.kind, VcKind::Precondition { .. } | VcKind::Postcondition)
            }),
            "rejected formula-only clauses must have no solver-capable contract row",
        );
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
            "the removed Requires must not suppress the body overflow",
        );
    }

    #[test]
    fn feedback_validation_surface_has_no_caller_supplied_authority_callback() {
        let func = feedback_loop_function();
        let mut vcs = Vec::new();
        check_contracts(&func, &mut vcs);
        let (initiation, consecution) = e4_pair(&vcs);

        let validator: fn(
            &VerifiableFunction,
            &VerificationCondition,
            &VerificationCondition,
        ) -> Option<LoopInvariantFeedbackCandidate> = loop_invariant_feedback_candidate;
        assert!(validator(&func, &initiation, &consecution).is_some());
    }

    #[test]
    fn feedback_candidate_rejects_cross_function_or_formula_drift() {
        let func = feedback_loop_function();
        let mut vcs = Vec::new();
        check_contracts(&func, &mut vcs);
        let (initiation, consecution) = e4_pair(&vcs);

        let mut wrong_function = consecution.clone();
        wrong_function.function = Symbol::intern("other::feedback_loop");
        assert!(loop_invariant_feedback_candidate(&func, &initiation, &wrong_function).is_none());

        let mut wrong_formula = consecution.clone();
        wrong_formula.formula = Formula::Bool(false);
        assert!(
            loop_invariant_feedback_candidate(&func, &initiation, &wrong_formula).is_none(),
            "a display-identical row with different semantics must not bind"
        );

        let mut wrong_header = consecution;
        let VcKind::LoopInvariantConsecution { header_block, .. } = &mut wrong_header.kind else {
            unreachable!()
        };
        *header_block = 2;
        assert!(
            loop_invariant_feedback_candidate(&func, &initiation, &wrong_header).is_none(),
            "a proof for another loop header must not bind"
        );
    }

    #[test]
    fn feedback_candidate_cannot_leak_across_def_path_or_source_drift() {
        let func = feedback_loop_function();
        let mut first_pass = Vec::new();
        check_contracts(&func, &mut first_pass);
        let (initiation, consecution) = e4_pair(&first_pass);
        let feedback = loop_invariant_feedback_candidate(&func, &initiation, &consecution)
            .expect("exact production pair");

        let mut other = func.clone();
        other.def_path = "other::feedback_loop".to_string();
        let mut other_vcs = Vec::new();
        check_contracts_with_loop_invariant_feedback(
            &other,
            &mut other_vcs,
            std::slice::from_ref(&feedback),
        );
        let predicate = feedback.predicate.clone();
        assert!(
            !formula_contains(&e5_formula(&other_vcs), &predicate),
            "same display name/header in another function must not inherit P"
        );

        let mut drifted = func.clone();
        drifted.contracts[0].span.line_start += 1;
        let mut drifted_vcs = Vec::new();
        check_contracts_with_loop_invariant_feedback(
            &drifted,
            &mut drifted_vcs,
            std::slice::from_ref(&feedback),
        );
        assert!(
            !formula_contains(&e5_formula(&drifted_vcs), &predicate),
            "a stale feedback candidate must not survive source-clause drift"
        );

        let mut body_drifted = func.clone();
        let Statement::Assign { rvalue, .. } = &mut body_drifted.body.blocks[0].stmts[0] else {
            unreachable!("fixture preheader initializes n")
        };
        *rvalue = Rvalue::Use(Operand::Constant(ConstValue::Int(11)));
        let mut body_drifted_vcs = Vec::new();
        check_contracts_with_loop_invariant_feedback(
            &body_drifted,
            &mut body_drifted_vcs,
            std::slice::from_ref(&feedback),
        );
        assert!(
            !formula_contains(&e5_formula(&body_drifted_vcs), &predicate),
            "a stale feedback candidate must not survive a changed function body even when path/header/source text are unchanged",
        );
    }

    #[test]
    fn test_type_refinement_generates_vc() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::TypeRefinement,
            span: SourceSpan::default(),
            body: "x: x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::TypeRefinementViolation { variable, predicate }
                if variable == "x" && predicate == "x > 0"
        ));
    }

    #[test]
    fn test_modifies_generates_frame_vcs() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::Modifies,
            span: SourceSpan::default(),
            body: "x".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        // "x" is in modifies set, so no frame VC for x.
        // The function has local "x" (index 1) and unnamed _0 (index 0).
        // Only named locals not in modifies set get frame VCs.
        assert!(vcs.is_empty(), "x is in modifies set, no frame VCs expected");
    }

    #[test]
    fn test_modifies_generates_frame_vc_for_unmodified() {
        // Function with two named locals: x and y, modifies only x.
        let func = VerifiableFunction {
            name: "contract_fn".to_string(),
            def_path: "test::contract_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("y".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![Contract {
                kind: ContractKind::Modifies,
                span: SourceSpan::default(),
                body: "x".to_string(),
            }],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = crate::generate_vcs(&func);

        // y is not in modifies set, so it gets a frame condition VC.
        let frame_vcs: Vec<_> = vcs.iter()
            .filter(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { variable, .. } if variable == "y"))
            .collect();
        assert_eq!(frame_vcs.len(), 1, "should have 1 frame VC for y");
    }

    #[test]
    fn test_modifies_frame_vc_uses_local_sort() {
        // Trust #integrity regression: a bool local's frame VC must carry the
        // local's real sort (Bool), never a hardcoded Int. An ill-typed Int frame
        // check `NOT(old == new)` over a bool can suppress a real frame violation
        // (a frame/modifies false-PROVE).
        let func = VerifiableFunction {
            name: "contract_fn".to_string(),
            def_path: "test::contract_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::usize(),
            },
            contracts: vec![Contract {
                kind: ContractKind::Modifies,
                span: SourceSpan::default(),
                body: "x".to_string(),
            }],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = crate::generate_vcs(&func);
        let frame_vc = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::FrameConditionViolation { variable, .. } if variable == "ok"))
            .expect("bool local `ok` (not in modifies set) should get a frame VC");
        let Formula::Not(eq) = &frame_vc.formula else {
            panic!("frame VC should be a negated equality, got {:?}", frame_vc.formula);
        };
        let Formula::Eq(old, new) = eq.as_ref() else {
            panic!("frame VC should compare old and new values");
        };
        for (label, operand) in [("old", old.as_ref()), ("new", new.as_ref())] {
            let Formula::Var(_, sort) = operand else {
                panic!("frame VC {label} operand should be a Var, got {operand:?}");
            };
            assert_eq!(
                *sort,
                trust_types::Sort::Bool,
                "frame VC {label} var for a bool local must use Sort::Bool, not {sort:?}"
            );
        }
    }

    #[test]
    fn test_parse_loop_invariant_body() {
        let (block, expr) = loop_contract_body("bb3: i < n").expect("paired loop clause");
        assert_eq!(block, 3);
        assert_eq!(expr, "i < n");

        assert!(
            loop_contract_body("x > 0").is_none(),
            "an unpaired clause must not inherit a default/stale block identity"
        );
    }

    #[test]
    fn test_parse_refinement_body() {
        let (var, pred) = parse_refinement_body("x: x > 0");
        assert_eq!(var, "x");
        assert_eq!(pred, "x > 0");

        let (var, pred) = parse_refinement_body("x > 0");
        assert_eq!(var, "v");
        assert_eq!(pred, "x > 0");
    }

    #[test]
    fn test_parse_modifies_body() {
        let vars = parse_modifies_body("x, y, z");
        assert_eq!(vars, vec!["x", "y", "z"]);

        let vars = parse_modifies_body("x");
        assert_eq!(vars, vec!["x"]);

        let vars = parse_modifies_body("");
        assert!(vars.is_empty());
    }

    #[test]
    fn test_trust_wp_vcs_have_contract_metadata() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        for vc in &vcs {
            assert!(vc.contract_metadata.is_some(), "trust-wp VCs should have contract metadata");
        }
    }

    #[test]
    fn test_unpaired_loop_invariant_is_never_l1_proof_credit() {
        let func = contract_test_function(vec![Contract {
            kind: ContractKind::LoopInvariant,
            span: SourceSpan::default(),
            body: "x > 0".to_string(),
        }]);

        let vcs = crate::generate_vcs(&func);

        assert!(matches!(vcs[0].kind, VcKind::UnsupportedMir { .. }));
    }
}

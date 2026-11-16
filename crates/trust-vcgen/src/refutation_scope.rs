//! Reject-only dependency accounting for generic solver counterexamples.
//!
//! A body VC can over-approximate loop state when an authored loop contract
//! cannot be modeled, or when a modeled transition explicitly leaves a call
//! result or nested-loop value unconstrained. SAT then witnesses the formula,
//! not an execution. This
//! scope never certifies fidelity, inserts an invariant, changes a formula, or
//! grants proof authority. It only tells the generic bidirectional bridge when
//! to withhold a counterexample. Independently grounded refute-only producers
//! do not consume this scope.

use std::collections::{BTreeMap, BTreeSet};

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    Formula, ObligationWrapper, Operand, PathGuardTerm, Place, Projection, Rvalue, SourceSpan,
    Statement, Symbol, Terminator, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

const MAX_BLOCKS: usize = 256;
const MAX_LOCALS: usize = 512;
const MAX_STATEMENTS: usize = 4096;
const MAX_FORMULA_NODES: usize = 16_384;
/// S2: how many passes over the body the shallow walk makes — the loop
/// iterations a refutation over a loop-carried join may need and still count as
/// an execution's.
const SHALLOW_SWEEPS: usize = 32;
/// S2: how many further passes a still-moving loop-carried bound is carried on
/// for, at its last pass's step ([`crate::abstract_interp::transfer::shallow_ascent`]).
/// `2^40` passes reach every value of a counter of up to 32 bits stepped by one
/// (the falsification gate's `loop_*` mutants overflow a `u8` on pass 256;
/// `loop_break_unbounded_still_refutes.rs` overflows a `u32` on pass `2^32`, a
/// real execution) and none a 64-bit cursor stepped by a small constant needs to
/// wrap (`utf8_simd.rs:61`'s `i + 3` needs `2^62`).
const SHALLOW_HORIZON_PASSES: i128 = 1 << 40;
/// Negative-only diagnostic classification; never evidence for any proof.
pub const GENERIC_REFUTATION_HELD_PREFIX: &str = "generic solver counterexample withheld:";

/// Retain the undecided native lane's stop when a pure provenance screen
/// withholds generic SAT. The screen supplies no proof or executable witness;
/// its deterministic decision must not erase a prior clock or unexplained stop.
/// The prefix remains first because it also denies runtime-check tolerance.
pub fn hold_generic_refutation_result(
    previous: &VerificationResult,
    held_reason: &str,
) -> Option<VerificationResult> {
    use trust_types::determinism::StopCause;

    if !held_reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX) {
        return None;
    }
    let (solver, time_ms, previous_detail) = match previous {
        VerificationResult::Unknown { solver, time_ms, reason } => {
            (*solver, *time_ms, reason.clone())
        }
        VerificationResult::Timeout { solver, timeout_ms } => {
            (*solver, 0, format!("native lane timed out with allowance {timeout_ms}ms"))
        }
        // Unknown future result variants cannot authorize this provenance rewrite.
        _ => return None,
    };
    let cause = StopCause::combine(StopCause::Solved, StopCause::of_result(previous));
    Some(VerificationResult::Unknown {
        solver,
        time_ms,
        // Delimit the original detail before applying the outer stamp, so
        // its own trailing token remains part of the retained diagnostic.
        reason: cause.stamp(&format!(
            "{held_reason}; native result before the provenance hold: ({previous_detail})"
        )),
    })
}

/// Compiler-derived, negative-only restriction. Absence of a restriction is
/// NOT a source-refinement certificate or a replacement for any existing gate.
pub struct GenericRefutationScope {
    function: Symbol,
    active: bool,
    names: Vec<(String, usize)>,
    /// Exact formula spelling -> unique `names` index (`Some(idx)`) or ambiguous (`None`).
    exact_locals: FxHashMap<String, Option<usize>>,
    /// True when no local's formula spelling contains `.`, `[`, `*`, or ends with `"__slice_len"`.
    roots_are_bare: bool,
    dependent: BTreeSet<usize>,
    opaque: Option<&'static str>,
    /// D5-A: the destinations of this body's calls into same-crate free `fn`s
    /// whose return value no summary constrains. Empty unless the compiler
    /// installed a [`LocalCallDestScreen`]; see
    /// [`Self::for_function_with_call_dests`].
    call_dests: Vec<UnpinnedCallDest>,
    /// D5-A: what the per-row dependence check reads off the body the VCs
    /// came from — how each formula name resolves to a local, and where each
    /// placeable violation sits. `None` (every scope not built by
    /// [`Self::for_function_with_call_dests`]) exempts nothing: a row over a
    /// screened destination is then held whenever its query mentions it.
    call_dest_body: Option<CallDestBody>,
    /// S1 (2026-10-16): this function's recorded L0 rows by span — kind,
    /// violation body, and whether the path condition COLLAPSED
    /// ([`PathGuardTerm::Collapsed`]). A row without an obligation record (the
    /// `HardenedBoundary` panic-boundary twin) carries the same collapsed path list
    /// as its L0 sibling, but no record to say so. A span alone can be shared by
    /// several obligations (a macro expansion, a desugared `for`), so the twin is
    /// read through the siblings that are ITS obligation ([`twin_sibling_matches`]:
    /// the same check family, and every variable of the sibling's body in the
    /// twin's query), and held only when every such sibling collapsed.
    l0_by_span: FxHashMap<SourceSpan, Vec<(VcKind, Formula, bool)>>,
    /// S2 (2026-10-16): the loop-carried join symbols of the body
    /// ([`crate::generate::StmtVersionCtx::loop_carried_join_symbols`]), or, for
    /// a body that has a loop and no exact answer, the conservative fallback
    /// ([`LoopJoins::Unavailable`]).
    loop_joins: LoopJoins,
    /// S3 (2026-10-16): the body's unmodelled foreign call values, as the L0
    /// havoc decline computes them, with every foreign monomorphic `Option`
    /// value call's payload admitted ([`crate::generate::PayloadSources`]).
    unmodelled: Option<crate::generate::UnmodelledValues>,
    /// Inclusive range facts bound the yield set, without modeling which call
    /// yields which member. They can support UNSAT, never executable generic SAT.
    inclusive_yield_set_only: Vec<String>,
    /// S3 (2026-10-16): what a recordless `HardenedBoundary` twin is read through
    /// — its L0 siblings at the same span. Empty unless `unmodelled` is set.
    twin_siblings: FxHashMap<SourceSpan, TwinSiblings>,
}

/// S2: the loop-carried join symbols of a body, or the fallback when they cannot
/// be computed exactly.
enum LoopJoins {
    /// The exact join symbols (empty for a body with no loop), each with its loop
    /// header's block, and every header's SHALLOW state
    /// ([`crate::abstract_interp::transfer::shallow_ascent`]): what the header's
    /// locals can hold within the first [`SHALLOW_SWEEPS`] passes. `shallow` is
    /// `None` when that walk is unavailable (a spent budget); every row naming a
    /// join is then held, as when the walk cannot clear it.
    Exact {
        joins: FxHashMap<String, usize>,
        shallow: Option<FxHashMap<usize, crate::abstract_interp::IntervalDomain>>,
    },
    /// No exact answer for a body that HAS a loop (a size bound, or an oracle
    /// built after the verify budget tripped). `tracked` is the base spelling of
    /// every local, marked when a loop block writes it or the body takes its
    /// address — the only names a join can be of. A query is held when it names an
    /// SSA-versioned symbol whose base resolves to a marked local, or to no local
    /// at all. `None`
    /// when the loop blocks have an effect that names no destination: every
    /// query of the body is held.
    Unavailable { detail: &'static str, tracked: Option<Vec<(String, bool)>> },
}

/// S3: the L0 rows of one span, for the recordless twin at that span.
#[derive(Default)]
struct TwinSiblings {
    /// The candidates siblings were declined on in generation
    /// (`UnmodeledCalleeReturn`, which drops the record): the L0 pass already
    /// decided that those violations rest on an unmodelled value. A twin follows
    /// one only when its own query names that candidate.
    declined: Vec<String>,
    /// Every sibling's obligation record.
    records: Vec<trust_types::ObligationRecord>,
}

impl GenericRefutationScope {
    /// Derive from the same current function and BOTH generated partitions.
    /// Preclassification moves unsupported rows out of the solver queue, but
    /// those Unknown results still restrict dependent counterexamples. Their
    /// presence is negative-only; no result status grants proof authority.
    /// Raw-generation callers pass their full inventory and an empty second
    /// slice. Discharge callers must retain the complete preclassified slice.
    pub fn for_function(
        func: &VerifiableFunction,
        generated: &[VerificationCondition],
        preclassified: &[(VerificationCondition, VerificationResult)],
    ) -> Self {
        let expanded = func.with_tail_calls_expanded();
        let _entry_scope = crate::generate::EntryScope::enter(expanded.as_ref());
        Self::for_function_with_expanded(func, expanded.as_ref(), generated, preclassified)
    }

    fn for_function_with_expanded(
        func: &VerifiableFunction,
        expanded_func: &VerifiableFunction,
        generated: &[VerificationCondition],
        preclassified: &[(VerificationCondition, VerificationResult)],
    ) -> Self {
        let _entry_scope = crate::generate::EntryScope::enter(expanded_func);
        let function = Symbol::intern(&func.name);
        let mut active = false;
        let mut collapsed_spans: FxHashSet<&SourceSpan> = FxHashSet::default();
        for vc in generated.iter().chain(preclassified.iter().map(|(vc, _)| vc)) {
            if vc.function != function {
                continue;
            }
            if matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported"
            ) {
                active = true;
            }
            if vc.location != SourceSpan::default()
                && !collapsed_spans.contains(&vc.location)
                && record_has_collapsed_path(vc)
            {
                collapsed_spans.insert(&vc.location);
            }
        }
        let mut l0_by_span: FxHashMap<SourceSpan, Vec<(VcKind, Formula, bool)>> =
            FxHashMap::default();
        if !collapsed_spans.is_empty() {
            for vc in generated.iter().chain(preclassified.iter().map(|(vc, _)| vc)) {
                if vc.function == function
                    && collapsed_spans.contains(&vc.location)
                    && let Some(record) = &vc.obligation
                {
                    l0_by_span.entry(vc.location.clone()).or_default().push((
                        vc.kind.clone(),
                        record.body.clone(),
                        record_has_collapsed_path(vc),
                    ));
                }
            }
        }
        let (loop_joins, unmodelled, inclusive_yield_set_only) = {
            let unmodelled = crate::generate::UnmodelledValues::of(
                expanded_func,
                crate::generate::PayloadSources::AnyForeignValueCall,
            );
            (
                loop_carried_joins(expanded_func),
                (!unmodelled.is_empty()).then_some(unmodelled),
                crate::generate::inclusive_range_yield_set_only_values(expanded_func),
            )
        };
        let mut twin_siblings: FxHashMap<SourceSpan, TwinSiblings> = FxHashMap::default();
        if unmodelled.is_some() {
            for vc in generated.iter().chain(preclassified.iter().map(|(vc, _)| vc)) {
                if vc.function != function
                    || vc.location == SourceSpan::default()
                    || matches!(vc.kind, VcKind::HardenedBoundary { .. })
                {
                    continue;
                }
                if let Some(record) = &vc.obligation {
                    twin_siblings
                        .entry(vc.location.clone())
                        .or_default()
                        .records
                        .push(record.clone());
                } else if let VcKind::UnsupportedMir { kind, detail } = &vc.kind
                    && kind == crate::generate::HAVOC_DECLINE_KIND
                {
                    let base = detail
                        .split_once("(`")
                        .and_then(|(_, rest)| rest.split_once("`)"))
                        .map_or_else(
                            || "an unmodelled call".to_owned(),
                            |(base, _)| base.to_owned(),
                        );
                    twin_siblings.entry(vc.location.clone()).or_default().declined.push(base);
                }
            }
        }
        let mut scope = Self {
            function,
            active,
            names: Vec::new(),
            exact_locals: FxHashMap::default(),
            roots_are_bare: true,
            dependent: BTreeSet::new(),
            opaque: None,
            call_dests: Vec::new(),
            call_dest_body: None,
            l0_by_span,
            loop_joins,
            unmodelled,
            inclusive_yield_set_only,
            twin_siblings,
        };
        if !active {
            return scope;
        }
        if func.body.blocks.len() > MAX_BLOCKS
            || func.body.locals.len() > MAX_LOCALS
            || func.body.blocks.iter().map(|b| b.stmts.len()).sum::<usize>() > MAX_STATEMENTS
            || crate::validate_function(func).is_err()
        {
            scope.opaque =
                Some("unresolved loop dependency analysis is unavailable or exceeds its bound");
            return scope;
        }
        // This detector uses dominance and predecessor closure, NOT block-ID
        // order. A lower-numbered acyclic successor must not fabricate a loop.
        let loops = crate::termination::detect_loops(&func.body);
        if loops.is_empty() {
            scope.opaque = Some("unresolved loop clause has no validated natural-loop context");
            return scope;
        }
        let backedges: BTreeSet<_> = loops.iter().map(|l| (l._latch.0, l.header.0)).collect();
        if unaccounted_cycle(func, &backedges) {
            scope.opaque =
                Some("unresolved loop body contains an unaccounted or irreducible cycle");
        }
        let loop_blocks: BTreeSet<_> =
            loops.iter().flat_map(|l| l.body_blocks.iter().map(|b| b.0)).collect();
        let mut definitions: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        scope.names.reserve(func.body.locals.len());
        scope.exact_locals.reserve(func.body.locals.len());
        for local in &func.body.locals {
            let root = crate::place_to_var_name(func, &Place::local(local.index));
            if scope.roots_are_bare
                && (root.contains(['.', '[', '*']) || root.ends_with("__slice_len"))
            {
                scope.roots_are_bare = false;
            }
            let idx = scope.names.len();
            scope
                .exact_locals
                .entry(root.clone())
                .and_modify(|slot| *slot = None)
                .or_insert(Some(idx));
            scope.names.push((root, local.index));
        }
        for block in &func.body.blocks {
            for statement in &block.stmts {
                match statement {
                    Statement::Assign { place, rvalue, .. } if place.projections.is_empty() => {
                        let Some(reads) = rvalue_reads(rvalue) else {
                            scope.opaque = Some(
                                "unresolved loop body has unaccounted alias or memory effects",
                            );
                            continue;
                        };
                        definitions.entry(place.local).or_default().extend(reads);
                        if loop_blocks.contains(&block.id.0) {
                            scope.dependent.insert(place.local);
                        }
                    }
                    Statement::StorageLive(local) | Statement::StorageDead(local) => {
                        if loop_blocks.contains(&block.id.0) {
                            scope.dependent.insert(*local);
                        }
                    }
                    Statement::Nop => {}
                    // A projected write, escape, intrinsic, or unknown statement
                    // can affect an alias/length not named by its destination.
                    _ => {
                        scope.opaque =
                            Some("unresolved loop body has unaccounted alias or memory effects")
                    }
                }
            }
            if !matches!(
                block.terminator,
                Terminator::Goto(_)
                    | Terminator::SwitchInt { .. }
                    | Terminator::Assert { .. }
                    | Terminator::Return
            ) {
                scope.opaque =
                    Some("unresolved loop body has an unaccounted call or control effect");
            }
        }
        // Include aliases and values computed AFTER the loop. Looking only at
        // the raw index name would miss `out = hi; index = out + 1`.
        for _ in 0..func.body.locals.len() {
            let old_len = scope.dependent.len();
            for (&destination, reads) in &definitions {
                if reads.iter().any(|read| scope.dependent.contains(read)) {
                    scope.dependent.insert(destination);
                }
            }
            if old_len == scope.dependent.len() {
                break;
            }
        }
        scope
    }

    /// [`Self::for_function`] plus the D5-A same-crate call-destination screen.
    ///
    /// `context` must be the SAME function-owned [`crate::VcgenContext`] the
    /// VCs were generated under: the pinned/unpinned decision reads the
    /// crate-wide callee return facts off it exactly as generation did, and the
    /// compiler's census ([`LocalCallDestScreen`]) rides on it. An owner
    /// mismatch or an empty screen installs no call-destination restriction,
    /// which is the pre-D5 behaviour; nothing here can grant any authority.
    pub fn for_function_with_call_dests(
        func: &VerifiableFunction,
        generated: &[VerificationCondition],
        preclassified: &[(VerificationCondition, VerificationResult)],
        context: &crate::VcgenContext,
    ) -> Self {
        let expanded = func.with_tail_calls_expanded();
        let _entry_scope = crate::generate::EntryScope::enter(expanded.as_ref());
        let mut scope =
            Self::for_function_with_expanded(func, expanded.as_ref(), generated, preclassified);
        let (call_dests, body) =
            unpinned_local_call_dests_with_body_expanded(func, expanded.as_ref(), context);
        scope.call_dests = call_dests;
        scope.call_dest_body = body;
        scope
    }

    /// Why generic SAT cannot establish an executable counterexample for this
    /// exact row. All hypotheses/path conditions are examined, not merely the
    /// raw violation's free variables. Ambiguous provenance remains Unknown.
    pub fn rejection_reason(&self, vc: &VerificationCondition) -> Option<String> {
        if vc.function == self.function && !self.inclusive_yield_set_only.is_empty() {
            let scan = scan_vars(&vc.formula, |name| {
                let base = name.split_once('#').map_or(name, |(base, _)| base);
                self.inclusive_yield_set_only.iter().any(|root| base_projects_from(base, root))
            });
            let detail = match scan {
                NameScan::Hit(name) => Some(format!(
                    "inclusive iterator value `{name}` has yield-set bounds, without a checked next-transition witness"
                )),
                NameScan::Exceeded => {
                    Some("inclusive iterator value-dependency scan exceeds its bound".into())
                }
                NameScan::Miss => None,
            };
            if let Some(detail) = detail {
                return Some(format!(
                    "{GENERIC_REFUTATION_HELD_PREFIX} {detail}; an interval member need not be yielded at this call; the original obligation remains unproved"
                ));
            }
        }
        // A modeled E4/E5 transition may have no UnsupportedMir row while its
        // value relation still contains explicit call/nested-loop havoc. The
        // complete solver query, including guards and hypotheses, must be
        // screened independently of the unsupported-loop dependency scope.
        // Use the same namespace discriminator as the mint/normalization
        // sites. This can only withhold SAT; it never rewrites a query or
        // changes the compiler's proof-direction decisions.
        if let Some(detail) = loop_transition_query_restriction(&vc.formula) {
            return Some(format!(
                "{GENERIC_REFUTATION_HELD_PREFIX} {detail}; symbolic loop values describe an over-approximation, not a checked execution; the original obligation remains unproved"
            ));
        }
        // D5-A: a same-crate callee's return value that no summary constrains
        // is a FREE variable of the query. SAT then chooses it, and the model is
        // a model of the formula, not a run (`guard(64)` reported `true`). Like
        // the screen above, this reads the complete query and only withholds.
        if let Some(detail) = self.call_dest_query_restriction(vc) {
            return Some(format!(
                "{GENERIC_REFUTATION_HELD_PREFIX} {detail}; a solver model over an unconstrained call result is not an execution; the original obligation remains unproved"
            ));
        }
        // The unsupported-loop-contract scope runs before S1-S3: where both hold a
        // row, its reason (which names the loop-written local) is the more
        // specific one. Either way the row is held.
        if let Some(reason) = self.unsupported_loop_contract_restriction(vc) {
            return Some(reason);
        }
        self.ungrounded_query_restriction(vc).map(|detail| {
            format!(
                "{GENERIC_REFUTATION_HELD_PREFIX} {detail}; a solver model of an over-approximated query is not an execution; the original obligation remains unproved"
            )
        })
    }

    /// The dependency scope of a body with an unsupported user loop contract
    /// (`active`): every reason it holds `vc` for, or `None`.
    fn unsupported_loop_contract_restriction(&self, vc: &VerificationCondition) -> Option<String> {
        if !self.active {
            return None;
        }
        let reason = |detail: &str| {
            Some(format!(
                "{GENERIC_REFUTATION_HELD_PREFIX} {detail}; an unsupported loop contract leaves an over-approximated state, not a checked execution; the original obligation remains unproved"
            ))
        };
        if vc.function != self.function {
            return reason("function identity does not match the retained dependency scope");
        }
        if let Some(detail) = self.opaque {
            return reason(detail);
        }
        let Some(record) = &vc.obligation else {
            return reason("raw-violation provenance is missing");
        };
        let Some(reconstructed) = reconstruct(&record.body, &record.wrappers) else {
            return reason("raw-violation reconstruction exceeds its bound");
        };
        if reconstructed != vc.formula {
            return reason("raw-violation wrappers do not reconstruct the exact query");
        }
        let mut pending = vec![&vc.formula];
        let mut visited = 0usize;
        while let Some(formula) = pending.pop() {
            visited += 1;
            if visited > MAX_FORMULA_NODES {
                return reason("query dependency analysis exceeds its bound");
            }
            // An uninterpreted predicate/function can carry implicit heap or
            // contract state even with no arguments, or only independent
            // scalar arguments. Its spelling does not establish provenance.
            if matches!(formula, Formula::Pred(..) | Formula::FnApp { .. }) {
                return reason(
                    "an opaque predicate or function has no complete dependency provenance",
                );
            }
            let name = match formula {
                Formula::Var(name, _) => Some(name.as_str()),
                Formula::SymVar(name, _) => Some(name.as_str()),
                _ => None,
            };
            if let Some(name) = name {
                // Tokens distinguish dynamic SSA values, but cannot establish
                // independence from a write in a cycle. Deliberately do not
                // interpret numeric token spellings as an execution proof.
                let base = name.split('#').next().unwrap_or(name);
                // PERF-COMPILER-VCGEN-712: resolve `base` in O(1) via `exact_locals`
                // when no root local spelling contains `.`, `[`, `*`, or ends with
                // `"__slice_len"`.
                let matched = if self.roots_are_bare {
                    let key = match base.find(['.', '[', '*']) {
                        Some(pos) => &base[..pos],
                        None => base.strip_suffix("__slice_len").unwrap_or(base),
                    };
                    self.exact_locals
                        .get(key)
                        .copied()
                        .flatten()
                        .and_then(|idx| self.names.get(idx))
                } else {
                    let mut matched: Option<&(String, usize)> = None;
                    for candidate @ (root, _) in &self.names {
                        if base == root
                            || base.strip_prefix(root.as_str()).is_some_and(|suffix| {
                                suffix.starts_with('.')
                                    || suffix.starts_with('[')
                                    || suffix.starts_with('*')
                                    || suffix == "__slice_len"
                            })
                        {
                            if matched.replace(candidate).is_some() {
                                return reason(
                                    "a query value has missing or ambiguous local/projection provenance",
                                );
                            }
                        }
                    }
                    matched
                };
                let Some((root, local)) = matched else {
                    return reason(
                        "a query value has missing or ambiguous local/projection provenance",
                    );
                };
                if self.dependent.contains(local) {
                    return reason(&format!(
                        "query depends on loop-written local `{root}` or its transitive value"
                    ));
                }
            }
            trust_types::for_each_formula_child(formula, |child| pending.push(child));
        }
        None
    }

    /// S1-S3 (2026-10-16): three shapes whose SAT model is a model of the formula,
    /// not of an execution, independent of any loop contract. Each only withholds;
    /// none rewrites a query, re-asks the solver, or grants authority. Asked in
    /// the order S1, S3, S2 (the first reason wins; every one holds).
    ///
    /// * S1 — the row's path condition COLLAPSED: the block's dominating guards
    ///   are absent from the query, so a model need not reach the block (aterm
    ///   `carry.rs:390`: two early returns both fire in the model).
    /// * S2 — the query names a loop-carried JOIN symbol: the value at a loop
    ///   header, which has a back-edge operand and no defining equation, so the
    ///   solver chooses it (aterm `utf8_simd.rs:61`: `i = 2^64 - 3` beside an empty
    ///   slice) — AND no value the join takes within the first [`SHALLOW_SWEEPS`]
    ///   passes over its loop satisfies the query ([`shallow_clears`]). Naming a
    ///   join alone does not hold: nearly every genuine in-loop bug names one (the
    ///   countdown mutant's `offset - 4` underflow on the fifth pass), and a query a
    ///   shallow execution satisfies keeps its refutation. Where the join's shallow
    ///   interval is unbounded the row is kept too (the status before S2).
    /// * S3 — the refutation rests on the value of an unmodelled FOREIGN call (or
    ///   its `Option` payload) that nothing pins, by the L0 havoc decline's own
    ///   candidate, pinning and flip tests (aterm `dispatch.rs:745`'s hardened twin,
    ///   `params.len() = u64::MAX`; `dispatch.rs:751` `Some(1)` on an empty slice).
    fn ungrounded_query_restriction(&self, vc: &VerificationCondition) -> Option<String> {
        if vc.function != self.function {
            return None;
        }
        let recordless_twin =
            vc.obligation.is_none() && matches!(vc.kind, VcKind::HardenedBoundary { .. });
        if record_has_collapsed_path(vc)
            || (recordless_twin
                && self.l0_by_span.get(&vc.location).is_some_and(|rows| {
                    let mut matching = rows
                        .iter()
                        .filter(|(kind, body, _)| twin_sibling_matches(vc, kind, body))
                        .peekable();
                    matching.peek().is_some() && matching.all(|(_, _, collapsed)| *collapsed)
                }))
        {
            return Some(
                "path condition collapsed; the block's dominating guards are absent".into(),
            );
        }
        // S3 before S2: where both hold, the unmodelled call value is the more
        // specific cause (a reseated `position` loop reads both).
        if let Some(values) = &self.unmodelled {
            let siblings =
                if recordless_twin { self.twin_siblings.get(&vc.location) } else { None };
            let declined = siblings.and_then(|s| {
                s.declined
                    .iter()
                    .find(|base| {
                        matches!(
                            scan_vars(&vc.formula, |name| {
                                base_projects_from(
                                    name.split_once('#').map_or(name, |(b, _)| b),
                                    base,
                                )
                            }),
                            NameScan::Hit(_)
                        )
                    })
                    .cloned()
            });
            if let Some(base) = declined.or_else(|| {
                values.query_rests_on_unmodelled_value(
                    vc,
                    siblings.map_or(&[][..], |s| s.records.as_slice()),
                )
            }) {
                return Some(format!(
                    "query rests on the unmodelled return of a foreign call (`{base}`), which nothing in this body constrains"
                ));
            }
        }
        match &self.loop_joins {
            LoopJoins::Exact { joins, shallow } if !joins.is_empty() => {
                let mut named: Vec<&str> = Vec::new();
                match scan_vars(&vc.formula, |name| {
                    if joins.contains_key(name) && !named.contains(&name) {
                        named.push(name);
                    }
                    false
                }) {
                    NameScan::Exceeded => {
                        return Some(
                            "loop-carried join scan of the query exceeds its bound".into(),
                        );
                    }
                    NameScan::Hit(_) | NameScan::Miss => {}
                }
                if named.len() > 1 {
                    named.sort_unstable();
                }
                if let Some(symbol) = named.first() {
                    // The join has no defining equation, so the solver chose it. The
                    // model is held only when NO value the joins take within the
                    // first iterations satisfies the query (`shallow_clears`): then a
                    // real execution needs a deep — or no — iteration to violate the
                    // obligation, and the model's join value is not shown to be one an
                    // execution holds. A query a shallow execution can satisfy keeps
                    // its refutation (a genuine in-loop bug at iteration k).
                    let cleared = shallow
                        .as_ref()
                        .is_none_or(|states| shallow_clears(&vc.formula, &named, joins, states));
                    if cleared {
                        return Some(format!(
                            "loop-carried value at a loop header has no defining equation (`{symbol}`), and no value it takes in the first {SHALLOW_SWEEPS} passes over its loop (a still-moving bound carried on for {SHALLOW_HORIZON_PASSES} more) satisfies the query"
                        ));
                    }
                }
            }
            LoopJoins::Exact { .. } => {}
            LoopJoins::Unavailable { detail, tracked: None } => return Some((*detail).into()),
            LoopJoins::Unavailable { detail, tracked: Some(tracked) } => {
                match formula_names_versioned_tracked(&vc.formula, tracked) {
                    NameScan::Hit(symbol) => {
                        return Some(format!("{detail}; the query names `{symbol}`"));
                    }
                    NameScan::Exceeded => {
                        return Some(
                            "loop-carried join scan of the query exceeds its bound".into(),
                        );
                    }
                    NameScan::Miss => {}
                }
            }
        }
        None
    }

    /// D5-A: withhold a row whose refutation may DEPEND on an unpinned
    /// same-crate call's result.
    ///
    /// A row whose query never mentions a screened destination is untouched: a
    /// model of it chose no call result. A row that does mention one is held
    /// unless one of two exemptions PROVES the model's choice for that
    /// destination is irrelevant; anything the proof cannot establish holds the
    /// row (a fail-closed `Unknown`, never a `Failed` over a value the solver
    /// invented).
    ///
    /// # Why "mentions" is not "depends on"
    ///
    /// The measured false refutation depended on the call through a PATH GUARD
    /// (`if !guard(bit) { return None } x >> bit` put `_3` in the guard, not in
    /// the shift), so the screen reads the whole query. But once a bounding
    /// callee (`requires b <= a ensures result <= a`) stopped pinning its
    /// result, the whole-query read also held rows that merely CARRY the call's
    /// own injected `pre → post` fact: `let _r = smax(20, 3); a - 10` read
    /// `[overflow:sub] UNKNOWN` instead of FAILED at `a = 0` (review, 2026-09-28,
    /// `rvB/mb/m2.rs::unused_result` and `m1.rs::indep_after`).
    ///
    /// # Exemption 1: the call's own precondition row
    ///
    /// When the destination cannot hold a value before that call runs
    /// ([`UnpinnedCallDest::precondition_precedes_value`]): the row judges
    /// `requires[actuals]` at the call's entry, before the destination is
    /// written (measured 2026-09-28: `use_outside_sub`'s genuine `rmax(0, 5)`
    /// violation).
    ///
    /// # Exemption 2: the row is independent of the result
    ///
    /// [`Self::row_is_independent_of`]. Its soundness argument: take the
    /// model's values for everything but the destination and run the program
    /// from them. If (a) no branch or assertion that can be decided by the
    /// result lies on any path to the violation, (b) the violation's own MIR
    /// operands are not computed from the result, and (c) no other value the
    /// query names is, then that run reaches the violation with the operands
    /// the model gave it, whatever the call really returned — the only
    /// conjuncts left over the destination are facts every run satisfies (its
    /// type range, the call's own guarded `pre → post`), because a fact over it
    /// that encodes a path DECISION would need a branch (a) excluded. The
    /// counterexample is then an execution — PROVIDED THE CALL RETURNS. A
    /// callee that panics or diverges on the model's arguments stops the run
    /// before the violation (`let _r = chk(a); a - 10` under `chk: requires
    /// x >= 10`, whose body `x - 10` panics at `a = 0`: the row is released and
    /// reads FAILED at `a = 0` beside the call's own, genuine, `[precond]`
    /// FAILED; review 2026-09-29, `rvB2/mb/m8.rs`). That is a false FAILED, not
    /// a false proof, and docs/KNOWN_HAZARDS.md discloses it with the shapes
    /// this screen never sees (a loop-carried copy of the result, a returned
    /// reference's pointee, method and generic callees).
    fn call_dest_query_restriction(&self, vc: &VerificationCondition) -> Option<String> {
        if self.call_dests.is_empty() {
            return None;
        }
        if vc.function != self.function {
            return Some(
                "function identity does not match the retained call-destination scope".into(),
            );
        }
        let Some(bases) = formula_base_names(&vc.formula) else {
            return Some("call-destination dependency analysis exceeds its bound".into());
        };
        for dest in &self.call_dests {
            if !bases.iter().any(|base| dest.names_value(base)) {
                continue;
            }
            if dest.is_own_precondition_row(vc) || self.row_is_independent_of(dest, vc, &bases) {
                continue;
            }
            return Some(format!(
                "query depends on the unmodeled return of same-crate `{}` (`{}`); no summary determines that value at this call (a bound such as `ensures result <= a`, or any clause guarded by a `requires`, leaves the solver free to choose it), so an `ensures result == …` on `{}` without `requires` is what lets callers use it",
                dest.callee, dest.name, dest.callee
            ));
        }
        None
    }

    /// Exemption 2 of [`Self::call_dest_query_restriction`]: whether `vc`'s
    /// refutation provably does not depend on `dest`'s value. Every `false` is
    /// "not proved", never "dependent", and holds the row.
    ///
    /// * The row must be PLACEABLE: a kind whose violation sits at one MIR
    ///   operation — an arithmetic/shift overflow or a division/remainder by
    ///   zero at a binary operation, a call-site precondition at the call — and
    ///   at least one operation of that kind must carry the row's span. A
    ///   postcondition, an assertion, or a row the span finds no operation for
    ///   is never exempt.
    /// * (a) No such operation's block is CONTROLLED by the result (reachable
    ///   from a branch or assertion that reads a value computed from it).
    /// * (b) No such operation reads a value computed from the result.
    /// * (c) Every other name in the query resolves to exactly one local, and
    ///   none of those is computed from the result. A name with no unique
    ///   local (a synthetic value, an ambiguous spelling) fails the check.
    /// * (d) Where the row carries an authenticated obligation record (its
    ///   wrappers reconstruct the exact query), the raw violation and its path
    ///   guards do not mention the destination at all — a second reading of
    ///   (b) and (a) that does not rely on the span.
    ///
    /// "Computed from the result" is [`CallResultInfluence`]: a flow-
    /// insensitive data closure plus every local written in a controlled block,
    /// and it is UNDECIDED — so nothing is exempt — the moment the value
    /// reaches memory or a callee.
    fn row_is_independent_of(
        &self,
        dest: &UnpinnedCallDest,
        vc: &VerificationCondition,
        bases: &BTreeSet<&str>,
    ) -> bool {
        let (Some(body), Some(influence)) = (&self.call_dest_body, &dest.influence) else {
            return false;
        };
        let mut sites = body.sites.iter().filter(|site| site.places(vc)).peekable();
        if sites.peek().is_none() {
            return false;
        }
        for site in sites {
            if influence.controlled.contains(&site.block)
                || site.reads.iter().any(|local| influence.dependents.contains(local))
            {
                return false;
            }
        }
        for &base in bases {
            // The direct spelling only (`_3`, `_3.0`, `_3[1]`): a downcast or
            // discriminant-carrier name of the destination still has to resolve
            // to a local here, as it did before D5-A-DOWNCAST-1 widened what
            // HOLDS a row, so that widening exempts nothing new.
            if dest.names_value_direct(base) {
                continue;
            }
            match body.local_of(base) {
                Some(local) if !influence.dependents.contains(&local) => {}
                _ => return false,
            }
        }
        if let Some(record) = &vc.obligation
            && reconstruct(&record.body, &record.wrappers).is_some_and(|q| q == vc.formula)
        {
            let mut core = vec![&record.body];
            for wrapper in &record.wrappers {
                if let ObligationWrapper::PathGuardOr { paths } = wrapper {
                    for path in paths {
                        if let PathGuardTerm::Guarded { guards } = path {
                            core.extend(guards.iter());
                        }
                    }
                }
            }
            for part in core {
                match formula_base_names(part) {
                    Some(names) if !names.iter().any(|base| dest.names_value(base)) => {}
                    _ => return false,
                }
            }
        }
        true
    }
}

/// Every variable of `formula` with its SSA token stripped (`a#s1_0` → `a`).
/// `None` past [`MAX_FORMULA_NODES`].
fn formula_base_names(formula: &Formula) -> Option<BTreeSet<&str>> {
    let mut names = BTreeSet::new();
    let mut pending = vec![formula];
    let mut visited = 0usize;
    while let Some(formula) = pending.pop() {
        visited += 1;
        if visited > MAX_FORMULA_NODES {
            return None;
        }
        let name = match formula {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(name, _) => Some(name.as_str()),
            _ => None,
        };
        if let Some(name) = name {
            let base = name.split('#').next().unwrap_or(name);
            names.insert(base);
        }
        trust_types::for_each_formula_child(formula, |child| pending.push(child));
    }
    Some(names)
}

/// D5-A: the body facts the per-row dependence check reads, computed once per
/// scope from the body the VCs were generated from.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CallDestBody {
    /// Each local's formula spelling (`place_to_var_name`) and index.
    names: Vec<(String, usize)>,
    /// Exact formula spelling -> unique local index (`Some(idx)`) or ambiguous (`None`).
    exact_locals: trust_types::fx::FxHashMap<String, Option<usize>>,
    /// True when no local's formula spelling contains `.`, `[`, `*`, or ends with `"__slice_len"`.
    roots_are_bare: bool,
    /// Every operation a placeable row can sit at.
    sites: Vec<ViolationSite>,
}

impl CallDestBody {
    fn of(func: &VerifiableFunction) -> Self {
        let names: Vec<(String, usize)> = func
            .body
            .locals
            .iter()
            .map(|local| (crate::place_to_var_name(func, &Place::local(local.index)), local.index))
            .collect();
        let mut exact_locals = trust_types::fx::FxHashMap::with_capacity_and_hasher(
            names.len(),
            Default::default(),
        );
        let mut roots_are_bare = true;
        for (root, local) in &names {
            if roots_are_bare
                && (root.contains(['.', '[', '*']) || root.ends_with("__slice_len"))
            {
                roots_are_bare = false;
            }
            exact_locals
                .entry(root.clone())
                .and_modify(|slot| *slot = None)
                .or_insert(Some(*local));
        }
        let mut sites = Vec::new();
        for (block_index, block) in func.body.blocks.iter().enumerate() {
            for statement in &block.stmts {
                let Statement::Assign { rvalue, span, .. } = statement else {
                    continue;
                };
                let (Rvalue::BinaryOp(op, lhs, rhs)
                | Rvalue::CheckedBinaryOp(op, lhs, rhs)
                | Rvalue::UncheckedBinaryOp(op, lhs, rhs)) = rvalue
                else {
                    continue;
                };
                let mut reads = Vec::new();
                // An operand the analysis cannot read is recorded as reading
                // EVERY local, so no dependents set can miss it.
                if operand_reads_all(lhs, &mut reads)
                    .and(operand_reads_all(rhs, &mut reads))
                    .is_none()
                {
                    reads.extend(func.body.locals.iter().map(|local| local.index));
                }
                reads.sort_unstable();
                reads.dedup();
                sites.push(ViolationSite {
                    span: span.clone(),
                    kind: SiteKind::BinaryOp(*op),
                    block: block_index,
                    reads,
                });
            }
            if let Terminator::Call { func: callee, args, span, .. }
            | Terminator::TailCall { func: callee, args, span, .. } = &block.terminator
            {
                let mut reads = Vec::new();
                if args.iter().try_for_each(|arg| operand_reads_all(arg, &mut reads)).is_none() {
                    reads.extend(func.body.locals.iter().map(|local| local.index));
                }
                reads.sort_unstable();
                reads.dedup();
                sites.push(ViolationSite {
                    span: span.clone(),
                    kind: SiteKind::Call(callee.clone()),
                    block: block_index,
                    reads,
                });
            }
        }
        Self { names, exact_locals, roots_are_bare, sites }
    }

    /// The unique local `base` spells: the local itself or a projection of it
    /// (`.field`, `[index]`, `*`, `__slice_len`), exactly as the loop scope
    /// resolves provenance. Missing or ambiguous is `None`.
    fn local_of(&self, base: &str) -> Option<usize> {
        // PERF-COMPILER-VCGEN-705: when no root local spelling contains `.`, `[`, `*`,
        // or ends with `"__slice_len"`, the only root that can match `base` is the
        // prefix before the first `.`/`[`/`*` (or `base` with a trailing `"__slice_len"`
        // stripped when no `.`/`[`/`*` is present). Resolve in O(1) via `exact_locals`.
        if self.roots_are_bare {
            let key = match base.find(['.', '[', '*']) {
                Some(pos) => &base[..pos],
                None => base.strip_suffix("__slice_len").unwrap_or(base),
            };
            return self.exact_locals.get(key).copied().flatten();
        }
        let mut candidates = self.names.iter().filter(|(root, _)| {
            base == root
                || base.strip_prefix(root.as_str()).is_some_and(|suffix| {
                    suffix.starts_with('.')
                        || suffix.starts_with('[')
                        || suffix.starts_with('*')
                        || suffix == "__slice_len"
                })
        });
        let (_, local) = candidates.next()?;
        candidates.next().is_none().then_some(*local)
    }
}

/// One MIR operation a placeable row's violation can sit at.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ViolationSite {
    span: SourceSpan,
    kind: SiteKind,
    /// Block index (position in `body.blocks`, not `BlockId`).
    block: usize,
    /// Locals the operation reads (operands, their index locals, pointers read
    /// through).
    reads: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SiteKind {
    BinaryOp(trust_types::BinOp),
    Call(String),
}

impl ViolationSite {
    /// Whether this operation is one `vc`'s violation can sit at: the same span
    /// and an operation of the row's kind. Only these kinds are placeable.
    fn places(&self, vc: &VerificationCondition) -> bool {
        if self.span != vc.location {
            return false;
        }
        match (&vc.kind, &self.kind) {
            (
                VcKind::ArithmeticOverflow { op, .. } | VcKind::ShiftOverflow { op, .. },
                SiteKind::BinaryOp(at),
            ) => op == at,
            (VcKind::DivisionByZero, SiteKind::BinaryOp(at)) => *at == trust_types::BinOp::Div,
            (VcKind::RemainderByZero, SiteKind::BinaryOp(at)) => *at == trust_types::BinOp::Rem,
            (VcKind::Precondition { callee }, SiteKind::Call(at)) => callee == at,
            _ => false,
        }
    }
}

/// What in one body may differ with one call's result.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CallResultInfluence {
    /// Locals whose value may be computed from the result: the destination,
    /// every local an assignment writes from one of these (flow-insensitive,
    /// so every write of a local counts), and every local written in a
    /// `controlled` block.
    dependents: BTreeSet<usize>,
    /// Block indices whose execution may be decided by the result: every block
    /// reachable from a `SwitchInt` or `Assert` that reads a dependent.
    controlled: BTreeSet<usize>,
}

/// The influence of the value `dest_local` receives, or `None` when it cannot
/// be bounded: the value (or an address of it) reaches memory or a callee, a
/// call/drop/memory write runs in a block the value controls, or the body uses
/// an effect this analysis does not model. `None` exempts nothing.
fn block_index_of(
    func: &VerifiableFunction,
    index_of: &Option<FxHashMap<usize, usize>>,
    block_id: usize,
) -> Option<usize> {
    if func.body.blocks.get(block_id).is_some_and(|b| b.id.0 == block_id) {
        Some(block_id)
    } else {
        index_of.as_ref().and_then(|map| map.get(&block_id).copied())
    }
}

fn call_result_influence(
    func: &VerifiableFunction,
    dest_local: usize,
) -> Option<CallResultInfluence> {
    if func.body.blocks.len() > MAX_BLOCKS
        || func.body.locals.len() > MAX_LOCALS
        || func.body.blocks.iter().map(|b| b.stmts.len()).sum::<usize>() > MAX_STATEMENTS
    {
        return None;
    }
    let index_of: Option<FxHashMap<usize, usize>> = func
        .body
        .blocks
        .iter()
        .enumerate()
        .any(|(index, block)| block.id.0 != index)
        .then(|| {
            func.body
                .blocks
                .iter()
                .enumerate()
                .map(|(index, block)| (block.id.0, index))
                .collect()
        });
    let mut dependents = BTreeSet::from([dest_local]);
    let mut controlled: BTreeSet<usize> = BTreeSet::new();
    let mut reads = Vec::new();
    let mut target = Vec::new();
    let mut pending = Vec::new();
    let reads_dependent = |reads: &[usize], dependents: &BTreeSet<usize>| {
        reads.iter().any(|local| dependents.contains(local))
    };
    loop {
        let before = (dependents.len(), controlled.len());
        for (block_index, block) in func.body.blocks.iter().enumerate() {
            let in_controlled = controlled.contains(&block_index);
            for statement in &block.stmts {
                match statement {
                    Statement::Assign { place, rvalue, .. } => {
                        let takes_address = rvalue_reads_all(rvalue, &mut reads)?;
                        target.clear();
                        place_reads_all(place, &mut target)?;
                        target.retain(|&l| l != place.local);
                        let rvalue_dep = reads_dependent(&reads, &dependents);
                        let flows = rvalue_dep || reads_dependent(&target, &dependents);
                        if takes_address && rvalue_dep {
                            return None;
                        }
                        if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                            if flows || in_controlled || dependents.contains(&place.local) {
                                return None;
                            }
                        } else if flows || in_controlled {
                            dependents.insert(place.local);
                        }
                    }
                    Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                        target.clear();
                        place_reads_all(place, &mut target)?;
                        target.retain(|&l| l != place.local);
                        let flows = reads_dependent(&target, &dependents) || in_controlled;
                        if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                            if flows || dependents.contains(&place.local) {
                                return None;
                            }
                        } else if flows {
                            dependents.insert(place.local);
                        }
                    }
                    Statement::Intrinsic { args, .. } => {
                        reads.clear();
                        for arg in args {
                            operand_reads_all(arg, &mut reads)?;
                        }
                        if in_controlled || reads_dependent(&reads, &dependents) {
                            return None;
                        }
                    }
                    Statement::CopyNonOverlapping { src, dst, count, .. } => {
                        reads.clear();
                        for operand in [src, dst, count] {
                            operand_reads_all(operand, &mut reads)?;
                        }
                        if in_controlled || reads_dependent(&reads, &dependents) {
                            return None;
                        }
                    }
                    Statement::StorageLive(_)
                    | Statement::StorageDead(_)
                    | Statement::Retag { .. }
                    | Statement::PlaceMention(_)
                    | Statement::Coverage
                    | Statement::ConstEvalCounter
                    | Statement::Nop => {}
                    _ => return None,
                }
            }
            let branch_reads_dependent = match &block.terminator {
                Terminator::SwitchInt { discr, .. } => {
                    reads.clear();
                    operand_reads_all(discr, &mut reads)?;
                    reads_dependent(&reads, &dependents)
                }
                Terminator::Assert { cond, .. } => {
                    reads.clear();
                    operand_reads_all(cond, &mut reads)?;
                    reads_dependent(&reads, &dependents)
                }
                Terminator::Call { args, dest, .. } => {
                    reads.clear();
                    for arg in args {
                        operand_reads_all(arg, &mut reads)?;
                    }
                    place_reads_all(dest, &mut reads)?;
                    reads.retain(|&l| l != dest.local);
                    if in_controlled || reads_dependent(&reads, &dependents) {
                        return None;
                    }
                    false
                }
                Terminator::TailCall { args, .. } => {
                    reads.clear();
                    for arg in args {
                        operand_reads_all(arg, &mut reads)?;
                    }
                    if in_controlled || reads_dependent(&reads, &dependents) {
                        return None;
                    }
                    false
                }
                Terminator::Drop { place, .. } => {
                    reads.clear();
                    place_reads_all(place, &mut reads)?;
                    if in_controlled || reads_dependent(&reads, &dependents) {
                        return None;
                    }
                    false
                }
                Terminator::Goto(_)
                | Terminator::Return
                | Terminator::Unreachable
                | Terminator::Resume => false,
                _ => return None,
            };
            if branch_reads_dependent {
                pending.clear();
                push_non_unwind_successors(&block.terminator, &mut pending);
                while let Some(next) = pending.pop() {
                    let index = block_index_of(func, &index_of, next.0)?;
                    if controlled.insert(index) {
                        push_non_unwind_successors(
                            &func.body.blocks[index].terminator,
                            &mut pending,
                        );
                    }
                }
            }
        }
        if before == (dependents.len(), controlled.len()) {
            return Some(CallResultInfluence { dependents, controlled });
        }
    }
}

/// Every local `rvalue` reads, and whether it TAKES AN ADDRESS (`&`, `&raw`),
/// through which a later write or callee could reach the place. `None` for an
/// rvalue this analysis does not model.
fn rvalue_reads_all(rvalue: &Rvalue, reads: &mut Vec<usize>) -> Option<bool> {
    reads.clear();
    let takes_address = match rvalue {
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => {
            place_reads_all(place, reads)?;
            true
        }
        Rvalue::CopyForDeref(place) => {
            place_reads_all(place, reads)?;
            false
        }
        Rvalue::PtrOffset { ptr, count } => {
            operand_reads_all(ptr, reads)?;
            operand_reads_all(count, reads)?;
            false
        }
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => {
            operand_reads_all(operand, reads)?;
            false
        }
        Rvalue::BinaryOp(_, lhs, rhs)
        | Rvalue::CheckedBinaryOp(_, lhs, rhs)
        | Rvalue::UncheckedBinaryOp(_, lhs, rhs) => {
            operand_reads_all(lhs, reads)?;
            operand_reads_all(rhs, reads)?;
            false
        }
        Rvalue::Len(place) | Rvalue::Discriminant(place) => {
            place_reads_all(place, reads)?;
            false
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                operand_reads_all(operand, reads)?;
            }
            false
        }
        _ => return None,
    };
    Some(takes_address)
}

/// [`place_reads`] for the call-result influence: the base local, every
/// `Index` local, and no others — a `Downcast`/cast projection selects, it
/// reads nothing. A projection this analysis does not know is `None`.
fn place_reads_all(place: &Place, reads: &mut Vec<usize>) -> Option<()> {
    reads.push(place.local);
    for projection in &place.projections {
        match projection {
            Projection::Index(local) => {
                reads.push(*local);
            }
            Projection::Deref
            | Projection::Field(_)
            | Projection::Downcast(_)
            | Projection::OpaqueCast(_)
            | Projection::UnwrapUnsafeBinder(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {}
            _ => return None,
        }
    }
    Some(())
}

/// [`operand_reads`] over [`place_reads_all`]. A symbolic or unsupported
/// operand is `None`.
fn operand_reads_all(operand: &Operand, reads: &mut Vec<usize>) -> Option<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_reads_all(place, reads),
        Operand::Constant(_) => Some(()),
        _ => None,
    }
}

/// D5-A: the compiler's census of which call sites in one body reach a
/// same-crate, non-generic, non-trait, non-foreign free `fn`, and which callees
/// that body's contract-summary DB PINS.
///
/// Only `rustc_mir_transform::trust_verify` can build a meaningful one: the
/// first set is keyed by the `(StableCrateId, DefIndex)` half of
/// [`trust_types::CalleeIdentity`] and decided from `tcx.def_kind` /
/// `tcx.generics_of`, never from a rendered callee string. Both are
/// NEGATIVE-ONLY inputs: a screened callee's destination is left to the solver
/// only where something DETERMINES it — a crate-wide return fact, or a pinning
/// contract summary the injector admitted at that very call site; nothing here
/// can make a verdict stronger.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LocalCallDestScreen {
    local_free_fns: FxHashSet<(u64, u32)>,
    /// Callee name → formal count, for each summary that PINS its result
    /// ([`crate::SummaryDatabase::postcondition_pinning_callees`]).
    contract_pinning_callees: FxHashMap<String, usize>,
    /// Extra typed actual-binding gate, shared with enum-clause emission.
    contract_pinning_entries: FxHashMap<String, crate::generate::EntryBindings>,
}

impl LocalCallDestScreen {
    /// `local_free_fns`: `(stable_crate_id, def_index)` of each screened
    /// callee. `summaries`: the DB the body's VCs were generated with.
    ///
    /// Only a summary whose injected clause DETERMINES the result counts
    /// ([`crate::SummaryDatabase::postcondition_pinning_callees`]), and the
    /// screen re-asks the injector's call-site half at each call. Two coarser
    /// questions were each measured to leave a false refutation standing:
    /// every DB name (2026-09-24: an L1 body's DB holds an entry for each
    /// same-crate callee, most with nothing injectable — `shift_via_guard`), and
    /// every INJECTING name (2026-09-28: `requires b <= a ensures result <= a`
    /// bounds `r` without fixing it — `p_falsefail::dead_else`). Taking the DB,
    /// not a list of names, is what keeps a caller from asking either again.
    #[must_use]
    pub fn new(
        local_free_fns: impl IntoIterator<Item = (u64, u32)>,
        summaries: &crate::SummaryDatabase,
    ) -> Self {
        Self {
            local_free_fns: local_free_fns.into_iter().collect(),
            contract_pinning_callees: summaries
                .postcondition_pinning_callees()
                .map(|(name, formals)| (name.to_owned(), formals))
                .collect(),
            contract_pinning_entries: summaries
                .postcondition_pinning_entry_bindings()
                .map(|(name, binding)| (name.to_owned(), binding.clone()))
                .collect(),
        }
    }

    /// Whether the census screens nothing.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.local_free_fns.is_empty()
    }
}

/// One screened destination: the name its value carries in a VC formula and
/// the callee's display path (the diagnostic, and the key of the call's own
/// `Precondition` row).
#[derive(Clone, Debug, PartialEq, Eq)]
struct UnpinnedCallDest {
    name: String,
    callee: String,
    /// The call's span, when this call is the only call to `callee` at it —
    /// the `location` its own call-site `Precondition` row carries. `None`
    /// never exempts that row.
    call_span: Option<SourceSpan>,
    /// Whether the destination holds no value before this call runs: it is not
    /// a parameter, this call is its ONLY write (no named assignment, no
    /// partial write, no `&mut` escape — `local_defs::unique_defining_block`),
    /// it is written whole, and no control-flow cycle leads from the call back
    /// to itself (a loop would carry the previous iteration's result into this
    /// call's arguments or path). Only then is the call's own precondition row
    /// independent of the value the call returns.
    precondition_precedes_value: bool,
    /// What in the body may depend on the value this call returns
    /// ([`call_result_influence`]); `None` when that cannot be bounded, which
    /// exempts no row from the screen.
    influence: Option<CallResultInfluence>,
}

impl UnpinnedCallDest {
    /// Whether `vc` is this call's own call-site `Precondition` row AND the
    /// destination provably has no value when that row's condition is judged.
    /// Such a row is exempt from the screen for this destination only; every
    /// other destination the query mentions still withholds it.
    fn is_own_precondition_row(&self, vc: &VerificationCondition) -> bool {
        self.precondition_precedes_value
            && self.call_span.as_ref().is_some_and(|span| *span == vc.location)
            && matches!(&vc.kind, VcKind::Precondition { callee } if *callee == self.callee)
    }

    /// Whether the SSA-token-stripped formula name `base` denotes this
    /// destination's VALUE: the destination itself or a by-value projection
    /// of it (`_3.0`, `_3[1]`). A dereference (`*`) is memory the call's
    /// result points at, not the result, and is deliberately not matched.
    ///
    /// Trust (2026-10-10, D5-A-DOWNCAST-1): an enum-valued destination's payload
    /// is spelled through a DOWNCAST (`_5@1.0`, `Some`'s field 0) and its
    /// variant through the discriminant carrier (`__trust_mir__discr__5`,
    /// [`crate::discriminant_formula_var_name`]); both are its value. Matching
    /// only `.`/`[` let `if let Some(i) = index_in(xs, at) { v[i] }` keep a
    /// solver model that chose `Some(0)` for an empty `xs` as a FAILED row
    /// (astream-agent `fork.rs:93`). Matching more names only withholds more
    /// models, and only ever as a held Unknown.
    fn names_value(&self, base: &str) -> bool {
        if base.contains('*') {
            return false;
        }
        let names = |candidate: &str| {
            candidate == self.name
                || candidate.strip_prefix(&self.name).is_some_and(|suffix| {
                    suffix.starts_with('.') || suffix.starts_with('[') || suffix.starts_with('@')
                })
        };
        names(base)
            || base
                .strip_prefix("__trust_mir__discr_")
                .is_some_and(names)
    }

    /// [`Self::names_value`] before D5-A-DOWNCAST-1: the destination itself or a
    /// `.`/`[` projection of it. Read only by the independence exemption's
    /// "every other name resolves to a local" check, whose skip set it keeps.
    ///
    /// Trust (merge 2026-10-14): deliberately NOT `crate::is_projection_segment_lead`.
    /// The soundness line's 3932521829a widened the one `names_value` it had to the
    /// namer's separators so a downcast payload HOLDS a row; upstream's D5-A-DOWNCAST-1
    /// did the same in [`Self::names_value`] and kept this narrower twin for the
    /// exemption. The merge (98b7fad77d2) carried 3932521829a's body into this twin, so
    /// a downcast payload of the destination (`_3@1.0`) skipped the "resolves to a
    /// local" check — `CallDestBody::local_of` resolves no `@` name, which HOLDS the
    /// row — and the exemption could release a counterexample that chose the
    /// destination's payload: the widening then exempted rows instead of only holding
    /// more of them.
    fn names_value_direct(&self, base: &str) -> bool {
        if base.contains('*') {
            return false;
        }
        base == self.name
            || base
                .strip_prefix(self.name.as_str())
                .is_some_and(|suffix| suffix.starts_with('.') || suffix.starts_with('['))
    }
}

/// D5-A: the destinations of `func`'s calls into screened callees whose value
/// nothing models. Evaluated under `context`, the SAME owner-checked frame
/// generation ran under, so the crate-wide return facts consulted here are the
/// ones `semantic_guard` consulted when it decided whether to emit a fact.
#[cfg(test)]
fn unpinned_local_call_dests(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> Vec<UnpinnedCallDest> {
    let expanded = func.with_tail_calls_expanded();
    unpinned_local_call_dests_with_body_expanded(func, expanded.as_ref(), context).0
}

/// [`unpinned_local_call_dests`] plus the [`CallDestBody`] the per-row
/// dependence check reads — `None` whenever no destination is screened.
fn unpinned_local_call_dests_with_body_expanded(
    func: &VerifiableFunction,
    expanded_func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> (Vec<UnpinnedCallDest>, Option<CallDestBody>) {
    let screen = &context.local_call_dest_screen;
    static CALL_DEST_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let trace = *CALL_DEST_DEBUG
        .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_CALL_DEST_DEBUG"));
    if trace {
        eprintln!(
            "TRUST_CALL_DEST_DEBUG: {} screen_empty={} owner={} screened={:?} pinning={:?}",
            func.def_path,
            screen.is_empty(),
            context.def_path,
            screen.local_free_fns,
            screen.contract_pinning_callees,
        );
    }
    if screen.is_empty()
        || context.def_path != func.def_path
        || crate::generate::cached_terminator_presence_for_body(&expanded_func.body)
            .is_some_and(|tp| !tp.has_call)
    {
        return (Vec::new(), None);
    }
    crate::with_vcgen_context(context, || {
        let func = expanded_func;
        let mut dests = Vec::new();
        for (block_index, block) in func.body.blocks.iter().enumerate() {
            let Terminator::Call {
                func: callee,
                args,
                dest,
                target: Some(_),
                is_foreign: false,
                callee_identity: Some(identity),
                span,
                ..
            } = &block.terminator
            else {
                continue;
            };
            if !screen.local_free_fns.contains(&(identity.stable_crate_id, identity.def_index)) {
                continue;
            }
            // Whether some producer may have modeled this destination. MIRRORS
            // the same-crate-callee producers of `generate::semantic_guard`'s
            // call arm (return upper/lower bound, constant set, injected callee
            // postcondition) and the summary readers of `generate::unwrap_panic`
            // / `callee_summaries` (discriminant, bool-predicate,
            // trivial-setter) and the field-read summary (asked of THIS call,
            // since its call-site gates decide whether the destination is
            // modeled at all). The lookups key on the SAME rendered callee
            // string those producers key on, which is the point: this asks what
            // generation saw. A producer added there and not here over-withholds
            // a genuine counterexample (a precision loss, never a proof). The
            // SCREENED set itself is identity-keyed.
            //
            // Trust (2026-09-30): the body-derived summaries are read only at a call
            // that reaches the summarized body (`crate::call_reaches_summarized_body`,
            // the producers' own gate); one that exists by name without reaching it
            // models nothing, and counting it pinned would keep a counterexample
            // that chose this destination.
            //
            // The contract arm (2026-09-28) asks what the injector EMITTED HERE,
            // not what the callee's summary says in general: the summary must
            // determine the result (`summary_pins_result`, decided when the
            // screen was built) AND the injector's call-site half must admit this
            // very call — a site it refuses (a twice-written dest, an actual that
            // reads the dest) gets no clause, so its destination is free.
            let pinned_by_contract =
                screen.contract_pinning_callees.get(callee.as_str()).is_some_and(|&formals| {
                    crate::generate::callee_postcondition_site_admits(func, dest, formals, args)
                        && screen
                            .contract_pinning_entries
                            .get(callee.as_str())
                            .is_none_or(|binding| binding.replacements(func, args, dest).is_some())
                });
            let summarized = crate::call_reaches_summarized_body(&block.terminator)
                && (crate::callee_return_upper_bound(callee).is_some()
                    || crate::callee_return_lower_bound(callee).is_some()
                    || crate::callee_return_const_set(callee).is_some()
                    || crate::callee_return_disc_summary(callee).is_some()
                    || crate::callee_return_bool_pred(callee).is_some()
                    || crate::callee_setter_summary(callee).is_some());
            let pinned = pinned_by_contract
                || summarized
                || crate::generate::return_field_call_is_modeled(func, block);
            if trace {
                eprintln!("TRUST_CALL_DEST_DEBUG:   call {callee} dest={dest:?} pinned={pinned}");
            }
            if pinned {
                continue;
            }
            if dest.projections.iter().any(|projection| matches!(projection, Projection::Deref)) {
                continue;
            }
            // A returned reference/pointer's POINTEE is memory, not this
            // value; only by-value results are screened (memo scope).
            let by_value = crate::local_ty_ref(func, dest.local).is_some_and(|ty| {
                !matches!(ty, trust_types::Ty::Ref { .. } | trust_types::Ty::RawPtr { .. })
            });
            if !by_value {
                continue;
            }
            dests.push(UnpinnedCallDest {
                name: crate::place_to_var_name(func, dest),
                callee: callee.clone(),
                call_span: call_site_is_unique(func, callee, span).then(|| span.clone()),
                precondition_precedes_value: dest.projections.is_empty()
                    && crate::local_defs::unique_defining_block(func, dest.local)
                        == Some(block_index)
                    && !block_reaches_itself(func, block_index),
                influence: call_result_influence(func, dest.local),
            });
        }
        // Trust (2026-10-10, D5-A-TRY-HOP-1): the `?` operator. `let i = f(..)?`
        // lowers to `_5 = f(..)` and `_4 = <Option<_> as Try>::branch(move _5)`,
        // and the index reads `(_4 as Continue).0`. Core's `branch` is a pure
        // re-wrap of its argument (`Some(v) -> Continue(v)`, `None -> Break(None)`;
        // `Ok`/`Err` likewise), so `_4` is a function of `_5` alone: when `_5` is
        // an unpinned same-crate result, so is `_4`. No model of `branch` ties the
        // two in the query, so before this a model over `_4` alone (astream-agent
        // `fork.rs:107`, `Continue(0)` beside an empty slice) was not seen to
        // depend on `f` and stood as FAILED. The hop is admitted ONLY for core's
        // authenticated `Try::branch` (`SysrootItem::TryBranch` on a real-sysroot
        // key, never a spelling); any other callee's result stays as free as it
        // was. Like the rest of the screen this only withholds a model, as a held
        // Unknown, and grants nothing.
        // PERF-COMPILER-VCGEN-704: pre-collect `Try::branch` sites once when `dests`
        // is non-empty so the fixpoint loop only iterates over `Try::branch` sites
        // (zero iterations when the body has no `Try::branch` calls).
        if !dests.is_empty() {
            let mut try_branches = Vec::new();
            for block in &func.body.blocks {
                let Terminator::Call { callee_key: Some(key), args, dest, target: Some(_), .. } =
                    &block.terminator
                else {
                    continue;
                };
                if !key.krate_is_real_sysroot
                    || key.sysroot_item != Some(trust_types::SysrootItem::TryBranch)
                {
                    continue;
                };
                let [Operand::Move(arg) | Operand::Copy(arg)] = args.as_slice() else {
                    continue;
                };
                if arg.projections.iter().any(|p| matches!(p, Projection::Deref))
                    || dest.projections.iter().any(|p| matches!(p, Projection::Deref))
                {
                    continue;
                }
                let by_value = crate::local_ty_ref(func, dest.local).is_some_and(|ty| {
                    !matches!(ty, trust_types::Ty::Ref { .. } | trust_types::Ty::RawPtr { .. })
                });
                if !by_value {
                    continue;
                }
                try_branches.push((dest, crate::place_to_var_name(func, arg)));
            }
            let mut grew = !try_branches.is_empty();
            while grew {
                grew = false;
                for (dest, arg_name) in &try_branches {
                    let Some(source) = dests.iter().find(|d| d.names_value(arg_name)) else {
                        continue;
                    };
                    let name = crate::place_to_var_name(func, dest);
                    if dests.iter().any(|d| d.name == name) {
                        continue;
                    }
                    let hop = UnpinnedCallDest {
                        name,
                        callee: source.callee.clone(),
                        // The hop is not a call to `callee`: no precondition row of
                        // its own, and none exempted.
                        call_span: None,
                        precondition_precedes_value: false,
                        influence: call_result_influence(func, dest.local),
                    };
                    dests.push(hop);
                    grew = true;
                }
            }
        }
        if trace {
            for dest in &dests {
                eprintln!(
                    "TRUST_CALL_DEST_DEBUG:   screened {} ({}) influence={:?}",
                    dest.name, dest.callee, dest.influence
                );
            }
        }
        let body = (!dests.is_empty()).then(|| CallDestBody::of(func));
        (dests, body)
    })
}

/// Whether `func` has exactly one call to `callee` at `span` — so a
/// `Precondition { callee }` row located at `span` can only be that call's.
fn call_site_is_unique(func: &VerifiableFunction, callee: &str, span: &SourceSpan) -> bool {
    func.body
        .blocks
        .iter()
        .filter(|block| match &block.terminator {
            Terminator::Call { func: called, span: at, .. }
            | Terminator::TailCall { func: called, span: at, .. } => called == callee && at == span,
            _ => false,
        })
        .count()
        == 1
}

/// Push non-unwind successor block IDs of `term` into `pending` without allocating
/// a temporary `Vec<BlockId>`. Matches `trust_types::block_successors_list`.
fn push_non_unwind_successors(term: &Terminator, pending: &mut Vec<trust_types::BlockId>) {
    match term {
        Terminator::Goto(target)
        | Terminator::Assert { target, .. }
        | Terminator::Drop { target, .. } => pending.push(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            pending.extend(targets.iter().map(|&(_, b)| b));
            pending.push(*otherwise);
        }
        Terminator::Call { target, .. } => {
            pending.extend(target.iter().copied());
        }
        Terminator::Opaque { targets, .. } => {
            pending.extend(targets.iter().copied());
        }
        Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | Terminator::Resume
        | _ => {}
    }
}

/// Whether some control-flow path leaves `func.body.blocks[start]` and comes
/// back to it. Unwind edges are not followed: a cleanup path does not re-enter
/// the call. A successor that names no block of the body is treated as a
/// cycle (fail closed: the exemption it would license is not granted).
fn block_reaches_itself(func: &VerifiableFunction, start: usize) -> bool {
    let Some(start_block) = func.body.blocks.get(start) else {
        return true;
    };
    let index_of: Option<FxHashMap<usize, usize>> = func
        .body
        .blocks
        .iter()
        .enumerate()
        .any(|(index, block)| block.id.0 != index)
        .then(|| {
            func.body
                .blocks
                .iter()
                .enumerate()
                .map(|(index, block)| (block.id.0, index))
                .collect()
        });
    let mut seen = vec![false; func.body.blocks.len()];
    let mut pending = Vec::new();
    push_non_unwind_successors(&start_block.terminator, &mut pending);
    while let Some(next) = pending.pop() {
        let Some(index) = block_index_of(func, &index_of, next.0) else {
            return true;
        };
        if index == start {
            return true;
        }
        if std::mem::replace(&mut seen[index], true) {
            continue;
        }
        push_non_unwind_successors(&func.body.blocks[index].terminator, &mut pending);
    }
    false
}

/// S1: whether `vc`'s obligation record carries a [`PathGuardTerm::Collapsed`]
/// path term (the path-guard walk lost the block's guards).
fn record_has_collapsed_path(vc: &VerificationCondition) -> bool {
    vc.obligation.as_ref().is_some_and(|record| {
        record.wrappers.iter().any(|wrapper| {
            matches!(wrapper, ObligationWrapper::PathGuardOr { paths }
                if paths.iter().any(|path| matches!(path, PathGuardTerm::Collapsed)))
        })
    })
}

/// S2: the body's loop-carried join symbols, or the fallback for a body that has
/// a loop and no exact answer. A body with no loop has none, whatever its size.
fn loop_carried_joins(func: &VerifiableFunction) -> LoopJoins {
    let n_blocks = func.body.blocks.len();
    if !func.body.blocks.iter().enumerate().any(|(i, b)| {
        crate::generate::any_full_graph_terminator_target(&b.terminator, |t| {
            t.0 <= i && t.0 < n_blocks
        })
    }) {
        return LoopJoins::Exact { joins: FxHashMap::default(), shallow: None };
    }
    let detail = if n_blocks > MAX_BLOCKS || func.body.locals.len() > MAX_LOCALS {
        "loop-carried join analysis exceeds its bound"
    } else {
        match crate::generate::StmtVersionCtx::build(func)
            .loop_carried_join_symbols(func, MAX_BLOCKS * MAX_LOCALS)
        {
            Some(joins) => {
                let shallow = if joins.is_empty() {
                    None
                } else {
                    crate::abstract_interp::transfer::shallow_ascent(
                        func,
                        SHALLOW_SWEEPS,
                        SHALLOW_HORIZON_PASSES,
                    )
                    .map(|states| {
                        let headers: FxHashSet<usize> = joins.values().copied().collect();
                        states
                            .into_iter()
                            .filter(|(block, _)| headers.contains(&block.0))
                            .map(|(block, state)| (block.0, state))
                            .collect()
                    })
                };
                return LoopJoins::Exact { joins, shallow };
            }
            None => "loop-carried join analysis is unavailable or exceeds its bound",
        }
    };
    // Dominance-proved natural loops only: a lower-numbered successor is not a
    // loop, and a body with no loop keeps every row as it is.
    let loops = crate::termination::detect_loops(&func.body);
    if loops.is_empty() {
        return LoopJoins::Exact { joins: FxHashMap::default(), shallow: None };
    }
    let loop_blocks: FxHashSet<usize> =
        loops.iter().flat_map(|l| l.body_blocks.iter().map(|b| b.0)).collect();
    LoopJoins::Unavailable { detail, tracked: loop_tracked_names(func, &loop_blocks) }
}

/// S2 fallback: the base spelling of every local, marked when a block of
/// `loop_blocks` writes it or the body takes its address anywhere (a write through
/// the pointer is a write the loop may make). `None` when a loop block has an
/// effect that names no destination this scan can read.
fn loop_tracked_names(
    func: &VerifiableFunction,
    loop_blocks: &FxHashSet<usize>,
) -> Option<Vec<(String, bool)>> {
    let mut locals: BTreeSet<usize> = BTreeSet::new();
    for block in &func.body.blocks {
        let in_loop = loop_blocks.contains(&block.id.0);
        for statement in &block.stmts {
            if let Statement::Assign {
                rvalue: Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place),
                ..
            } = statement
            {
                locals.insert(place.local);
            }
            if !in_loop {
                continue;
            }
            match statement {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => {
                    locals.insert(place.local);
                }
                Statement::StorageLive(local) | Statement::StorageDead(local) => {
                    locals.insert(*local);
                }
                Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => return None,
            }
        }
        if !in_loop {
            continue;
        }
        match &block.terminator {
            Terminator::Call { dest, .. } => {
                locals.insert(dest.local);
            }
            Terminator::Drop { place, .. } => {
                locals.insert(place.local);
            }
            Terminator::TailCall { .. } => {
                locals.insert(0);
            }
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Assert { .. }
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => {}
            _ => return None,
        }
    }
    Some(
        func.body
            .locals
            .iter()
            .map(|d| {
                (crate::place_to_var_name(func, &Place::local(d.index)), locals.contains(&d.index))
            })
            .collect(),
    )
}

/// The outcome of a bounded scan of a query's variables.
enum NameScan<'f> {
    Hit(&'f str),
    Miss,
    /// The query has more than [`MAX_FORMULA_NODES`] nodes; the caller fails closed.
    Exceeded,
}

/// Walk `formula`'s variables (full SSA spelling) until `hit` accepts one.
fn scan_vars<'f>(formula: &'f Formula, mut hit: impl FnMut(&'f str) -> bool) -> NameScan<'f> {
    let mut pending = vec![formula];
    let mut visited = 0usize;
    while let Some(formula) = pending.pop() {
        visited += 1;
        if visited > MAX_FORMULA_NODES {
            return NameScan::Exceeded;
        }
        let name = match formula {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(name, _) => Some(name.as_str()),
            _ => None,
        };
        if let Some(name) = name
            && hit(name)
        {
            return NameScan::Hit(name);
        }
        trust_types::for_each_formula_child(formula, |child| pending.push(child));
    }
    NameScan::Miss
}

/// S1: whether the L0 row (`kind`, recorded violation `body`) is the obligation
/// the recordless `HardenedBoundary` twin `twin` stands over: the twin's MIR
/// assert is that kind's check family, and every variable of `body` occurs in
/// the twin's own query. A twin of another obligation at the same span (another
/// family, or other operands) does not match. Bounded; a scan past the bound
/// does not match.
fn twin_sibling_matches(twin: &VerificationCondition, kind: &VcKind, body: &Formula) -> bool {
    let VcKind::HardenedBoundary { callee, .. } = &twin.kind else { return false };
    let Some(message) = trust_types::hardened_mir_assert_message(callee) else { return false };
    let matches_family = match kind {
        VcKind::ArithmeticOverflow { op, .. } | VcKind::ShiftOverflow { op, .. } => {
            if !message.starts_with("Overflow(") {
                false
            } else {
                use std::io::Write;
                let mut buf = [0u8; 32];
                let mut cursor = &mut buf[..];
                let _ = write!(cursor, "Overflow({op:?})");
                let len = 32 - cursor.len();
                message.as_bytes() == &buf[..len]
            }
        }
        VcKind::NegationOverflow { .. } => message == "OverflowNeg",
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => message == "BoundsCheck",
        VcKind::DivisionByZero => message == "DivisionByZero",
        VcKind::RemainderByZero => message == "RemainderByZero",
        _ => false,
    };
    if !matches_family {
        return false;
    }
    let mut twin_vars: FxHashSet<&str> = FxHashSet::default();
    if matches!(
        scan_vars(&twin.formula, |name| {
            twin_vars.insert(name);
            false
        }),
        NameScan::Exceeded
    ) {
        return false;
    }
    let mut any = false;
    let scan = scan_vars(body, |name| {
        any = true;
        !twin_vars.contains(name)
    });
    any && matches!(scan, NameScan::Miss)
}

/// S2: whether NO value the `named` joins take within the first
/// [`SHALLOW_SWEEPS`] passes over their loops satisfies `query` — the query
/// conjoined with each join's shallow interval at its header is shown false by
/// interval evaluation ([`interval_infeasible`]). `false` (keep the refutation)
/// when no named join has a bounded shallow interval, or nothing is decided.
fn shallow_clears(
    query: &Formula,
    named: &[&str],
    joins: &FxHashMap<String, usize>,
    shallow: &FxHashMap<usize, crate::abstract_interp::IntervalDomain>,
) -> bool {
    use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain};
    let mut env = IntervalDomain::top();
    let mut bounded = false;
    for &symbol in named {
        let Some(state) = joins.get(symbol).and_then(|h| shallow.get(h)) else {
            // A header the shallow walk never reached: no shallow execution enters
            // the loop, so none holds a value of its join.
            return true;
        };
        if state.is_unreachable {
            return true;
        }
        let base = symbol.split_once('#').map_or(symbol, |(b, _)| b);
        let interval = state.get(base);
        if interval != Interval::TOP {
            bounded = true;
            env.set(symbol.to_owned(), interval);
        }
    }
    bounded && interval_infeasible(query, &env, &FxHashMap::default(), 3)
}

/// An arithmetic definition `v = rhs` among a query's conjuncts: `v` a variable
/// that is not in `env` (never a join the caller bounds) and does not occur in
/// `rhs`, `rhs` an integer term.
fn arithmetic_definition<'f>(
    conjunct: &'f Formula,
    env: &crate::abstract_interp::IntervalDomain,
) -> Option<(&'f str, &'f Formula)> {
    fn integer_term(f: &Formula) -> bool {
        match f {
            Formula::Int(_) | Formula::UInt(_) | Formula::Var(..) => true,
            Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b) => integer_term(a) && integer_term(b),
            Formula::Neg(a) => integer_term(a),
            _ => false,
        }
    }
    let Formula::Eq(a, b) = conjunct else { return None };
    for (lhs, rhs) in [(a, b), (b, a)] {
        if let Formula::Var(name, _) = lhs.as_ref()
            && !env.vars.contains_key(name)
            && integer_term(rhs)
            && matches!(scan_vars(rhs, |n| n == name), NameScan::Miss)
        {
            return Some((name.as_str(), rhs.as_ref()));
        }
    }
    None
}

/// `formula` with every variable `defs` defines replaced by its definition, at
/// most `depth` times over; `None` past the node bound.
fn resolve_definitions<'f>(
    formula: &'f Formula,
    defs: &FxHashMap<&str, &Formula>,
    depth: usize,
) -> Option<std::borrow::Cow<'f, Formula>> {
    if depth == 0
        || defs.is_empty()
        || matches!(scan_vars(formula, |name| defs.contains_key(name)), NameScan::Miss)
    {
        return Some(std::borrow::Cow::Borrowed(formula));
    }
    fn substitute(f: Formula, defs: &FxHashMap<&str, &Formula>, changed: &mut bool) -> Formula {
        if let Formula::Var(name, _) = &f
            && let Some(rhs) = defs.get(name.as_str())
        {
            *changed = true;
            return (*rhs).clone();
        }
        f.map_children(&mut |c| substitute(c, defs, changed))
    }
    let mut current = formula.clone();
    for _ in 0..depth {
        let mut changed = false;
        current = substitute(current, defs, &mut changed);
        if !changed {
            break;
        }
        if matches!(scan_vars(&current, |_| false), NameScan::Exceeded) {
            return None;
        }
    }
    Some(std::borrow::Cow::Owned(current))
}

/// Whether interval evaluation under `env` shows the conjunction `formula`
/// false: some conjunct, with the conjunction's integer definitions substituted
/// ([`arithmetic_definition`]), evaluates to `false`, or some disjunction among
/// them has every disjunct infeasible (each with the definitions in scope, to
/// `depth` levels). A definition is a conjunct of the same query, so reading
/// through it is reasoning within the query. Never proof: an answer only
/// withholds a counterexample.
fn interval_infeasible(
    formula: &Formula,
    env: &crate::abstract_interp::IntervalDomain,
    outer: &FxHashMap<&str, &Formula>,
    depth: usize,
) -> bool {
    let mut conjuncts = Vec::new();
    let mut pending = vec![formula];
    while let Some(f) = pending.pop() {
        if let Formula::And(parts) = f {
            pending.extend(parts.iter().rev());
        } else {
            conjuncts.push(f);
        }
        if conjuncts.len() + pending.len() > MAX_FORMULA_NODES {
            return false;
        }
    }
    let mut defs = outer.clone();
    let mut is_def = vec![false; conjuncts.len()];
    for (i, c) in conjuncts.iter().enumerate() {
        if let Some((name, rhs)) = arithmetic_definition(c, env) {
            defs.entry(name).or_insert(rhs);
            is_def[i] = true;
        }
    }
    conjuncts.iter().zip(is_def).any(|(c, def)| {
        if def {
            return false;
        }
        if let Formula::Or(disjuncts) = c
            && depth > 0
        {
            return !disjuncts.is_empty()
                && disjuncts.iter().all(|d| interval_infeasible(d, env, &defs, depth - 1));
        }
        resolve_definitions(c, &defs, 4).is_some_and(|resolved| {
            crate::abstract_interp::discharge::try_eval_boolean(&resolved, env) == Some(false)
        })
    })
}

/// S2 fallback: the first SSA-versioned variable of `formula` (`base#token` — a
/// join symbol always carries a token) whose base is, or projects from, a
/// marked `tracked` local, or resolves to no local of the body at all.
fn formula_names_versioned_tracked<'f>(
    formula: &'f Formula,
    tracked: &[(String, bool)],
) -> NameScan<'f> {
    scan_vars(formula, |name| {
        let Some((base, _)) = name.split_once('#') else {
            return false;
        };
        let mut resolved = false;
        for (root, marked) in tracked {
            if base_projects_from(base, root) {
                if *marked {
                    return true;
                }
                resolved = true;
            }
        }
        !resolved
    })
}

/// Whether formula base name `name` is local `root` or a projection of it.
fn base_projects_from(name: &str, root: &str) -> bool {
    name == root
        || name.strip_prefix(root).is_some_and(|suffix| {
            suffix.starts_with('.')
                || suffix.starts_with('[')
                || suffix.starts_with('*')
                || suffix.starts_with('@')
                || suffix == "__slice_len"
        })
}

fn loop_transition_query_restriction(formula: &Formula) -> Option<&'static str> {
    let mut pending = vec![formula];
    let mut visited = 0usize;
    while let Some(formula) = pending.pop() {
        visited += 1;
        if visited > MAX_FORMULA_NODES {
            return Some("symbolic loop query dependency analysis exceeds its bound");
        }
        let name = match formula {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(name, _) => Some(name.as_str()),
            _ => None,
        };
        if name.is_some_and(crate::version_token_is_loop_transition_havoc) {
            return Some("query depends on loop-transition havoc from an unmodeled value relation");
        }
        trust_types::for_each_formula_child(formula, |child| pending.push(child));
    }
    None
}

// Removing all dominator-proved backedges must leave a DAG. Otherwise the
// natural-loop write census misses a cycle, so no independence claim follows.
fn unaccounted_cycle(func: &VerifiableFunction, backedges: &BTreeSet<(usize, usize)>) -> bool {
    let block_count = func.body.blocks.len();
    let mut edges = vec![Vec::new(); block_count];
    let mut incoming = vec![0usize; block_count];
    for block in &func.body.blocks {
        let src = block.id.0;
        let mut add_edge = |target: usize| -> bool {
            if target >= block_count {
                return false;
            }
            if !backedges.contains(&(src, target)) {
                edges[src].push(target);
                incoming[target] += 1;
            }
            true
        };
        match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => {
                if !add_edge(target.0) {
                    return true;
                }
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for &(_, target) in targets {
                    if !add_edge(target.0) {
                        return true;
                    }
                }
                if !add_edge(otherwise.0) {
                    return true;
                }
            }
            Terminator::Return => {}
            _ => return true,
        }
    }
    let mut ready = Vec::with_capacity(block_count);
    for (index, &count) in incoming.iter().enumerate() {
        if count == 0 {
            ready.push(index);
        }
    }
    let mut removed = 0;
    while let Some(block) = ready.pop() {
        removed += 1;
        for &target in &edges[block] {
            incoming[target] -= 1;
            if incoming[target] == 0 {
                ready.push(target);
            }
        }
    }
    removed != edges.len()
}

fn place_reads(place: &Place, reads: &mut BTreeSet<usize>) -> Option<()> {
    reads.insert(place.local);
    for projection in &place.projections {
        match projection {
            Projection::Index(local) => {
                reads.insert(*local);
            }
            Projection::Deref
            | Projection::Field(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {}
            _ => return None,
        }
    }
    Some(())
}

fn operand_reads(operand: &Operand, reads: &mut BTreeSet<usize>) -> Option<()> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_reads(place, reads),
        Operand::Constant(_) => Some(()),
        _ => None,
    }
}

fn rvalue_reads(rvalue: &Rvalue) -> Option<BTreeSet<usize>> {
    let mut reads = BTreeSet::new();
    match rvalue {
        Rvalue::Use(a) | Rvalue::UnaryOp(_, a) | Rvalue::Cast(a, _) | Rvalue::Repeat(a, _) => {
            operand_reads(a, &mut reads)?
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => {
            operand_reads(a, &mut reads)?;
            operand_reads(b, &mut reads)?;
        }
        Rvalue::Len(place) | Rvalue::Discriminant(place) => place_reads(place, &mut reads)?,
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                operand_reads(operand, &mut reads)?;
            }
        }
        _ => return None,
    }
    Some(reads)
}

fn reconstruct(body: &Formula, wrappers: &[ObligationWrapper]) -> Option<Formula> {
    // Moved to trust-types (TINV step 7.1) so the kernel gate can replay a record
    // without depending on vcgen; identical behaviour.
    trust_types::ObligationRecord::reconstruct_parts(body, wrappers)
}

#[cfg(test)]
mod tests;

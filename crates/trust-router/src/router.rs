//! The Router struct: dispatches VCs to verification backends.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::*;

use crate::memory_guard::MemoryGuard;
use crate::{BackendSelection, VerificationBackend, constant_folder, routing, ty_backend};

/// Routes VCs to appropriate backends.
///
/// Trust: Backends are stored as `Arc<dyn VerificationBackend>` so one
/// discovered inventory can be shared by several routers. The public
/// constructors accept `Box<dyn VerificationBackend>` and convert to Arc on
/// construction.
///
/// Dispatch is serial, in input order: there is no parallel path, so the
/// order in which a backend sees VCs is a function of the input alone
/// (plan P4).
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VcKind, Formula, Sort, SourceSpan};
/// use trust_router::{Router, constant_folder::ConstantFolderBackend};
///
/// // Create a router with the mock backend
/// let router = Router::with_backends(vec![Box::new(ConstantFolderBackend)]);
///
/// // Build a VC and verify it
/// let vc = VerificationCondition {
///     kind: VcKind::DivisionByZero,
///     function: "my_fn".into(),
///     location: SourceSpan::default(),
///     formula: Formula::Bool(false),
///     contract_metadata: None,
/// obligation: None,
/// };
///
/// let result = router.verify_one(&vc);
/// assert!(result.is_proved());
///
/// // Verify multiple VCs at once
/// let results = router.verify_all(&[vc]);
/// assert_eq!(results.len(), 1);
/// ```
pub struct Router {
    // Trust: Arc storage lets one router hand its backends to another
    // (`arc_backends`) without re-wrapping them.
    backends: Vec<Arc<dyn VerificationBackend>>,
    // Pre-interned backend names aligned 1:1 with `backends`, avoiding repeated
    // `Symbol::intern(backend.name())` lock acquisitions on every `backend_plan`.
    backend_names: Vec<Symbol>,
    // Process memory guard — checks RSS before each solver dispatch.
    memory_guard: Arc<MemoryGuard>,
}

impl Router {
    /// Create a router with the mock backend only.
    ///
    /// For real verification, use `Router::with_backends()` and pass in
    /// concrete backend implementations (e.g. `InProcessAyBackend`).
    pub fn new() -> Self {
        // When the `ay-backend` feature is enabled, register the
        // in-process ay-dpll SMT backend alongside the constant folder; the
        // router selects it through its `can_handle`/`role`. The subprocess
        // backends (`IncrementalAYSession`, `smtlib_backend`) are never
        // registered here: since plan P4 / T4.1 only targo-trust's
        // verify-binary builds one.
        #[allow(unused_mut)]
        let mut backends: Vec<Arc<dyn VerificationBackend>> =
            vec![Arc::new(constant_folder::ConstantFolderBackend)];
        #[cfg(feature = "ay-backend")]
        backends.push(Arc::new(crate::in_process_ay_backend::InProcessAyBackend::new()));
        Self::with_arc_backends(backends)
    }

    /// Create a router with specific backends.
    ///
    /// Accepts `Box<dyn VerificationBackend>` and converts to Arc internally.
    pub fn with_backends(backends: Vec<Box<dyn VerificationBackend>>) -> Self {
        Self::with_arc_backends(backends.into_iter().map(Arc::from).collect())
    }

    /// Trust (R-U Phase D, router convergence): the deterministic
    /// analysis-seam router — a single in-process ay backend with the given
    /// per-VC timeout, and nothing else. The compiler's analysis seams (the R1
    /// oracle, the assert-refutation sweeps) construct their router through
    /// this name so the determinism contract has one definition site:
    /// IN-PROCESS ay only, never a subprocess solver, whose per-VC timeout
    /// made verdicts differ across builds (Failed one build, Unknown the
    /// next). One compiler router that runs ay is not built here: the Liskov
    /// check's, over `discover_router_backends`' four-backend inventory, on
    /// which this same in-process ay handles symbolic Liskov VCs and the
    /// constant folder can decide fully constant ones (plan P4 / T4.1).
    ///
    /// `scale` sets the one effort count that ends an undecided solve (ay
    /// `:rlimit`, `min(C, max(1, k · size))` per query); `timeout_ms` is the
    /// wall-clock backstop.
    #[cfg(feature = "ay-backend")]
    pub fn deterministic_in_process_ay(
        timeout_ms: u64,
        scale: trust_types::determinism::EffortScale,
    ) -> Self {
        Router::with_backends(vec![Box::new(
            crate::in_process_ay_backend::InProcessAyBackend::new()
                .with_timeout(timeout_ms)
                .with_effort_scale(scale),
        )])
    }

    /// Trust: Create a router with Arc-wrapped backends.
    ///
    /// Use this when you already hold Arc-wrapped backends, for example
    /// another router's (`arc_backends`).
    pub fn with_arc_backends(backends: Vec<Arc<dyn VerificationBackend>>) -> Self {
        let backend_names = backends.iter().map(|b| Symbol::intern(b.name())).collect();
        Router { backends, backend_names, memory_guard: Arc::new(MemoryGuard::default()) }
    }

    /// Set a custom memory guard on this router.
    ///
    /// The guard's `check_memory()` is called before each solver dispatch.
    /// Use `MemoryGuard::new(limit_mb)` to set the limit, or
    /// `MemoryGuard::new(0)` to disable enforcement.
    #[must_use]
    pub fn with_memory_guard(mut self, guard: MemoryGuard) -> Self {
        self.memory_guard = Arc::new(guard);
        self
    }

    /// Get a reference to the router's memory guard.
    #[must_use]
    pub fn memory_guard(&self) -> &MemoryGuard {
        self.memory_guard.as_ref()
    }

    /// Trust: Get a clone of the Arc-wrapped backend list.
    ///
    /// Useful for building another router over the same inventory without
    /// re-wrapping.
    pub fn arc_backends(&self) -> Vec<Arc<dyn VerificationBackend>> {
        self.backends.clone()
    }

    /// Trust: Return the backend selection plan for a VC.
    ///
    /// The plan is ordered by router heuristics, not by insertion order:
    /// the preferred backend family for the VC's proof level is tried first,
    /// then fallback families, then general-purpose backends.
    pub fn backend_plan(&self, vc: &VerificationCondition) -> Vec<BackendSelection> {
        // Trust (v6/D2): the concurrency kinds carry no execution or memory model,
        // so no backend is planned for them (see `unsupported_mir_unknown`).
        if matches!(&vc.kind, VcKind::UnsupportedMir { .. })
            || crate::backend_trait::is_unmodeled_concurrency_kind(&vc.kind)
        {
            return Vec::new();
        }

        routing::backend_plan(&self.backends, &self.backend_names, vc)
    }

    /// Verify all VCs, returning paired results.
    pub fn verify_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.verify_all_with_deadline(vcs, None)
    }

    /// Verify all VCs under an optional per-batch wall-clock deadline.
    ///
    /// Once `deadline` has passed, every remaining VC short-circuits to a
    /// sound `Unknown` verdict instead of being dispatched to a solver. This
    /// bounds the time a single pathological function (e.g. a machine-generated
    /// body with hundreds of thousands of obligations, each able to consume the
    /// full per-VC solver timeout) can spend in the verifier. Soundness is
    /// preserved: a budget-exceeded obligation is reported `Unknown`, never
    /// `Proved`.
    pub fn verify_all_with_deadline(
        &self,
        vcs: &[VerificationCondition],
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        if vcs.is_empty() {
            return Vec::new();
        }
        if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
            return vcs.iter().map(|vc| (vc.clone(), budget_exceeded_unknown(vc))).collect();
        }

        // Trust: shared-prefix batch fast path. When this router's SOLE backend
        // is one that shares a per-function assertion prefix across a batch
        // (the incremental AY session), route the whole VC set through its
        // `verify_batch` so each function's common facts are asserted ONCE at
        // the solver's base scope (M·N → M+N assert work). This is engaged only
        // in the single-backend configuration, where there is no fallback-chain
        // ambiguity — every handled VC goes to that one backend — so the verdict
        // is provably identical to the per-VC path. Any router with >1 backend
        // (the production multi-backend router) takes the unchanged per-VC loop
        // below. The deadline is still honored: a passed deadline short-circuits
        // before dispatch.
        if let Some(backend) = self.sole_shared_prefix_batch_backend() {
            return Self::batch_via_backend_with_deadline(backend, vcs, deadline);
        }

        // Single-VC fast path: skip dedup bucketing, `VcKind::description`
        // formatting, formula hashing, and intermediate slot/plan vectors.
        if let [vc] = vcs {
            let result = if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                budget_exceeded_unknown(vc)
            } else {
                self.verify_one(vc)
            };
            return vec![(vc.clone(), result)];
        }

        // Trust (audit rec 4): structural dedup before sequential dispatch.
        //
        // Identical safety VCs (the same obligation up to renaming of bound
        // variables) are collapsed to ONE solve and the shared verdict is
        // fanned out to every duplicate, within this batch only (nothing is
        // carried from one batch, or one function, to the next).
        //
        // Soundness: `vc_dedup::dedup_groups` merges two VCs only when they are
        // alpha-equivalent obligations AND carry the same routing requirements
        // (the plan signature below). Retain the preflight `backend_plan`
        // computed for each VC so `verify_one_with_cached_plan` never re-runs
        // `backend.can_handle` on group representatives.
        let mut cached_plans: Vec<Option<Vec<BackendSelection>>> = Vec::with_capacity(vcs.len());
        cached_plans.resize_with(vcs.len(), || None);
        let groups = crate::vc_dedup::dedup_groups(vcs, |i| {
            let plan = self.backend_plan(&vcs[i]);
            let sig = Self::plan_signature_from_plan(&plan);
            cached_plans[i] = Some(plan);
            sig
        });

        // Output slots, one per input VC, filled by original index.
        let mut slots: Vec<Option<VerificationResult>> = Vec::with_capacity(vcs.len());
        slots.resize_with(vcs.len(), || None);

        for group in &groups {
            let rep_idx = group.representative;
            let rep_vc = &vcs[rep_idx];
            // Solve the representative once (honoring the deadline exactly as
            // the per-VC loop would).
            let rep_result = if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                budget_exceeded_unknown(rep_vc)
            } else {
                self.verify_one_with_cached_plan(rep_vc, cached_plans[rep_idx].as_deref())
            };

            // Fan the verdict out to every member of the group. Members denote
            // the same obligation, so the verdict is identical. We still honor
            // the deadline per-member: if it lapsed mid-group, late members
            // degrade to a sound `Unknown` rather than receiving the
            // representative's verdict — matching the per-VC loop's behavior
            // where each VC re-checks the deadline before dispatch. Move
            // `rep_result` on the final member so unique VCs avoid deep-cloning
            // proof certificates or counterexamples.
            let mut rep_opt = Some(rep_result);
            let last_pos = group.members.len().saturating_sub(1);
            for (pos, &member) in group.members.iter().enumerate() {
                let use_rep = member == group.representative
                    || !deadline.is_some_and(|at| std::time::Instant::now() >= at);
                let member_result = if use_rep {
                    if pos == last_pos {
                        rep_opt.take().unwrap_or_else(|| budget_exceeded_unknown(&vcs[member]))
                    } else {
                        rep_opt
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|| budget_exceeded_unknown(&vcs[member]))
                    }
                } else {
                    budget_exceeded_unknown(&vcs[member])
                };
                slots[member] = Some(member_result);
            }
        }

        // Reassemble in original order; every slot is filled because every
        // input index appears in exactly one group.
        vcs.iter()
            .zip(slots)
            .map(|(vc, slot)| {
                let result = slot.unwrap_or_else(|| {
                    // Defensive: a missing slot should be impossible given the
                    // dedup_groups partition invariant, but fail closed to a
                    // sound Unknown rather than panic.
                    VerificationResult::Unknown {
                        solver: Symbol::intern("router-dedup"),
                        time_ms: 0,
                        reason: "dedup slot unfilled".to_string(),
                    }
                });
                (vc.clone(), result)
            })
            .collect()
    }

    /// Trust: The router's sole backend IFF it exists, is the only backend, and
    /// shares a per-function assertion prefix across a batch (so `verify_batch`
    /// is a real throughput win, not the default per-VC map). Returns `None`
    /// otherwise — including any multi-backend router — so the shared-prefix
    /// fast path engages only where it is unambiguously sound.
    fn sole_shared_prefix_batch_backend(&self) -> Option<&Arc<dyn VerificationBackend>> {
        match self.backends.as_slice() {
            [only] if only.supports_shared_prefix_batch() => Some(only),
            _ => None,
        }
    }

    /// Trust: Dispatch `vcs` through a single backend's `verify_batch`, honoring
    /// `deadline` for any VC not reached when the deadline lapses. The
    /// unroutable-VC guard runs per VC exactly as in the per-VC path, so
    /// unsupported MIR and data-race VCs are never sent to the backend.
    fn batch_via_backend_with_deadline(
        backend: &Arc<dyn VerificationBackend>,
        vcs: &[VerificationCondition],
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        // Partition into VCs the backend should solve (after the unroutable-VC
        // short-circuit) vs. those resolved here, preserving order.
        let mut to_batch: Vec<VerificationCondition> = Vec::with_capacity(vcs.len());
        let mut to_batch_indices: Vec<usize> = Vec::with_capacity(vcs.len());
        let mut results: Vec<Option<VerificationResult>> = (0..vcs.len()).map(|_| None).collect();

        for (i, vc) in vcs.iter().enumerate() {
            if let Some(result) = unroutable_vc_unknown(vc) {
                results[i] = Some(result);
            } else if !backend.can_handle(vc) {
                // Match the per-VC fallback-chain outcome: no eligible backend.
                results[i] = Some(trust_types::determinism::StopCause::Unsupported.unknown_result(
                    "none",
                    0,
                    "no backend can handle this VC",
                ));
            } else {
                to_batch_indices.push(i);
                to_batch.push(vc.clone());
            }
        }

        if !to_batch.is_empty() {
            let batched = backend.verify_batch(&to_batch);
            for (idx, (_, result)) in to_batch_indices.iter().zip(batched) {
                results[*idx] = Some(result);
            }
        }

        vcs.iter()
            .zip(results)
            .map(|(vc, r)| {
                let result = r.unwrap_or_else(|| {
                    // Deadline lapsed (or a missing slot): fail closed to a sound
                    // Unknown, matching the per-VC deadline behavior.
                    if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                        budget_exceeded_unknown(vc)
                    } else {
                        VerificationResult::Unknown {
                            solver: "router-batch".into(),
                            time_ms: 0,
                            reason: "batch slot unfilled".to_string(),
                        }
                    }
                });
                (vc.clone(), result)
            })
            .collect()
    }

    /// Trust: A hashable signature of a VC's routing requirements, used by the
    /// sequential-dispatch dedup to avoid merging VCs that would be routed to
    /// different backends. Two VCs with the same alpha-equivalent obligation but
    /// different backend plans (e.g. one handled by an SMT backend, the other
    /// only by the temporal backend) must NOT share a verdict, so the dedup keys
    /// on this.
    ///
    /// The signature is the ordered list of `(backend name, can_handle)` pairs
    /// from the backend plan — exactly the routing inputs that determine which
    /// backend ultimately produces the verdict in `verify_one`.
    fn plan_signature_from_plan(plan: &[BackendSelection]) -> Vec<(trust_types::Symbol, bool)> {
        plan.iter().map(|sel| (sel.name, sel.can_handle)).collect()
    }

    /// Verify a single VC by finding an appropriate backend.
    ///
    /// Checks process RSS against the configured memory limit
    /// before dispatching to a solver backend. Returns an Unknown result
    /// with the memory error reason if the limit is exceeded.
    pub fn verify_one(&self, vc: &VerificationCondition) -> VerificationResult {
        self.verify_one_with_cached_plan(vc, None)
    }

    fn verify_one_with_cached_plan(
        &self,
        vc: &VerificationCondition,
        cached_plan: Option<&[BackendSelection]>,
    ) -> VerificationResult {
        if let Some(result) = unroutable_vc_unknown(vc) {
            return result;
        }

        let eligible_backends = match cached_plan {
            Some(plan) => routing::eligible_backends_from_plan(&self.backends, vc, plan),
            None => routing::eligible_backends(&self.backends, vc),
        };
        Self::verify_eligible_with_backend_fallback(
            &eligible_backends,
            self.memory_guard.as_ref(),
            |backend| backend.verify(vc),
        )
    }

    /// Verify temporal VCs that carry an associated StateMachine.
    ///
    /// Unlike `verify_all`, these VCs were produced by the temporal discovery
    /// pipeline and each comes with an explicit `StateMachine`. The TyBackend
    /// requires this machine for BFS exploration and deadlock/dead-state analysis.
    ///
    /// Dispatches through the standard backend selection: if a Temporal backend
    /// is registered, it uses `TyBackend::verify_with_machine`; otherwise
    /// falls through to general backends.
    pub fn verify_temporal_vcs(
        &self,
        vcs: &[(VerificationCondition, trust_temporal::StateMachine)],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|(vc, machine)| {
                if let Some(result) = unroutable_vc_unknown(vc) {
                    return (vc.clone(), result);
                }

                // Try TyBackend::verify_with_machine directly for
                // temporal VCs with an accompanying state machine.
                let result = ty_backend::TyBackend::verify_with_machine(vc, machine);
                (vc.clone(), result)
            })
            .collect()
    }

    // -------------------------------------------------------------------
    // Memory guard integration
    // -------------------------------------------------------------------

    fn verify_eligible_with_backend_fallback<F>(
        eligible_backends: &[&Arc<dyn VerificationBackend>],
        memory_guard: &MemoryGuard,
        mut verify: F,
    ) -> VerificationResult
    where
        F: FnMut(&Arc<dyn VerificationBackend>) -> VerificationResult,
    {
        // Ordinary router dispatch keeps FallbackChain's retry/simplify policy
        // out of the path: only later capable backends are tried here.
        let mut last_non_definitive = None;
        let mut dispatched_any = false;

        for backend in eligible_backends {
            if let Some(result) = Self::check_memory_limit_for(memory_guard) {
                return result;
            }

            dispatched_any = true;
            let result = verify(backend);
            if router_result_is_definitive(&result) {
                return result;
            }
            last_non_definitive = Some(result);
        }

        if dispatched_any {
            return last_non_definitive.unwrap_or_else(|| VerificationResult::Unknown {
                solver: "none".into(),
                time_ms: 0,
                reason: "no backend produced a verification result".to_string(),
            });
        }

        trust_types::determinism::StopCause::Unsupported.unknown_result(
            "none",
            0,
            "no backend can handle this VC",
        )
    }

    fn check_memory_limit_for(memory_guard: &MemoryGuard) -> Option<VerificationResult> {
        match memory_guard.check_memory() {
            Ok(_snapshot) => None,
            Err(crate::memory_guard::MemoryGuardError::LimitExceeded {
                current_mb,
                limit_mb,
                peak_mb,
            }) => {
                let result = trust_types::determinism::StopCause::RssBackstop.unknown_result(
                    "memory-guard",
                    0,
                    &format!(
                        "memory limit exceeded: {current_mb}MB used, {limit_mb}MB limit \
                         (peak: {peak_mb}MB) — skipping solver dispatch"
                    ),
                );
                // Plan §2: an RSS backstop fired, whether or not this result
                // becomes a published row.
                trust_types::determinism::note_result(ROUTER_LANE, &result);
                Some(result)
            }
            Err(_query_err) => {
                // Query failure is non-fatal: proceed with dispatch.
                // The guard already logs warnings to stderr.
                None
            }
        }
    }
}

fn unroutable_vc_unknown(vc: &VerificationCondition) -> Option<VerificationResult> {
    crate::backend_trait::unsupported_mir_unknown(vc, "router", 0)
}

fn router_result_is_definitive(result: &VerificationResult) -> bool {
    result.is_proved() || result.is_failed()
}

impl Default for Router {
    fn default() -> Self {
        Self::new()
    }
}

/// Sound fallback verdict when a per-function wall-clock budget is exceeded: the
/// obligation is reported `Unknown` (never `Proved` or `Failed`), so degrading a
/// pathological function under time pressure can never produce an unsound proof.
///
/// Which obligations land here depends on how fast the ones before them ran, so
/// the stop is `wall-backstop`: the unit that carries it is not reproducible.
fn budget_exceeded_unknown(vc: &VerificationCondition) -> VerificationResult {
    let result = trust_types::determinism::StopCause::WallBackstop.unknown_result(
        "trust-budget",
        0,
        &format!(
            "per-function wall-clock verification budget exceeded before dispatching obligation for `{}`",
            vc.function
        ),
    );
    // Plan §2: the wall backstop fired, whether or not this result becomes a
    // published row (an internal lane that routes through here consumes it).
    trust_types::determinism::note_result(ROUTER_LANE, &result);
    result
}

/// The backstop-ledger lane the router reports its own backstops under (the
/// per-function deadline before dispatch, the memory guard).
const ROUTER_LANE: &str = "router";

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    /// R-U Phase D pin: the named deterministic analysis-seam constructor is
    /// extensionally the single-backend in-process-ay `with_backends` form the
    /// compiler seams used inline — one backend, same name, nothing else. A
    /// second backend or a different backend identity appearing here means the
    /// determinism contract's definition site changed out from under the
    /// migrated seams.
    #[cfg(feature = "ay-backend")]
    #[test]
    fn deterministic_in_process_ay_is_the_inline_form() {
        let scale = trust_types::determinism::EffortScale { conflicts_per_node: 7 };
        let named = Router::deterministic_in_process_ay(1234, scale);
        let inline = Router::with_backends(vec![Box::new(
            crate::in_process_ay_backend::InProcessAyBackend::new()
                .with_timeout(1234)
                .with_effort_scale(scale),
        )]);
        assert_eq!(named.backends.len(), 1, "exactly one backend — determinism seam");
        assert_eq!(inline.backends.len(), 1);
        assert_eq!(named.backends[0].name(), inline.backends[0].name());
        assert_eq!(named.backends[0].role(), inline.backends[0].role());
    }

    struct CountingBackend {
        can_handle_calls: Arc<AtomicUsize>,
        verify_calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for CountingBackend {
        fn name(&self) -> &str {
            "counting"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            self.can_handle_calls.fetch_add(1, Ordering::SeqCst);
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.verify_calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Proved {
                solver: "counting".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    fn unsupported_mir_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "TerminatorKind::Yield".to_string(),
                detail: "valid MIR terminator preserved as opaque TrustIr".to_string(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn unsupported_mir_backend_plan_does_not_query_backends() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        let plan = router.backend_plan(&unsupported_mir_vc());

        assert!(plan.is_empty());
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn unsupported_mir_verify_one_does_not_dispatch_backend() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        let result = router.verify_one(&unsupported_mir_vc());

        assert!(
            matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
        );
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    fn division_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: function.into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn verify_all_with_past_deadline_degrades_to_unknown_without_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let vcs = vec![division_vc("a"), division_vc("b"), division_vc("c")];

        // A deadline already in the past: every VC must short-circuit to Unknown.
        let past = std::time::Instant::now() - std::time::Duration::from_secs(1);
        let results = router.verify_all_with_deadline(&vcs, Some(past));

        assert_eq!(results.len(), 3);
        assert!(results.iter().all(|(_, r)| matches!(
            r,
            VerificationResult::Unknown { reason, .. } if reason.contains("budget exceeded")
        )));
        // Soundness: a budget-exceeded obligation is never reported Proved, and the
        // solver backend is never dispatched once the deadline has passed.
        assert!(!results.iter().any(|(_, r)| r.is_proved()));
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn verify_all_without_deadline_dispatches_normally() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        // Two DISTINCT obligations (different free vars) so the sequential-dedup
        // pass keeps them separate: this test asserts that every distinct VC is
        // dispatched once when there is no deadline.
        let vcs = vec![distinct_division_vc("a"), distinct_division_vc("b")];

        // No deadline (and equivalently a far-future deadline) dispatches every VC.
        let results = router.verify_all(&vcs);
        let future = std::time::Instant::now() + std::time::Duration::from_secs(3600);
        let future_results = router.verify_all_with_deadline(&vcs, Some(future));

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|(_, r)| r.is_proved()));
        assert!(future_results.iter().all(|(_, r)| r.is_proved()));
        // Two distinct VCs, run twice (once via verify_all, once with a future
        // deadline) => 4 solver dispatches, none coalesced.
        assert_eq!(verify_calls.load(Ordering::SeqCst), 4);
    }

    /// A division-by-zero VC whose formula embeds a distinct free variable, so
    /// two of them are NOT alpha-equivalent and never deduped. The `function`
    /// label is deliberately ignored by the dedup (it is not verdict-affecting),
    /// so distinctness must come from the formula.
    fn distinct_division_vc(var_name: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: var_name.into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var(var_name.into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn verify_all_dedups_identical_vcs_to_one_solve_and_fans_out() {
        // Three byte-identical obligations (same kind + same formula). The
        // sequential-dedup pass must collapse them to ONE solver dispatch and
        // fan the shared verdict out to all three, preserving order/count.
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        // `division_vc` differs only by function label, which is NOT part of the
        // obligation identity, so all three are the same obligation `Bool(true)`.
        let vcs = vec![division_vc("a"), division_vc("b"), division_vc("c")];
        let results = router.verify_all(&vcs);

        // Output contract: one result per input, in original order.
        assert_eq!(results.len(), 3);
        for (i, (vc, r)) in results.iter().enumerate() {
            assert_eq!(vc.function.as_str(), vcs[i].function.as_str());
            assert!(r.is_proved(), "fanned-out verdict must match the representative");
        }
        // Exactly ONE solver dispatch for the three duplicates.
        assert_eq!(
            verify_calls.load(Ordering::SeqCst),
            1,
            "identical VCs must collapse to a single solve"
        );
    }

    #[test]
    fn verify_all_does_not_dedup_distinct_vcs() {
        // Distinct obligations must each be solved: no false coalescing.
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        let vcs =
            vec![distinct_division_vc("x"), distinct_division_vc("y"), distinct_division_vc("z")];
        let results = router.verify_all(&vcs);

        assert_eq!(results.len(), 3);
        assert!(results.iter().all(|(_, r)| r.is_proved()));
        assert_eq!(
            verify_calls.load(Ordering::SeqCst),
            3,
            "three distinct obligations must each be solved"
        );
    }

    #[test]
    fn verify_all_dedup_preserves_order_and_count_with_mixed_batch() {
        // Batch [A, B, A, C, B]: A,B,C distinct; A appears twice, B twice. Dedup
        // must produce exactly one result per input in input order, and dispatch
        // only the 3 unique obligations.
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        let vcs = vec![
            distinct_division_vc("a"),
            distinct_division_vc("b"),
            distinct_division_vc("a"),
            distinct_division_vc("c"),
            distinct_division_vc("b"),
        ];
        let results = router.verify_all(&vcs);

        // One result per input, in order, all proved.
        assert_eq!(results.len(), 5);
        for (i, (vc, r)) in results.iter().enumerate() {
            assert_eq!(vc.function.as_str(), vcs[i].function.as_str());
            assert!(r.is_proved());
        }
        // Only 3 unique obligations dispatched (A, B, C).
        assert_eq!(
            verify_calls.load(Ordering::SeqCst),
            3,
            "only the unique obligations should be solved"
        );
    }

    /// Plan P4: dispatch is serial and in input order — the only path. A
    /// backend sees the batch's distinct obligations exactly in the order they
    /// were given, on the calling thread.
    #[test]
    fn serial_canonical_dispatch_is_the_only_path() {
        struct OrderRecordingBackend {
            seen: Arc<std::sync::Mutex<Vec<(String, std::thread::ThreadId)>>>,
        }

        impl VerificationBackend for OrderRecordingBackend {
            fn name(&self) -> &str {
                "order-recording"
            }

            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }

            fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
                self.seen
                    .lock()
                    .unwrap()
                    .push((vc.function.as_str().to_string(), std::thread::current().id()));
                VerificationResult::Proved {
                    solver: "order-recording".into(),
                    time_ms: 0,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                }
            }
        }

        let seen = Arc::new(std::sync::Mutex::new(Vec::new()));
        let router = Router::with_backends(vec![Box::new(OrderRecordingBackend {
            seen: Arc::clone(&seen),
        })]);
        let names = ["v9", "v1", "v5", "v3", "v7", "v2", "v8", "v4", "v6", "v0"];
        let vcs: Vec<VerificationCondition> = names.into_iter().map(distinct_division_vc).collect();

        let results = router.verify_all(&vcs);

        assert_eq!(results.len(), names.len());
        let seen = seen.lock().unwrap();
        let order: Vec<&str> = seen.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(order, names, "the backend sees the batch in input order");
        let caller = std::thread::current().id();
        assert!(seen.iter().all(|(_, thread)| *thread == caller), "dispatch stays on the caller");
    }

    #[test]
    fn routing_preflight_backend_plan_queries_each_backend_once() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let first = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let second = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![first, second]);

        let plan = router.backend_plan(&division_vc("plan_once"));

        assert_eq!(plan.len(), 2);
        assert_eq!(
            can_handle_calls.load(Ordering::SeqCst),
            2,
            "backend_plan should cache one can_handle result per backend"
        );
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn routing_preflight_verify_one_queries_each_backend_once_before_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let first = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let second = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![first, second]);

        let result = router.verify_one(&division_vc("verify_once"));

        assert!(result.is_proved());
        assert_eq!(
            can_handle_calls.load(Ordering::SeqCst),
            2,
            "verify_one should reuse routing preflight instead of querying the winning backend twice"
        );
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn routing_preflight_verify_all_queries_each_backend_once_per_vc() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let first = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let second = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![first, second]);

        let vcs = vec![
            distinct_division_vc("a"),
            distinct_division_vc("b"),
            distinct_division_vc("a"),
        ];
        let results = router.verify_all(&vcs);
        assert_eq!(results.len(), 3);
        assert!(results.iter().all(|(_, r)| r.is_proved()));
        // 3 input VCs × 2 backends = 6 `can_handle` queries total (representatives
        // reuse their preflight plan instead of re-querying every backend).
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 6);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn unsupported_mir_temporal_dispatch_is_guarded() {
        let router = Router::new();
        let machine = trust_temporal::StateMachine::new(trust_temporal::StateId(0));
        let results = router.verify_temporal_vcs(&[(unsupported_mir_vc(), machine)]);

        assert_eq!(results.len(), 1);
        assert!(
            matches!(&results[0].1, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
        );
    }

    #[test]
    fn wave495_single_vc_fast_path_and_multi_vc_fanout_and_ground_check_parity() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);

        let single = [distinct_division_vc("only")];
        let out = router.verify_all(&single);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].0.function.as_str(), "only");
        assert!(out[0].1.is_proved());
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 1);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 1);

        #[cfg(feature = "ay-backend")]
        {
            use crate::in_process_ay_backend::formula_is_ground;
            assert!(formula_is_ground(&Formula::Eq(
                Box::new(Formula::Int(2)),
                Box::new(Formula::Int(2)),
            )));
            assert!(!formula_is_ground(&Formula::Var("free_x".into(), Sort::Int)));
            let closed_forall = Formula::Forall(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            );
            assert!(formula_is_ground(&closed_forall));
            let shadowed_plus_free = Formula::And(vec![
                closed_forall,
                Formula::Eq(
                    Box::new(Formula::Var("b".into(), Sort::BitVec(8))),
                    Box::new(Formula::BitVec { value: 1, width: 8 }),
                ),
            ]);
            assert!(!formula_is_ground(&shadowed_plus_free));
        }
    }
}

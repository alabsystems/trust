//! The Router struct: dispatches VCs to verification backends.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use trust_types::*;

use crate::memory_guard::MemoryGuard;
use crate::{
    BackendSelection, VerificationBackend, constant_folder, routing, termination_dispatch,
    ty_backend,
};

/// Routes VCs to appropriate backends.
///
/// Trust: Backends are stored as `Arc<dyn VerificationBackend>` internally
/// to support both sequential and parallel verification modes. The public
/// constructors accept `Box<dyn VerificationBackend>` for backward
/// compatibility and convert to Arc on construction.
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
    // Trust: Arc storage enables zero-copy sharing with parallel threads.
    backends: Vec<Arc<dyn VerificationBackend>>,
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
        // in-process ay-dpll SMT backend alongside the constant folder. It sits
        // beside the existing subprocess backends (IncrementalAYSession,
        // smtlib_backend) — it does not replace them at the registration site —
        // and is selected by the router for L0 safety obligations via its
        // `can_handle`/`role`.
        #[allow(unused_mut)]
        let mut backends: Vec<Arc<dyn VerificationBackend>> =
            vec![Arc::new(constant_folder::ConstantFolderBackend)];
        #[cfg(feature = "ay-backend")]
        backends.push(Arc::new(crate::in_process_ay_backend::InProcessAyBackend::new()));
        Router { backends, memory_guard: Arc::new(MemoryGuard::default()) }
    }

    /// Create a router with specific backends.
    ///
    /// Accepts `Box<dyn VerificationBackend>` for backward compatibility.
    /// Converts to Arc internally to support parallel verification.
    pub fn with_backends(backends: Vec<Box<dyn VerificationBackend>>) -> Self {
        Router {
            backends: backends.into_iter().map(Arc::from).collect(),
            memory_guard: Arc::new(MemoryGuard::default()),
        }
    }

    /// Trust (R-U Phase D, router convergence): the ONE name for the
    /// deterministic analysis-seam router — a single in-process ay backend
    /// with the given per-VC timeout, and nothing else. Compiler analysis
    /// seams (the R1 oracle, assert-refutation sweeps, Liskov checks)
    /// construct their router through this name instead of an inline
    /// `with_backends` so the seam set is enumerable and the determinism
    /// contract has one definition site: IN-PROCESS ay only — never the
    /// external-binary cached router, whose per-VC subprocess timeout makes
    /// verdicts nondeterministic across builds (Failed one build, Unknown
    /// the next).
    #[cfg(feature = "ay-backend")]
    pub fn deterministic_in_process_ay(timeout_ms: u64) -> Self {
        Router::with_backends(vec![Box::new(
            crate::in_process_ay_backend::InProcessAyBackend::new().with_timeout(timeout_ms),
        )])
    }

    /// Trust: Create a router with Arc-wrapped backends for parallel use.
    ///
    /// Use this when you already have Arc-wrapped backends (e.g., when
    /// sharing backends between a Router and standalone parallel functions).
    pub fn with_arc_backends(backends: Vec<Arc<dyn VerificationBackend>>) -> Self {
        Router { backends, memory_guard: Arc::new(MemoryGuard::default()) }
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
    /// Useful for passing backends to standalone parallel functions
    /// without re-wrapping.
    pub fn arc_backends(&self) -> Vec<Arc<dyn VerificationBackend>> {
        self.backends.clone()
    }

    /// Trust: Return the backend selection plan for a VC.
    ///
    /// The plan is ordered by router heuristics, not by insertion order:
    /// the preferred backend family for the VC's proof level is tried first,
    /// then fallback families, then general-purpose backends.
    pub fn backend_plan(&self, vc: &VerificationCondition) -> Vec<BackendSelection> {
        if matches!(&vc.kind, VcKind::UnsupportedMir { .. }) {
            return Vec::new();
        }

        routing::backend_plan(&self.backends, vc)
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
            if !deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                return Self::batch_via_backend_with_deadline(backend, vcs, deadline);
            }
        }

        // Trust (audit rec 4): structural dedup before sequential dispatch.
        //
        // Identical safety VCs (the same obligation up to renaming of bound
        // variables) are collapsed to ONE solve and the shared verdict is
        // fanned out to every duplicate. This mirrors the parallel cache path's
        // miss-coalescing (`solver_cache::pending_miss_by_key`), which the
        // sequential loop here previously lacked — it dispatched every duplicate
        // 1:1.
        //
        // Soundness: `vc_dedup::dedup_groups` merges two VCs only when they are
        // alpha-equivalent obligations AND carry the same routing requirements
        // (the plan signature below). The representative of each group is
        // verified exactly as it would be in the per-VC path; cloning its
        // verdict to the other group members is sound because they denote the
        // identical obligation. Every input VC still receives a result, in
        // original order (see the fan-out below). The deadline short-circuit is
        // preserved for every VC, including non-representatives.
        let groups = crate::vc_dedup::dedup_groups(vcs, |i| self.plan_signature(&vcs[i]));

        // Output slots, one per input VC, filled by original index.
        let mut slots: Vec<Option<VerificationResult>> = (0..vcs.len()).map(|_| None).collect();

        for group in &groups {
            let rep_vc = &vcs[group.representative];
            // Solve the representative once (honoring the deadline exactly as
            // the per-VC loop would).
            let rep_result = if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                budget_exceeded_unknown(rep_vc)
            } else {
                self.verify_one(rep_vc)
            };

            // Fan the verdict out to every member of the group. Members denote
            // the same obligation, so the verdict is identical. We still honor
            // the deadline per-member: if it lapsed mid-group, late members
            // degrade to a sound `Unknown` rather than receiving the
            // representative's verdict — matching the per-VC loop's behavior
            // where each VC re-checks the deadline before dispatch.
            for &member in &group.members {
                let member_result = if member == group.representative {
                    rep_result.clone()
                } else if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                    budget_exceeded_unknown(&vcs[member])
                } else {
                    rep_result.clone()
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
    /// unsupported-MIR guard runs per VC exactly as in the per-VC path, so
    /// unsupported-MIR VCs are never sent to the backend.
    fn batch_via_backend_with_deadline(
        backend: &Arc<dyn VerificationBackend>,
        vcs: &[VerificationCondition],
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        // Partition into VCs the backend should solve (after the unsupported-MIR
        // short-circuit) vs. those resolved here, preserving order.
        let mut to_batch: Vec<VerificationCondition> = Vec::with_capacity(vcs.len());
        let mut to_batch_indices: Vec<usize> = Vec::with_capacity(vcs.len());
        let mut results: Vec<Option<VerificationResult>> = (0..vcs.len()).map(|_| None).collect();

        for (i, vc) in vcs.iter().enumerate() {
            if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "router", 0) {
                results[i] = Some(result);
            } else if !backend.can_handle(vc) {
                // Match the per-VC fallback-chain outcome: no eligible backend.
                results[i] = Some(VerificationResult::Unknown {
                    solver: "none".into(),
                    time_ms: 0,
                    reason: "no backend can handle this VC".to_string(),
                });
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
    fn plan_signature(&self, vc: &VerificationCondition) -> Vec<(trust_types::Symbol, bool)> {
        self.backend_plan(vc).iter().map(|sel| (sel.name, sel.can_handle)).collect()
    }

    /// Verify a single VC by finding an appropriate backend.
    ///
    /// Checks process RSS against the configured memory limit
    /// before dispatching to a solver backend. Returns an Unknown result
    /// with the memory error reason if the limit is exceeded.
    pub fn verify_one(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "router", 0) {
            return result;
        }

        self.verify_one_with_components(vc)
    }

    /// Verify a VC using a routing plan that was already computed by this router.
    ///
    /// This keeps wrapper layers that need the plan for their own preflight
    /// work from paying a second `can_handle` pass on cache misses.
    pub(crate) fn verify_one_with_plan(
        &self,
        vc: &VerificationCondition,
        plan: &[BackendSelection],
    ) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "router", 0) {
            return result;
        }

        Self::verify_with_backend_fallback_from_plan(
            &self.backends,
            self.memory_guard.as_ref(),
            vc,
            plan,
            |backend| backend.verify(vc),
        )
    }

    /// Trust: Verify all VCs using bounded thread parallelism.
    ///
    /// For a single VC or `max_threads <= 1`, falls back to sequential
    /// `verify_all` to avoid thread overhead. Otherwise splits VCs into
    /// chunks and verifies each chunk on a separate thread.
    ///
    /// `max_threads` bounds concurrency (clamped to `1..=vcs.len()`).
    pub fn verify_all_parallel(
        &self,
        vcs: &[VerificationCondition],
        max_threads: usize,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.verify_all_parallel_with_deadline(vcs, max_threads, None)
    }

    /// Verify all VCs using bounded thread parallelism under an optional
    /// per-batch wall-clock deadline.
    ///
    /// The deadline is checked inside each worker immediately before a VC is
    /// dispatched. Obligations that have not started by the time the deadline
    /// passes degrade to `Unknown`; already-started solver calls rely on their
    /// per-VC timeout.
    pub fn verify_all_parallel_with_deadline(
        &self,
        vcs: &[VerificationCondition],
        max_threads: usize,
        deadline: Option<std::time::Instant>,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        // Trust: Sequential fallback for trivial cases.
        if vcs.is_empty() {
            return Vec::new();
        }
        if vcs.len() <= 1 || max_threads <= 1 {
            return self.verify_all_with_deadline(vcs, deadline);
        }

        // Inlined from deleted parallel.rs — simple chunked threading.
        //
        // Trust: ownership-only optimization — dispatch by shared `Arc<[VC]>`
        // + per-thread index ranges instead of cloning each VC into an owned
        // chunk (and again into a panic-fallback chunk, and again into each
        // result tuple). The VCs are materialized into the `Arc` exactly once;
        // workers borrow them by index and return `(index, result)` pairs, and
        // the final output tuples clone each VC once from the shared slice into
        // its original position. Verdicts and output order are unchanged: every
        // VC is still dispatched exactly once, results are placed back by their
        // original index, and the panic-fallback path re-runs the same VC range
        // by borrowing the shared slice (no lost fallback).
        let max_threads = max_threads.min(vcs.len()).max(1);
        let backends = Arc::new(self.backends.clone());
        let memory_guard = Arc::clone(&self.memory_guard);
        let shared_vcs: Arc<[VerificationCondition]> = Arc::from(vcs);
        let chunk_size = vcs.len().div_ceil(max_threads);

        let mut handles = Vec::with_capacity(max_threads);
        let mut start = 0usize;
        while start < shared_vcs.len() {
            let end = (start + chunk_size).min(shared_vcs.len());
            let backends = Arc::clone(&backends);
            let memory_guard = Arc::clone(&memory_guard);
            let shared_vcs = Arc::clone(&shared_vcs);
            let handle = std::thread::spawn(move || {
                let mut results = Vec::with_capacity(end - start);
                for index in start..end {
                    let vc = &shared_vcs[index];
                    let result = if deadline.is_some_and(|at| std::time::Instant::now() >= at) {
                        budget_exceeded_unknown(vc)
                    } else {
                        catch_unwind(AssertUnwindSafe(|| {
                            Self::verify_one_with_components_from(
                                backends.as_slice(),
                                memory_guard.as_ref(),
                                vc,
                            )
                        }))
                        .unwrap_or_else(|_| {
                            crate::backend_trait::panic_unknown(
                                "router-parallel",
                                0,
                                format!("parallel dispatch for {}", vc.function),
                            )
                        })
                    };
                    results.push((index, result));
                }
                results
            });
            handles.push((start, end, handle));
            start = end;
        }

        // Preallocate result slots by original position so output order is
        // independent of thread completion order.
        let mut slots: Vec<Option<VerificationResult>> =
            (0..shared_vcs.len()).map(|_| None).collect();
        for (start, end, handle) in handles {
            match handle.join() {
                Ok(chunk_results) => {
                    for (index, result) in chunk_results {
                        slots[index] = Some(result);
                    }
                }
                // Panic-fallback: the worker thread itself unwound. Re-fill the
                // same VC range (borrowed from the shared slice) with a sound
                // `Unknown`, matching the prior per-VC fallback behavior.
                Err(_) => {
                    for index in start..end {
                        slots[index] = Some(crate::backend_trait::panic_unknown(
                            "router-parallel",
                            0,
                            format!("parallel worker for {}", shared_vcs[index].function),
                        ));
                    }
                }
            }
        }

        shared_vcs
            .iter()
            .zip(slots)
            .map(|(vc, slot)| {
                let result = slot.unwrap_or_else(|| {
                    crate::backend_trait::panic_unknown(
                        "router-parallel",
                        0,
                        format!("missing parallel result for {}", vc.function),
                    )
                });
                (vc.clone(), result)
            })
            .collect()
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
                if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "router", 0)
                {
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

    /// Verify through shared components so sequential and
    /// parallel dispatch apply the same memory guard before solver calls.
    fn verify_one_with_components(&self, vc: &VerificationCondition) -> VerificationResult {
        Self::verify_one_with_components_from(&self.backends, self.memory_guard.as_ref(), vc)
    }

    fn verify_one_with_components_from(
        backends: &[Arc<dyn VerificationBackend>],
        memory_guard: &MemoryGuard,
        vc: &VerificationCondition,
    ) -> VerificationResult {
        if let Some(result) = crate::backend_trait::unsupported_mir_unknown(vc, "router", 0) {
            return result;
        }

        Self::verify_with_backend_fallback(backends, memory_guard, vc, |backend| backend.verify(vc))
    }

    fn verify_with_backend_fallback<F>(
        backends: &[Arc<dyn VerificationBackend>],
        memory_guard: &MemoryGuard,
        vc: &VerificationCondition,
        mut verify: F,
    ) -> VerificationResult
    where
        F: FnMut(&Arc<dyn VerificationBackend>) -> VerificationResult,
    {
        // Ordinary router dispatch keeps FallbackChain's retry/simplify policy
        // out of the path: only later capable backends are tried here.
        let eligible_backends = routing::eligible_backends(backends, vc);
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

        VerificationResult::Unknown {
            solver: "none".into(),
            time_ms: 0,
            reason: "no backend can handle this VC".to_string(),
        }
    }

    fn verify_with_backend_fallback_from_plan<F>(
        backends: &[Arc<dyn VerificationBackend>],
        memory_guard: &MemoryGuard,
        vc: &VerificationCondition,
        plan: &[BackendSelection],
        mut verify: F,
    ) -> VerificationResult
    where
        F: FnMut(&Arc<dyn VerificationBackend>) -> VerificationResult,
    {
        let property = termination_dispatch::classify_property(vc);
        let mut last_non_definitive = None;
        let mut dispatched_any = false;

        for selection in plan {
            if !selection.can_handle {
                continue;
            }
            let Some(backend) = backends.get(selection.index) else {
                continue;
            };
            let validity = termination_dispatch::validate_dispatch(property, backend.name());
            if validity.is_invalid() {
                continue;
            }

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

        VerificationResult::Unknown {
            solver: "none".into(),
            time_ms: 0,
            reason: "no backend can handle this VC".to_string(),
        }
    }

    fn check_memory_limit_for(memory_guard: &MemoryGuard) -> Option<VerificationResult> {
        match memory_guard.check_memory() {
            Ok(_snapshot) => None,
            Err(crate::memory_guard::MemoryGuardError::LimitExceeded {
                current_mb,
                limit_mb,
                peak_mb,
            }) => Some(VerificationResult::Unknown {
                solver: "memory-guard".into(),
                time_ms: 0,
                reason: format!(
                    "memory limit exceeded: {current_mb}MB used, {limit_mb}MB limit \
                     (peak: {peak_mb}MB) — skipping solver dispatch"
                ),
            }),
            Err(_query_err) => {
                // Query failure is non-fatal: proceed with dispatch.
                // The guard already logs warnings to stderr.
                None
            }
        }
    }
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
fn budget_exceeded_unknown(vc: &VerificationCondition) -> VerificationResult {
    VerificationResult::Unknown {
        solver: Symbol::intern("trust-budget"),
        time_ms: 0,
        reason: format!(
            "per-function wall-clock verification budget exceeded before dispatching obligation for `{}`",
            vc.function
        ),
    }
}

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
        let named = Router::deterministic_in_process_ay(1234);
        let inline = Router::with_backends(vec![Box::new(
            crate::in_process_ay_backend::InProcessAyBackend::new().with_timeout(1234),
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
    fn verify_all_parallel_with_past_deadline_degrades_to_unknown_without_dispatch() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let vcs = vec![division_vc("a"), division_vc("b"), division_vc("c"), division_vc("d")];

        let past = std::time::Instant::now() - std::time::Duration::from_secs(1);
        let results = router.verify_all_parallel_with_deadline(&vcs, 4, Some(past));

        assert_eq!(results.len(), 4);
        assert!(results.iter().all(|(_, r)| matches!(
            r,
            VerificationResult::Unknown { solver, reason, .. }
                if solver.as_str() == "trust-budget" && reason.contains("budget exceeded")
        )));
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
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
    fn unsupported_mir_verify_all_parallel_does_not_dispatch_backend() {
        let can_handle_calls = Arc::new(AtomicUsize::new(0));
        let verify_calls = Arc::new(AtomicUsize::new(0));
        let backend = Arc::new(CountingBackend {
            can_handle_calls: Arc::clone(&can_handle_calls),
            verify_calls: Arc::clone(&verify_calls),
        });
        let router = Router::with_arc_backends(vec![backend]);
        let vcs = vec![unsupported_mir_vc(), unsupported_mir_vc()];

        let results = router.verify_all_parallel(&vcs, 2);

        assert_eq!(results.len(), 2);
        assert!(
            results
                .iter()
                .all(|(_, result)| matches!(result, VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR")))
        );
        assert_eq!(can_handle_calls.load(Ordering::SeqCst), 0);
        assert_eq!(verify_calls.load(Ordering::SeqCst), 0);
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
}

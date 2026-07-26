//! The VerificationBackend trait definition.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::BackendRole;

/// Return the mandatory fail-closed result for an unsupported MIR VC.
///
/// `UnsupportedMir` is not a solver obligation: it records a valid MIR shape
/// whose semantics are not yet modeled precisely enough for proof. Any direct
/// backend/router entrypoint must return `Unknown` before formula dispatch.
pub fn unsupported_mir_unknown(
    vc: &VerificationCondition,
    solver: impl Into<Symbol>,
    time_ms: u64,
) -> Option<VerificationResult> {
    if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
        let classification = unsupported_mir_classification(kind, detail)
            .map(|classification| format!(" [{classification}]"))
            .unwrap_or_default();
        Some(VerificationResult::Unknown {
            solver: solver.into(),
            time_ms,
            reason: format!(
                "unsupported MIR {kind}{classification} preserved in TrustIr: {detail}"
            ),
        })
    } else {
        None
    }
}

fn unsupported_mir_classification(kind: &str, detail: &str) -> Option<&'static str> {
    if kind == "SourceBackpropagationGateBlocker" || kind == "source_backpropagation_gate" {
        return Some(source_backpropagation_gate_classification(detail));
    }
    if is_symbolic_formula_not_consumed_kind(kind) {
        return Some("trust_symbolic_formula_not_consumed");
    }
    if kind != "AArch64AtomicSemanticFactNotProofConsumed" {
        return Some("unsupported_mir");
    }

    let detail = detail.to_ascii_lowercase();
    if detail.contains("exclusive_monitor=loadreserve")
        || detail.contains("exclusive_monitor=storeconditional")
        || detail.contains("exclusive-monitor")
    {
        if detail.contains("store-conditional status result")
            || detail.contains("status semantics")
            || detail.contains("reports_status=true")
        {
            return Some("aarch64_exclusive_monitor_status_unsupported");
        }
        return Some("aarch64_exclusive_monitor_unsupported");
    }
    if detail.contains("ordering=acquire")
        || detail.contains("opcode=ldar")
        || detail.contains("acquire ordering")
    {
        return Some("aarch64_atomic_acquire_ordering_unsupported");
    }
    if detail.contains("ordering=release")
        || detail.contains("opcode=stlr")
        || detail.contains("release ordering")
    {
        return Some("aarch64_atomic_release_ordering_unsupported");
    }
    Some("aarch64_atomic_semantics_unsupported")
}

fn is_symbolic_formula_not_consumed_kind(kind: &str) -> bool {
    matches!(
        kind,
        "TrustSymbolicFormulaNotProofConsumed"
            | "SymbolicFormulaNotProofConsumed"
            | "trust_symbolic.formula"
    )
}

fn source_backpropagation_gate_classification(detail: &str) -> &'static str {
    let detail = detail.to_ascii_lowercase();
    let normalized = detail.replace(['_', '-'], " ");
    if detail.contains("missing_reconstruction")
        || normalized.contains("missing reconstruction")
        || normalized.contains("accepted reconstruction")
    {
        "source_backpropagation_missing_reconstruction"
    } else if detail.contains("type_ownership")
        || normalized.contains("type ownership")
        || normalized.contains("exact source type fact ownership")
        || normalized.contains("source type fact ownership")
        || normalized.contains("type fact owner")
        || normalized.contains("type fact ownership")
    {
        "source_backpropagation_type_ownership"
    } else if detail.contains("exact_source_provenance")
        || normalized.contains("exact source provenance")
    {
        "source_backpropagation_exact_source_provenance"
    } else if detail.contains("target_validation")
        || normalized.contains("target validation")
        || normalized.contains("target semantic")
        || normalized.contains("target proof consumer")
        || detail.contains("target/formula consumer")
        || detail.contains("target/formula consumers")
        || normalized.contains("target formula consumer")
        || normalized.contains("formula consumer")
        || detail.contains("trust_symbolic.formula")
        || detail.contains("binary-proof-obligation-pending-refinement-metadata")
        || normalized.contains("pending refinement metadata")
        || normalized.contains("bidirectional refinement")
    {
        "source_backpropagation_target_validation"
    } else if detail.contains("checked_certificate_identity")
        || normalized.contains("checked certificate identity")
        || normalized.contains("checked certificate readback")
        || normalized.contains("checked proof cert readback")
        || normalized.contains("proof cert readback")
        || normalized.contains("proof certificate readback")
        || normalized.contains("certificate identity")
        || normalized.contains("proof certificate identity")
    {
        "source_backpropagation_checked_certificate_identity"
    } else if detail.contains("replay_identity")
        || normalized.contains("replay identity")
        || normalized.contains("replay attestation")
        || normalized.contains("replay backend attested")
        || normalized.contains("replay attested")
        || normalized.contains("replay byte/range identity")
        || normalized.contains("replay byte range identity")
        || normalized.contains("byte range identity")
        || normalized.contains("step witness")
        || normalized.contains("machine effect witness")
        || normalized.contains("effect witness")
        || normalized.contains("concrete scalar memory address")
        || normalized.contains("replay source backprop")
    {
        "source_backpropagation_replay_identity"
    } else {
        "source_backpropagation_gate_unsupported"
    }
}

/// Return the mandatory fail-closed result when an isolated dispatch panics.
///
/// Parallel router workers and MIR portfolio lanes must not let one backend
/// panic erase sibling results or unwind the caller. Convert the panic into an
/// inconclusive verifier result so downstream aggregation still sees a result
/// for the affected obligation.
pub(crate) fn panic_unknown(
    solver: impl Into<Symbol>,
    time_ms: u64,
    context: impl std::fmt::Display,
) -> VerificationResult {
    VerificationResult::Unknown {
        solver: solver.into(),
        time_ms,
        reason: format!("{context} panicked; failing closed"),
    }
}

/// A verification backend that can check verification conditions.
///
/// Implement this trait to add a new solver backend to the router.
/// The router calls `can_handle` to check compatibility, then `verify`
/// to dispatch the VC.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VerificationResult, ProofStrength};
/// use trust_router::VerificationBackend;
///
/// struct MyBackend;
///
/// impl VerificationBackend for MyBackend {
///     fn name(&self) -> &str { "my-solver" }
///
///     fn can_handle(&self, vc: &VerificationCondition) -> bool {
///         // Accept only L0 safety VCs
///         vc.kind.proof_level() == trust_types::ProofLevel::L0Safety
///     }
///
///     fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
///         // Real implementation would call an SMT solver here
///         VerificationResult::Unknown {
///             solver: "my-solver".into(),
///             time_ms: 0,
///             reason: "not implemented".into(),
///         }
///     }
/// }
///
/// let backend = MyBackend;
/// assert_eq!(backend.name(), "my-solver");
/// ```
pub trait VerificationBackend: Send + Sync {
    fn name(&self) -> &str;

    /// Trust: Backend role used to rank solver families.
    ///
    /// Defaults to `General` so existing backends continue to compile even if
    /// they do not yet advertise a more specific capability.
    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool;
    fn verify(&self, vc: &VerificationCondition) -> VerificationResult;

    /// Trust: Whether `verify_batch` exploits a persistent solver context to
    /// share a per-function assertion prefix across a batch.
    ///
    /// `false` for every backend whose `verify_batch` is the default per-VC map
    /// (no throughput difference vs. `verify`). The router uses this to decide
    /// whether grouping VCs by function and dispatching them through
    /// `verify_batch` is worth it; the verdict is identical either way, so this
    /// is purely a throughput hint.
    fn supports_shared_prefix_batch(&self) -> bool {
        false
    }

    /// Trust: Batch verification entry point.
    ///
    /// Verifies a slice of VCs and returns one `(vc, result)` pair per input,
    /// IN INPUT ORDER. The element type and result type match `verify()`
    /// exactly — `verify_batch` is purely a throughput refinement of calling
    /// `verify()` once per VC.
    ///
    /// The default implementation maps `self.verify` over the VCs, so it is
    /// behaviorally identical to dispatching each VC individually. Backends
    /// that maintain a persistent solver context (e.g.
    /// `IncrementalAYSession`) override this to assert a per-function shared
    /// assertion prefix ONCE at the solver's base scope, then decide each
    /// obligation against the shared base — turning the `M*N` assert work of
    /// the per-VC path into `M+N`. Such an override MUST be verdict-identical
    /// to the default: for every VC the solver decides exactly the same
    /// logical formula (`shared_prefix ∧ obligation`), never adding or
    /// dropping a fact.
    fn verify_batch(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter().map(|vc| (vc.clone(), self.verify(vc))).collect()
    }
}

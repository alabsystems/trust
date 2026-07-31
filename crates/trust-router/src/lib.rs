//! trust-router: VC dispatch to verification backends
//!
//! Two dispatch decisions live here and they answer different questions.
//! `Router` ranks the registered `VerificationBackend`s for one
//! `VerificationCondition` (see `routing`) and walks that order until a
//! backend returns a definitive verdict. `full_verification` routes a typed
//! `TrustObligation` to the one primary engine that owns its kind and holds
//! the evidence bar that engine's proofs must clear; that is the decision the
//! compiler's obligation lane takes.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Keep the direct serde dependency explicit for serde_json-backed report/result
// APIs that cross the trust-router crate boundary.
use serde as _;

mod backend_trait;
pub mod report;
mod router;
pub(crate) mod routing;
mod types;
// Structural (alpha-equivalence) dedup of VCs before sequential dispatch.
pub(crate) mod vc_dedup;
// MIR-level router for function classification and dispatch.
pub(crate) mod mir_router;
// Obligation adapter that maps external tool
// results back to per-obligation identities (source span, VcKind, function name).
pub(crate) mod verification_obligation;
pub mod verifier_result;

// --- Public re-exports preserving the crate's external API ---
pub use backend_trait::{VerificationBackend, unsupported_mir_unknown};
// MIR-level router and obligation adapter.
pub use mir_router::build_v1_vcs;
pub use mir_router::{MirRouter, MirRouterConfig, MirStrategy};
pub use report::build_json_report_from_verifier_results;
pub use router::Router;
pub use types::{BackendRole, BackendSelection};
pub use verification_obligation::VerificationObligation;
pub use verifier_result::{
    ObligationDescriptor, StableObligationId, UnattributedVerifierArtifact, VerifierFunctionResult,
    VerifierObligationResult, VerifierResultSummary, descriptors_for_vcs,
    function_placeholder_obligation,
};

pub(crate) mod error;
pub use error::SolverProcessError;
pub use full_verification::{
    DEFAULT_PER_OBLIGATION_TIMEOUT_MS, DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt,
    FullVerificationEngine, FullVerificationPolicy, FullVerificationRunWithFreshReceipts,
    LiveVerificationReceiptBatch, NativeTrustMcTrustIrEngine, NativeTyEngine,
    required_native_engines, required_native_engines_with_timeout_ms,
};
// Incremental AY session re-exports.
pub use incremental_ay::{
    CommonAssertion, IncrementalAYSession, IncrementalAYStats, alloc_over_ceiling_forced,
    violation_is_forced, violation_is_modeling_gap_failclose,
};
// In-process ay-dpll SMT backend re-export.
#[cfg(feature = "ay-backend")]
pub use in_process_ay_backend::{InProcessAyBackend, formula_is_ground};
// trust_cg codegen backend re-exports.
#[cfg(feature = "trust-cg-backend")]
pub use trust_cg_backend::{
    CodegenVerdict, TrustCgBackend as TrustCgCodegenBackend, TrustCgBackendConfig,
    TrustCgBackendError,
};
// Memory guard re-exports for solver memory limit enforcement.
pub use memory_guard::{MemoryGuard, MemoryGuardError, MemorySnapshot};
pub use memory_jobserver::{
    MemoryJobserverError, MemoryReservation, acquire as acquire_memory_reservation,
};
// Trust: coordinator client — the SINGLE seam the in-process backend (now) and a
// future trustc edit (later) use to request admission from the selected
// coordinator domain. Participating workers are serialized against that
// domain's configured allowance; per-process guards remain the failure backstop.
pub use coordinator::{
    DaemonStatus, Reservation as MemoryCoordinatorReservation, ReservationError,
    reserve as reserve_memory, status as coordinator_status,
};
pub use trust_verifier_api::{VerificationRunResult, VerifierExecutionContext};

/// Fail-closed authority gate for inferred-precondition strengthening (#540).
/// Production attribution is disabled until exact VC digests and replayed
/// certificates arrive through a sealed carrier.
pub mod strengthen_gate;
/// R1 whole-program caller-propagation structural model. The coverage oracle
/// exists, but production verdict flipping is disabled because public assurance
/// labels are not proof authority.
pub mod strengthen_whole_program;
// There is no trust-vc / trust-mc / clean module here, and that is not an
// absence of those engines: they are reached as full-verification primary
// engines over typed obligations, not as per-VC `VerificationBackend`s.
pub mod full_verification;
pub mod constant_folder;
// Trust: cheap in-process interval/range backend — discharges bounded
// arithmetic-overflow VCs before ay (which times out / unknowns / false-fails
// on them in normal mode). Raises the normal-mode proof floor.
pub mod interval_backend;
#[path = "ownership_encoding.rs"]
pub(crate) mod ownership_encoding_impl;
pub(crate) mod ownership_encoding {
    pub(crate) use super::ownership_encoding_impl::is_ownership_vc;
}
// smt2_export provides SMT-LIB2 text serialization used by the in-process
// ay backend. Always compiled.
pub(crate) mod smt2_export;
// smtlib_backend carries the SMT-LIB2 script emitter and the solver-output
// parser the external-`ay` subprocess session drives; the in-process backend
// speaks to ay through its library API instead.
pub mod smtlib_backend;
// Incremental AY session with push/pop scoping for batch VC
// verification. Maintains a persistent solver context and shares common
// assertions across multiple VCs. Always compiled (not feature-gated by
// because it provides a higher-level API over the subprocess path.
pub mod incremental_ay;
// In-process ay-dpll SMT backend. Replaces the subprocess SMT path
// for L0 safety obligations by solving against the linked ay-dpll library and
// capturing ay's real UnsatProofArtifact. Gated behind the `ay-backend` feature
// because ay's transitive deps (stacker, cc) conflict with compiler-pinned
// versions in the main workspace.
#[cfg(feature = "ay-backend")]
pub mod in_process_ay_backend;
// Solver-internal tracing diagnostics policy for in-process solves (suppressed
// by default so ay's WARN spam never leaks onto trustc's stderr; TRUST_AY_LOG
// opts back in). Same gate as its sole consumer.
#[cfg(feature = "ay-backend")]
mod ay_log;
// N-version Alethe cross-check: independent Carcara re-check of ay UNSAT proofs,
// wired into the live in-process ay gate when both `ay-backend` and
// `carcara-crosscheck` are enabled (Carcara pulls in GMP via `rug`).
#[cfg(feature = "carcara-crosscheck")]
pub mod carcara_cross_check;
// Experimental native reconstruction of selected ay UNSAT proofs into Clean
// kernel terms.  This module is crate-private and NON-AUTHORITATIVE: the live
// result carrier cannot yet bind and replay its `CertifiedPayload` for the exact
// VC, so the public backend keeps SmtBacked assurance.  Gated behind
// `ay-certify` (links ay + clean-auto WITHOUT carcara-verify).
#[cfg(feature = "ay-certify")]
pub(crate) mod ay_certify;
// Termination dispatch — PDR/k-induction prove safety, not termination.
pub(crate) mod termination_dispatch;
pub mod trust_wp_backend;
pub mod ty_backend;
// Process memory monitoring for solver memory limit enforcement.
pub(crate) mod memory_guard;
// Cross-process memory-aware token bucket: one admission ledger for participating
// workers. It does not measure or impose a hard ceiling on machine-wide RSS.
pub mod memory_jobserver;
// Trust: client + shared server helpers for the `trustd` memory-coordination
// daemon — the in-memory admission-ledger version of `memory_jobserver`'s flock
// transport (2026-06-17 OOM response, daemon upgrade). The single seam joins
// targo's auto-start glue and the in-process backend call.
pub mod coordinator;
// trust_cg verified codegen backend (behind trust_cg-backend feature).
#[cfg(feature = "trust-cg-backend")]
pub mod trust_cg_backend;
// VC-level solver result caching wired into verification dispatch.
pub mod solver_cache;

#[cfg(test)]
mod router_tests;

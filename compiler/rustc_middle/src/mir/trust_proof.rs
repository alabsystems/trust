// Trust: Proof-carrying MIR type definitions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Per-function verification results accessible via compiler query.
// Design: designs/2026-03-27-proof-carrying-mir.md
//
// Hot/cold split:
//   TrustProofResults  — semantic facts, deterministic, StableHash, drives codegen
//   TrustProofTelemetry — solver timings, counterexamples, NOT hashable
//
// Key decisions:
//   - Query keyed by ty::InstanceKind (follows coverage_ids_info pattern)
//   - ObligationId is a newtype index with 128-bit Fingerprint for stable identity
//   - arena_cache: provider returns Option<T> (owned), query system arenas automatically
//   - Vec<T> → &'tcx [T] for arena safety (arenas don't call Drop)
//   - Only clean-Certified results permit codegen check elision

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_index::IndexVec;
use rustc_macros::{StableHash, TyDecodable, TyEncodable};
use rustc_span::Symbol;

// ---------------------------------------------------------------------------
// Trust: ObligationId — stable proof obligation identity
// ---------------------------------------------------------------------------

rustc_index::newtype_index! {
    /// Trust: Index into per-function obligation arrays.
    ///
    /// Each obligation gets a dense index for O(1) codegen lookup via IndexVec.
    /// The canonical identity is the VC fingerprint (see `TrustObligationFingerprint`),
    /// but ObligationId is the fast runtime key.
    #[stable_hash]
    #[encodable]
    #[orderable]
    #[debug_format = "ObligationId({})"]
    pub struct ObligationId {}
}

// ---------------------------------------------------------------------------
// Trust: Semantic proof results (HOT path — drives codegen)
// ---------------------------------------------------------------------------

/// Trust: Per-function verification results. Arena-allocated, returned by query.
///
/// This is the canonical proof data that flows through the compiler.
/// Codegen reads `dispositions` to skip runtime checks (only if `Certified`).
/// Reporting reads `summary` for JSON output.
///
/// Keyed by `ty::InstanceKind` in the query (follows `coverage_ids_info` pattern).
/// Provider returns `Option<TrustProofResults>` (owned); `arena_cache` handles allocation.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofResults {
    /// Trust: Dense per-obligation dispositions for O(1) codegen lookup.
    /// Indexed by `ObligationId`.
    pub dispositions: IndexVec<ObligationId, TrustDisposition>,

    // Trust: NOTE — Location→ObligationId mapping is NOT stored here.
    // Location doesn't derive TyEncodable/TyDecodable (and it's fragile — shifts
    // during inlining). The location_map is computed at query time from the MIR
    // body and cached separately. See designs/2026-03-27-proof-carrying-mir.md
    // §"CRITICAL: Replace Location with Stable ObligationId".
    /// Trust: 128-bit fingerprint per obligation for cross-compilation stability.
    /// Indexed by `ObligationId`. Computed structurally over the logical VC formula,
    /// NOT over MIR locations (which shift during optimization).
    pub fingerprints: IndexVec<ObligationId, Fingerprint>,

    /// Trust: Function-level summary statistics.
    pub summary: TrustFunctionSummary,
}

impl TrustProofResults {
    /// Trust: Lookup a per-obligation disposition by dense obligation index.
    #[must_use]
    pub fn disposition(&self, obligation: ObligationId) -> Option<TrustDisposition> {
        self.dispositions.get(obligation).copied()
    }

    /// Trust: Returns true when every obligation is statically discharged.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.has_aligned_obligation_arrays()
            && self.summary.is_fully_verified()
            && self.recompute_summary() == self.summary
    }

    /// Trust: Returns true when any obligation falls back to a runtime check.
    #[must_use]
    pub fn has_runtime_checks(&self) -> bool {
        self.summary.runtime_checked > 0
    }

    /// Trust: Returns true when the result array carries more than one outcome
    /// class. Useful for guarding adapters against collapsing mixed VC results
    /// into a single function-level verdict.
    #[must_use]
    pub fn has_mixed_statuses(&self) -> bool {
        let Some(first) = self.dispositions.iter().next() else {
            return false;
        };
        self.dispositions.iter().any(|disposition| disposition.status != first.status)
    }

    /// Trust: Recompute summary statistics from the per-obligation
    /// dispositions. This is intentionally derived from the dense result array
    /// so failed or unknown sub-obligations cannot be hidden by a whole-function
    /// summary.
    #[must_use]
    pub fn recompute_summary(&self) -> TrustFunctionSummary {
        TrustFunctionSummary::from_dispositions(&self.dispositions)
    }

    /// Trust: Check that dense dispositions and stable fingerprints remain
    /// aligned one-to-one.
    #[must_use]
    pub fn has_aligned_obligation_arrays(&self) -> bool {
        self.dispositions.len() == self.fingerprints.len()
    }
}

/// Trust: Per-obligation codegen disposition. The hot-path type.
///
/// 8 bytes or less. Copy. This is what codegen reads at every checked operation.
/// If `status == Certified`, codegen can elide the runtime check.
/// If `status == Trusted`, the check stays but we report it as proved.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustDisposition {
    /// Trust: What property was checked.
    pub kind: TrustObligationKind,

    /// Trust: Proof status (Trusted/Certified/Failed/Unknown/RuntimeChecked).
    pub status: TrustStatus,

    /// Trust: How strong the proof is.
    pub strength: TrustProofStrength,

    /// Trust: Only true if clean kernel independently verified the certificate.
    /// This is the gate for codegen check elision.
    pub certified: bool,
}

// ---------------------------------------------------------------------------
// Trust: Telemetry / diagnostics (COLD path — reporting only)
// ---------------------------------------------------------------------------

/// Trust: Per-function diagnostic telemetry. Non-deterministic, NOT hashable.
///
/// Solver timings fluctuate with system load. Counterexamples may differ between
/// solver versions. This data drives reporting but MUST NOT affect incremental
/// compilation hashes (hence no `StableHash` derive).
///
/// Returned by a separate `trust_proof_telemetry` query with `no_hash` modifier.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct TrustProofTelemetry {
    /// Trust: Per-obligation diagnostic details, indexed by ObligationId.
    pub details: IndexVec<ObligationId, TrustObligationDetail>,
}

impl TrustProofTelemetry {
    /// Trust: Lookup a diagnostic detail by dense obligation index.
    #[must_use]
    pub fn detail(&self, obligation: ObligationId) -> Option<&TrustObligationDetail> {
        self.details.get(obligation)
    }

    /// Trust: Iterate only over obligations that fell back to runtime checking.
    #[must_use]
    pub fn runtime_checked_details(
        &self,
    ) -> impl Iterator<Item = (ObligationId, &TrustObligationDetail)> {
        self.details.iter_enumerated().filter(|(_, detail)| detail.runtime_fallback.is_some())
    }

    /// Trust: Count obligations that were runtime-checked instead of statically proved.
    #[must_use]
    pub fn runtime_checked_count(&self) -> usize {
        self.runtime_checked_details().count()
    }
}

/// Trust: Diagnostic detail for a single obligation. Cold path.
///
/// Contains solver identity, timing, and counterexample data.
/// Not StableHash — timings are non-deterministic.
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct TrustObligationDetail {
    /// Trust: Which solver produced this result. Interned Symbol (4 bytes, Copy).
    pub solver: Symbol,

    /// Trust: Wall-clock time in microseconds (not milliseconds — sub-ms precision matters).
    /// ay frequently returns in 100-300us.
    pub time_us: u64,

    /// Trust: Counterexample as (variable_name, value) pairs.
    /// Variable names are interned Symbols. Values are i128 (sufficient for
    /// all integer types up to 128-bit; floats encoded as bits).
    ///
    /// Empty vec means no counterexample (proved or unknown).
    /// For arena-allocated query results, this becomes `&'tcx [(Symbol, i128)]`.
    pub counterexample: Vec<(Symbol, i128)>,

    /// Trust: Structured runtime fallback metadata, if the obligation was
    /// checked dynamically because the solver could not discharge it.
    pub runtime_fallback: Option<TrustRuntimeFallback>,
}

/// Trust: Runtime fallback metadata for a verification obligation.
#[derive(Clone, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
pub struct TrustRuntimeFallback {
    /// Trust: Why the compiler fell back to runtime checking.
    pub reason: TrustRuntimeFallbackReason,

    /// Trust: Human-readable note explaining the fallback decision.
    pub note: String,
}

/// Trust: Machine-readable reason for a runtime fallback.
#[derive(Copy, Clone, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
pub enum TrustRuntimeFallbackReason {
    /// Trust: The solver returned `Unknown` and the compiler retained a check.
    Unknown,

    /// Trust: The solver timed out and the compiler retained a check.
    Timeout,
}

impl TrustObligationDetail {
    /// Trust: Returns true when this obligation was runtime-checked.
    #[must_use]
    pub fn is_runtime_checked(&self) -> bool {
        self.runtime_fallback.is_some()
    }

    /// Trust: Runtime fallback metadata, if the obligation was not statically proved.
    #[must_use]
    pub fn runtime_fallback(&self) -> Option<&TrustRuntimeFallback> {
        self.runtime_fallback.as_ref()
    }
}

// ---------------------------------------------------------------------------
// Trust: Proof status and strength enums
// ---------------------------------------------------------------------------

/// Trust: What the verification system concluded about an obligation.
///
/// Two-level trust model:
/// - `Trusted`: Solver says proved. Safe for diagnostics and reporting.
/// - `Certified`: clean kernel verified the proof certificate. Safe for codegen check elision.
///
/// Only `Certified` permits codegen to elide overflow/bounds checks. This keeps the
/// compiler TCB minimal: rustc + clean kernel.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustStatus {
    /// Trust: Solver says proved. Trusted but not independently verified.
    /// Safe for diagnostics, reporting, and advisory optimization hints.
    Trusted,

    /// Trust: Proof certificate verified by clean kernel.
    /// Safe for UB-relevant check elision in codegen.
    Certified,

    /// Trust: Counterexample found. Property violated.
    Failed,

    /// Trust: Solver could not determine (incomplete or resource-limited).
    Unknown,

    /// Trust: Solver timed out.
    Timeout,

    /// Trust: Runtime check inserted (unproved, but monitored).
    RuntimeChecked,
}

/// Trust: How strong the proof is.
///
/// Ordered roughly by increasing strength. Determines which proofs can
/// contribute to clean certification.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofStrength {
    /// Trust: No proof attempted or possible.
    None,

    /// Trust: Bounded model checking to depth k (trust-mc).
    /// Sound up to k steps; does not guarantee absence of deeper bugs.
    Bounded {
        /// Maximum unwinding/exploration depth.
        depth: u32,
    },

    /// Trust: SMT solver returned UNSAT (ay).
    /// Sound for the encoded formula; soundness depends on encoding correctness.
    SmtUnsat,

    /// Trust: Inductive invariant found (trust-wp).
    Inductive,

    /// Trust: Deductive verification with pre/post (trust-wp).
    Deductive,

    /// Trust: Ownership/lifetime proof (trust-vc).
    Ownership,

    /// Trust: Temporal property verified (ty).
    Temporal,

    /// Trust: Neural network robustness bound (`ny`). Reserved: no verifier
    /// produces this strength today, and it is deliberately not an alias for
    /// any other — an epsilon-ball bound is a different guarantee from an SMT
    /// refutation, so folding it into `SmtUnsat` would overstate what `ny`
    /// establishes. Epsilon is fixed point; multiply by 1e-9 for the value.
    NeuralBound {
        /// Fixed-point epsilon (1e-9 scale).
        epsilon: u64,
    },

    /// Trust: Constructive proof term exists, checkable by clean.
    /// This is the only strength that can produce `Certified` status.
    Constructive,
}

// ---------------------------------------------------------------------------
// Trust: Obligation kinds (what property was verified)
// ---------------------------------------------------------------------------

/// Trust: What kind of property was verified at this obligation.
///
/// Mirrors the VC kinds from trust_vcgen but uses compiler-internal types
/// (Symbol, no serde, no heap strings).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustObligationKind {
    /// Trust: Arithmetic overflow on a binary operation.
    ArithmeticOverflow(TrustBinOp),
    /// Trust: Division by zero.
    DivisionByZero,
    /// Trust: Remainder by zero.
    RemainderByZero,
    /// Trust: Array/slice index out of bounds.
    IndexOutOfBounds,
    /// Trust: Signed negation overflow (e.g., -i32::MIN).
    NegationOverflow,
    /// Trust: Shift amount exceeds bit width.
    ShiftOverflow,
    /// Trust: Cast truncation.
    CastOverflow,
    /// Trust: User assertion (`assert!`, `debug_assert!`).
    Assertion,
    /// Trust: Function precondition (`#[requires(...)]`).
    Precondition,
    /// Trust: Function postcondition (`#[ensures(...)]`).
    Postcondition,
    /// Trust: Unreachable code reached.
    Unreachable,
    /// Trust: Valid MIR preserved conservatively because Trust lacks precise semantics.
    UnsupportedMir,
    /// Trust: Deadlock freedom (concurrent code).
    Deadlock,
    /// Trust: Temporal property (distributed protocols).
    Temporal,
    /// Trust: Liveness property (something good eventually happens).
    Liveness,
    /// Trust: Taint tracking violation (untrusted data flows to sensitive sink).
    TaintViolation,
    /// Trust: Refinement violation (implementation doesn't refine spec).
    RefinementViolation,
    /// Trust: Resilience violation (missing error handling path).
    ResilienceViolation,
    /// Trust: Protocol violation (message sequence violates protocol spec).
    ProtocolViolation,
    /// Trust: Non-termination (loop may not terminate).
    NonTermination,
    /// Trust: Hardened profile boundary hazard.
    HardenedBoundary(TrustHardenedVcCategory),
}

/// Trust: Stable hardened profile boundary categories.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustHardenedVcCategory {
    RawPathApi,
    PathIdentity,
    PermissionChange,
    PermissionCreate,
    PermissionWindow,
    Utf8Reject,
    ByteLoss,
    ErrorDiscard,
    PanicBoundary,
    CompatObservable,
    ProcessSemantics,
    TrustDomain,
    TrustDomainOrder,
    UnsafeOperation,
    FfiBoundary,
    Unknown(Symbol),
}

/// Trust: Binary operations for overflow checking.
///
/// Copy, 1 byte — no heap allocation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
}

// ---------------------------------------------------------------------------
// Trust: Function-level summary
// ---------------------------------------------------------------------------

/// Trust: Function-level proof summary. Computed once, cached in results.
///
/// These counts are deterministic (derived from dispositions, not timings).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustFunctionSummary {
    /// Trust: Total number of proof obligations.
    pub total: u32,
    /// Trust: Number with `Trusted` status (solver-proved, not clean-certified).
    pub trusted: u32,
    /// Trust: Number with `Certified` status (clean-verified).
    pub certified: u32,
    /// Trust: Number replayed from the persistent proof cache — previously
    /// proved by this same trustc on byte-identical inputs (sound key HIT) and
    /// unchanged since, so re-verification was skipped this run. NOT a fresh
    /// `certified` (no re-checked evidence this run) and NOT `unknown` (it is a
    /// known prior PROVED); a distinct, honest "verified earlier, unchanged" class.
    pub cached: u32,
    /// Trust: Number with counterexamples.
    pub failed: u32,
    /// Trust: Number unknown or timed out.
    pub unknown: u32,
    /// Trust: Number with runtime checks inserted.
    pub runtime_checked: u32,
    /// Trust: Highest proof level achieved for this function.
    pub max_level: TrustProofLevel,
}

impl TrustFunctionSummary {
    /// Trust: Derive function-level counts from per-obligation dispositions.
    ///
    /// Adapters should prefer this over hand-built function verdicts whenever
    /// per-obligation data is available.
    #[must_use]
    pub fn from_dispositions(
        dispositions: &IndexVec<ObligationId, TrustDisposition>,
    ) -> TrustFunctionSummary {
        let mut summary = TrustFunctionSummary {
            total: dispositions.len() as u32,
            trusted: 0,
            certified: 0,
            cached: 0,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            max_level: TrustProofLevel::None,
        };

        for disposition in dispositions.iter() {
            match disposition.status {
                TrustStatus::Trusted => summary.trusted += 1,
                TrustStatus::Certified => summary.certified += 1,
                TrustStatus::Failed => summary.failed += 1,
                TrustStatus::Unknown | TrustStatus::Timeout => summary.unknown += 1,
                TrustStatus::RuntimeChecked => summary.runtime_checked += 1,
            }
            summary.max_level = summary.max_level.max(disposition.kind.proof_level());
        }

        summary
    }

    /// Trust: Returns true when the function has any unresolved obligations.
    #[must_use]
    pub fn has_unresolved(&self) -> bool {
        self.failed > 0 || self.unknown > 0 || self.runtime_checked > 0
    }

    /// Trust: the number of obligations accounted for across ALL disposition
    /// classes — the partition of `total`:
    /// `trusted + certified + cached + failed + unknown + runtime_checked`.
    /// Centralizes the breakdown invariant so consumers cannot drift (e.g.
    /// silently omit `cached` or `runtime_checked`) and so `total - accounted()`
    /// is exactly the genuinely-unattributed remainder. Saturating to avoid
    /// overflow on adversarial counts.
    #[must_use]
    pub fn accounted(&self) -> u32 {
        self.trusted
            .saturating_add(self.certified)
            .saturating_add(self.cached)
            .saturating_add(self.failed)
            .saturating_add(self.unknown)
            .saturating_add(self.runtime_checked)
    }

    /// Trust: Returns true when every obligation was discharged statically.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.total > 0
            && !self.has_unresolved()
            && self.trusted.saturating_add(self.certified) == self.total
    }
}

impl TrustObligationKind {
    /// Trust: Proof level associated with this obligation kind.
    #[must_use]
    pub fn proof_level(self) -> TrustProofLevel {
        match self {
            TrustObligationKind::ArithmeticOverflow(_)
            | TrustObligationKind::DivisionByZero
            | TrustObligationKind::RemainderByZero
            | TrustObligationKind::IndexOutOfBounds
            | TrustObligationKind::NegationOverflow
            | TrustObligationKind::ShiftOverflow
            | TrustObligationKind::CastOverflow
            | TrustObligationKind::Assertion
            | TrustObligationKind::Unreachable
            | TrustObligationKind::UnsupportedMir
            | TrustObligationKind::HardenedBoundary(
                TrustHardenedVcCategory::UnsafeOperation | TrustHardenedVcCategory::FfiBoundary,
            ) => TrustProofLevel::L0Safety,
            TrustObligationKind::Precondition
            | TrustObligationKind::Postcondition
            | TrustObligationKind::NonTermination
            | TrustObligationKind::TaintViolation
            | TrustObligationKind::ResilienceViolation
            | TrustObligationKind::HardenedBoundary(_) => TrustProofLevel::L1Functional,
            TrustObligationKind::Deadlock
            | TrustObligationKind::Temporal
            | TrustObligationKind::Liveness
            | TrustObligationKind::RefinementViolation
            | TrustObligationKind::ProtocolViolation => TrustProofLevel::L2Domain,
        }
    }
}

/// Trust: Verification level achieved for a function.
///
/// Ordered: None < L0Safety < L1Functional < L2Domain.
/// This ordering is meaningful — Ord derive produces the correct comparison.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofLevel {
    /// Trust: No verification performed.
    None,
    /// Trust: L0: Safety (overflow, bounds, div-by-zero).
    L0Safety,
    /// Trust: L1: Functional correctness (pre/postconditions).
    L1Functional,
    /// Trust: L2: Domain properties (temporal, distributed).
    L2Domain,
}

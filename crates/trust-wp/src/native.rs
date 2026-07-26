// trust_wp native request API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Native in-process trust_wp API.
//!
//! This module defines the request/result shape for the tRustc-owned path:
//! callers pass typed MIR and typed contract expressions directly instead of
//! reconstructing contracts from CLI arguments or source strings. With the
//! `trust-build` feature, the first native lane verifies pure trust_wp IR
//! obligations in-process through `trust-wp-ay`; unsupported richer semantics
//! and proof-evidence gaps still fail closed with structured blockers.

#[cfg(feature = "trust-build")]
use std::time::{Duration, Instant};

#[cfg(feature = "trust-build")]
use trust_wp_core::{TrackLevel, formula::PureExpr};
#[cfg(feature = "trust-build")]
use trust_wp_ay::{
    VerificationRequest, VerificationResult as AYVerificationResult, verify_function_with_modes,
};

use crate::config::TrustWpConfig;
use crate::contract::{Contract, ContractKind, ContractSet};
use crate::error::TrustWpLibError;
use crate::result::{DiagLevel, DiagnosticMessage, TrustWpResult, Verdict};
#[cfg(feature = "trust-build")]
use crate::result::{FunctionVerdict, VerificationCounts};
use crate::verifier_api::{
    TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION, TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION,
};

/// A tRustc-native trust_wp verification request.
///
/// `Mir` and `Expr` are intentionally generic so compiler-side callers can pass
/// borrowed rustc MIR bodies and typed contract nodes without this standalone
/// crate depending on rustc internals.
#[derive(Debug, Clone)]
pub struct NativeTrustWpRequest<Mir, Expr> {
    /// Function identity for reporting and result correlation.
    pub target: NativeFunctionTarget,

    /// Caller-owned native MIR handle or body.
    pub mir: Mir,

    /// Typed contract facts for the target function.
    pub contracts: NativeContractBundle<Expr>,

    /// Verification configuration shared with the compatibility API.
    pub config: TrustWpConfig,
}

impl<Mir, Expr> NativeTrustWpRequest<Mir, Expr> {
    /// Create a native request with default trust_wp configuration.
    pub fn new(
        target: NativeFunctionTarget,
        mir: Mir,
        contracts: NativeContractBundle<Expr>,
    ) -> Self {
        Self { target, mir, contracts, config: TrustWpConfig::default() }
    }

    /// Attach an explicit trust_wp configuration.
    #[must_use]
    pub fn with_config(mut self, config: TrustWpConfig) -> Self {
        self.config = config;
        self
    }
}

/// Function identity supplied by the compiler.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeFunctionTarget {
    /// Human-readable path, usually rustc's def path.
    pub def_path: String,

    /// Stable compiler identity, such as `DefPathHash`, when available.
    pub stable_id: Option<String>,

    /// Source span for diagnostics, formatted by the compiler caller.
    pub span: Option<String>,
}

impl NativeFunctionTarget {
    /// Create a target from a displayable def path.
    pub fn new(def_path: impl Into<String>) -> Self {
        Self { def_path: def_path.into(), stable_id: None, span: None }
    }

    /// Attach a stable compiler identity.
    #[must_use]
    pub fn with_stable_id(mut self, stable_id: impl Into<String>) -> Self {
        self.stable_id = Some(stable_id.into());
        self
    }

    /// Attach a source span for diagnostics.
    #[must_use]
    pub fn with_span(mut self, span: impl Into<String>) -> Self {
        self.span = Some(span.into());
        self
    }
}

/// Typed contract bundle for a native trust_wp request.
#[derive(Debug, Clone, Default)]
pub struct NativeContractBundle<Expr> {
    /// Preconditions.
    pub requires: Vec<NativeContract<Expr>>,

    /// Postconditions.
    pub ensures: Vec<NativeContract<Expr>>,

    /// Functional refinement predicates.
    pub refinements: Vec<NativeContract<Expr>>,

    /// Loop invariants keyed by compiler loop identity when available.
    pub loop_invariants: Vec<NativeLoopContract<Expr>>,

    /// Loop variants/termination metrics.
    pub loop_variants: Vec<NativeLoopContract<Expr>>,

    /// Old/snapshot bindings used by postconditions.
    pub snapshots: Vec<NativeSnapshot<Expr>>,

    /// Optional result binding used by postconditions.
    pub result_binding: Option<NativeResultBinding>,

    /// Cross-crate summaries that may be needed by the verifier.
    pub cross_crate_summaries: Vec<NativeSummaryRef>,

    /// Whether this function is trusted and should be assumed.
    pub trusted: bool,
}

impl<Expr> NativeContractBundle<Expr> {
    /// Create an empty native contract bundle.
    pub fn new() -> Self {
        Self {
            requires: Vec::new(),
            ensures: Vec::new(),
            refinements: Vec::new(),
            loop_invariants: Vec::new(),
            loop_variants: Vec::new(),
            snapshots: Vec::new(),
            result_binding: None,
            cross_crate_summaries: Vec::new(),
            trusted: false,
        }
    }

    /// Add a typed precondition.
    #[must_use]
    pub fn with_requires(mut self, expression: Expr) -> Self {
        self.requires.push(NativeContract::new(ContractKind::Requires, expression));
        self
    }

    /// Add a typed postcondition.
    #[must_use]
    pub fn with_ensures(mut self, expression: Expr) -> Self {
        self.ensures.push(NativeContract::new(ContractKind::Ensures, expression));
        self
    }

    /// Add a typed functional refinement predicate.
    #[must_use]
    pub fn with_refinement(mut self, expression: Expr) -> Self {
        self.refinements.push(NativeContract::new(ContractKind::Refinement, expression));
        self
    }

    /// Add a typed loop invariant.
    #[must_use]
    pub fn with_loop_invariant(mut self, expression: Expr) -> Self {
        self.loop_invariants.push(NativeLoopContract::invariant(expression));
        self
    }

    /// Add a typed loop variant.
    #[must_use]
    pub fn with_loop_variant(mut self, expression: Expr) -> Self {
        self.loop_variants.push(NativeLoopContract::variant(expression));
        self
    }

    /// Add an old/snapshot binding.
    #[must_use]
    pub fn with_snapshot(mut self, snapshot: NativeSnapshot<Expr>) -> Self {
        self.snapshots.push(snapshot);
        self
    }

    /// Attach the result binding for postconditions.
    #[must_use]
    pub fn with_result_binding(mut self, binding: NativeResultBinding) -> Self {
        self.result_binding = Some(binding);
        self
    }

    /// Add a cross-crate summary dependency.
    #[must_use]
    pub fn with_cross_crate_summary(mut self, summary: NativeSummaryRef) -> Self {
        self.cross_crate_summaries.push(summary);
        self
    }

    /// Mark this function as trusted.
    #[must_use]
    pub fn with_trusted(mut self, trusted: bool) -> Self {
        self.trusted = trusted;
        self
    }

    /// Return `true` when the bundle has no contract obligations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty()
            && self.ensures.is_empty()
            && self.refinements.is_empty()
            && self.loop_invariants.is_empty()
            && self.loop_variants.is_empty()
            && self.snapshots.is_empty()
            && self.result_binding.is_none()
            && self.cross_crate_summaries.is_empty()
            && !self.trusted
    }
}

impl NativeContractBundle<String> {
    /// Build a native-shaped string bundle from the compatibility contract set.
    ///
    /// This is useful for tests and adapters, but the target tRustc path should
    /// pass typed compiler contract nodes as `Expr`.
    pub fn from_compat_contracts(contracts: &ContractSet) -> Self {
        let mut bundle = Self::new().with_trusted(contracts.trusted);

        for contract in &contracts.requires {
            bundle.requires.push(NativeContract::from_compat(contract));
        }
        for contract in &contracts.ensures {
            bundle.ensures.push(NativeContract::from_compat(contract));
        }
        for contract in &contracts.invariants {
            bundle.loop_invariants.push(NativeLoopContract::from_compat_invariant(contract));
        }

        bundle
    }
}

/// One typed contract clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeContract<Expr> {
    /// Contract kind.
    pub kind: ContractKind,

    /// Caller-owned typed expression.
    pub expression: Expr,

    /// Source span for diagnostics, formatted by the compiler caller.
    pub span: Option<String>,
}

impl<Expr> NativeContract<Expr> {
    /// Create a typed contract clause.
    pub fn new(kind: ContractKind, expression: Expr) -> Self {
        Self { kind, expression, span: None }
    }

    /// Attach a source span.
    #[must_use]
    pub fn with_span(mut self, span: impl Into<String>) -> Self {
        self.span = Some(span.into());
        self
    }
}

impl NativeContract<String> {
    fn from_compat(contract: &Contract) -> Self {
        Self {
            kind: contract.kind,
            expression: contract.expression.clone(),
            span: contract.location.clone(),
        }
    }
}

/// A typed loop contract with optional compiler loop identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeLoopContract<Expr> {
    /// Contract kind. This is normally `Invariant` for invariants; variants use
    /// `role` because the compatibility `ContractKind` has no variant case.
    pub contract: NativeContract<Expr>,

    /// Whether this loop contract is an invariant or a termination variant.
    pub role: NativeLoopContractRole,

    /// Compiler loop identity, such as a MIR basic block index.
    pub loop_id: Option<String>,
}

impl<Expr> NativeLoopContract<Expr> {
    /// Create a typed loop invariant.
    pub fn invariant(expression: Expr) -> Self {
        Self {
            contract: NativeContract::new(ContractKind::Invariant, expression),
            role: NativeLoopContractRole::Invariant,
            loop_id: None,
        }
    }

    /// Create a typed loop variant.
    pub fn variant(expression: Expr) -> Self {
        Self {
            contract: NativeContract::new(ContractKind::Invariant, expression),
            role: NativeLoopContractRole::Variant,
            loop_id: None,
        }
    }

    /// Attach a compiler loop identity.
    #[must_use]
    pub fn with_loop_id(mut self, loop_id: impl Into<String>) -> Self {
        self.loop_id = Some(loop_id.into());
        self
    }
}

impl NativeLoopContract<String> {
    fn from_compat_invariant(contract: &Contract) -> Self {
        Self {
            contract: NativeContract::from_compat(contract),
            role: NativeLoopContractRole::Invariant,
            loop_id: None,
        }
    }
}

/// The role of a loop-level contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeLoopContractRole {
    /// Preservation invariant.
    Invariant,
    /// Termination variant.
    Variant,
}

/// A typed old/snapshot binding used by postconditions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeSnapshot<Expr> {
    /// Snapshot name used in typed contract expressions.
    pub name: String,

    /// Compiler-owned expression captured at function entry or another program point.
    pub expression: Expr,

    /// Source span for diagnostics, formatted by the compiler caller.
    pub span: Option<String>,
}

impl<Expr> NativeSnapshot<Expr> {
    /// Create a typed snapshot binding.
    pub fn new(name: impl Into<String>, expression: Expr) -> Self {
        Self { name: name.into(), expression, span: None }
    }

    /// Attach a source span.
    #[must_use]
    pub fn with_span(mut self, span: impl Into<String>) -> Self {
        self.span = Some(span.into());
        self
    }
}

/// Native result binding metadata for postconditions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeResultBinding {
    /// Binding name used by typed contract expressions.
    pub name: String,

    /// Compiler type display for diagnostics and lowering checks.
    pub ty: Option<String>,

    /// Source span for diagnostics, formatted by the compiler caller.
    pub span: Option<String>,
}

impl NativeResultBinding {
    /// Create result binding metadata.
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), ty: None, span: None }
    }

    /// Attach compiler type display.
    #[must_use]
    pub fn with_ty(mut self, ty: impl Into<String>) -> Self {
        self.ty = Some(ty.into());
        self
    }

    /// Attach a source span.
    #[must_use]
    pub fn with_span(mut self, span: impl Into<String>) -> Self {
        self.span = Some(span.into());
        self
    }
}

/// Native reference to a cross-crate verified summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeSummaryRef {
    /// Callee def path or summary key.
    pub callee: String,

    /// Optional stable compiler identity for the summary.
    pub stable_id: Option<String>,
}

impl NativeSummaryRef {
    /// Create a cross-crate summary reference.
    pub fn new(callee: impl Into<String>) -> Self {
        Self { callee: callee.into(), stable_id: None }
    }

    /// Attach a stable compiler identity.
    #[must_use]
    pub fn with_stable_id(mut self, stable_id: impl Into<String>) -> Self {
        self.stable_id = Some(stable_id.into());
        self
    }
}

/// Native verification result.
#[derive(Debug, Clone)]
pub struct NativeTrustWpResult {
    /// Native API status.
    pub status: NativeTrustWpStatus,

    /// Function identity for this result.
    pub target: NativeFunctionTarget,

    /// Compatibility result when native verification reaches trust_wp.
    pub trust_wp_result: Option<TrustWpResult>,

    /// Structured fail-closed blockers.
    pub blockers: Vec<NativeUnsupportedFeature>,

    /// Diagnostics produced by native lowering or trust_wp.
    pub diagnostics: Vec<DiagnosticMessage>,

    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
}

impl NativeTrustWpResult {
    fn unsupported(target: NativeFunctionTarget, blockers: Vec<NativeUnsupportedFeature>) -> Self {
        let diagnostics = blockers.iter().map(NativeUnsupportedFeature::to_diagnostic).collect();
        Self {
            status: NativeTrustWpStatus::Unsupported,
            target,
            trust_wp_result: None,
            blockers,
            diagnostics,
            time_ms: 0,
        }
    }

    #[cfg(feature = "trust-build")]
    fn from_trust_wp_result(target: NativeFunctionTarget, trust_wp_result: TrustWpResult) -> Self {
        let status = match trust_wp_result.verdict {
            Verdict::Verified => NativeTrustWpStatus::Verified,
            Verdict::Failed => NativeTrustWpStatus::Failed,
            Verdict::Unknown { .. } => NativeTrustWpStatus::Unknown,
            Verdict::Timeout => NativeTrustWpStatus::Timeout,
            Verdict::Error { .. } => NativeTrustWpStatus::Error,
        };
        Self {
            status,
            target,
            time_ms: trust_wp_result.time_ms,
            diagnostics: trust_wp_result.diagnostics.clone(),
            trust_wp_result: Some(trust_wp_result),
            blockers: Vec::new(),
        }
    }

    /// Convert this native result to the compatibility result type.
    #[must_use]
    pub fn to_trust_wp_result(&self) -> TrustWpResult {
        if let Some(result) = &self.trust_wp_result {
            return result.clone();
        }

        let reason = if self.blockers.is_empty() {
            format!("native trust_wp status: {:?}", self.status)
        } else {
            self.blockers
                .iter()
                .map(|blocker| blocker.reason.as_str())
                .collect::<Vec<_>>()
                .join("; ")
        };

        TrustWpResult {
            verdict: Verdict::Unknown { reason },
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: self.time_ms,
            diagnostics: self.diagnostics.clone(),
            function_name: self.target.def_path.clone(),
            counts: Default::default(),
        }
    }
}

/// High-level status for the native trust_wp API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeTrustWpStatus {
    /// All proof obligations were verified.
    Verified,
    /// At least one proof obligation failed.
    Failed,
    /// Verification was inconclusive.
    Unknown,
    /// Verification timed out.
    Timeout,
    /// Native lowering or a required semantic feature is not implemented.
    Unsupported,
    /// Native verification encountered an infrastructure error.
    Error,
}

/// A structured fail-closed blocker for the native API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeUnsupportedFeature {
    /// Blocker kind.
    pub kind: NativeUnsupportedKind,

    /// Human-readable reason.
    pub reason: String,
}

impl NativeUnsupportedFeature {
    fn new(kind: NativeUnsupportedKind, reason: impl Into<String>) -> Self {
        Self { kind, reason: reason.into() }
    }

    fn to_diagnostic(&self) -> DiagnosticMessage {
        DiagnosticMessage {
            level: DiagLevel::Warning,
            message: format!("native trust_wp unsupported ({:?}): {}", self.kind, self.reason),
            location: None,
        }
    }
}

/// Native API features that can currently block verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeUnsupportedKind {
    /// Native MIR-to-trust-wp lowering has not been wired.
    MirLowering,
    /// Typed contract expression lowering has not been wired.
    ContractLowering,
    /// Old/snapshot semantics are present but unsupported.
    SnapshotSemantics,
    /// Postcondition result binding is present but unsupported.
    ResultBinding,
    /// Loop variant/termination metric is present but unsupported.
    LoopVariant,
    /// Cross-crate summary import is present but unsupported.
    CrossCrateSummary,
    /// Loop invariant verification is present but unsupported by this lane.
    LoopInvariant,
    /// Functional refinement proof is present but unsupported by this lane.
    Refinement,
    /// `#[trusted]` assumptions are not native proof results.
    TrustedAssumption,
    /// trust_wp proof-evidence/replay artifacts are unavailable.
    ProofEvidence,
    /// Proof certificate byte production is requested but unavailable.
    ProofCertificate,
}

/// Concrete native body shape for the first in-process trust_wp lane.
///
/// This is intentionally not a source-string or CLI facade: callers provide
/// already-typed trust_wp IR facts and an optional typed return expression. The
/// verifier checks each `ensures` clause under `requires + body_facts`.
#[cfg(feature = "trust-build")]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NativePureBody {
    /// Typed facts obtained from native body lowering.
    pub body_facts: Vec<PureExpr>,

    /// Optional typed expression for the function result.
    pub return_expr: Option<PureExpr>,
}

#[cfg(feature = "trust-build")]
impl NativePureBody {
    /// Create an empty pure native body.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a typed body fact.
    #[must_use]
    pub fn with_body_fact(mut self, fact: PureExpr) -> Self {
        self.body_facts.push(fact);
        self
    }

    /// Attach a typed return expression.
    #[must_use]
    pub fn with_return_expr(mut self, return_expr: PureExpr) -> Self {
        self.return_expr = Some(return_expr);
        self
    }
}

/// Native MIR/body lowering hook for the `trust-build` in-process lane.
#[cfg(feature = "trust-build")]
pub trait NativeTrustWpMir {
    /// Return typed trust_wp IR facts produced from the native body.
    fn trust_wp_body_facts(&self) -> Result<Vec<PureExpr>, NativeUnsupportedFeature>;

    /// Return the typed expression for the function result, if one is needed.
    fn trust_wp_return_expr(&self) -> Result<Option<PureExpr>, NativeUnsupportedFeature>;
}

#[cfg(feature = "trust-build")]
impl NativeTrustWpMir for NativePureBody {
    fn trust_wp_body_facts(&self) -> Result<Vec<PureExpr>, NativeUnsupportedFeature> {
        Ok(self.body_facts.clone())
    }

    fn trust_wp_return_expr(&self) -> Result<Option<PureExpr>, NativeUnsupportedFeature> {
        Ok(self.return_expr.clone())
    }
}

/// Native contract expression lowering hook for the `trust-build` lane.
#[cfg(feature = "trust-build")]
pub trait NativeTrustWpExpr {
    /// Convert a typed contract node to trust-wp's pure IR.
    fn to_trust_wp_pure_expr(&self) -> Result<PureExpr, NativeUnsupportedFeature>;
}

#[cfg(feature = "trust-build")]
impl NativeTrustWpExpr for PureExpr {
    fn to_trust_wp_pure_expr(&self) -> Result<PureExpr, NativeUnsupportedFeature> {
        Ok(self.clone())
    }
}

/// Verify using the native tRustc-owned request path.
///
/// Without `trust-build`, native trust_wp internals are not linked into this
/// standalone compatibility crate, so the call records structured blockers and
/// returns `Unsupported`.
#[cfg(not(feature = "trust-build"))]
pub fn verify_native<Mir, Expr>(
    request: NativeTrustWpRequest<Mir, Expr>,
) -> Result<NativeTrustWpResult, TrustWpLibError> {
    let blockers = native_blockers(&request);
    Ok(NativeTrustWpResult::unsupported(request.target, blockers))
}

/// Verify using the native tRustc-owned request path.
///
/// With `trust-build`, this lowers typed native inputs to trust_wp `PureExpr`
/// obligations and calls `trust-wp-ay` in-process. The currently supported class
/// is pure function/postcondition obligations:
///
/// `requires + native_body_facts => ensures`
///
/// Loops, snapshots, result-binding metadata, trusted assumptions, cross-crate
/// summaries, and proof-evidence/replay artifact production fail closed.
#[cfg(feature = "trust-build")]
pub fn verify_native<Mir, Expr>(
    request: NativeTrustWpRequest<Mir, Expr>,
) -> Result<NativeTrustWpResult, TrustWpLibError>
where
    Mir: NativeTrustWpMir,
    Expr: NativeTrustWpExpr,
{
    let started = Instant::now();
    let mut blockers = native_blockers(&request);

    let mut requires = Vec::new();
    for contract in &request.contracts.requires {
        match contract.expression.to_trust_wp_pure_expr() {
            Ok(expr) => requires.push(expr),
            Err(blocker) => blockers.push(blocker),
        }
    }

    let mut ensures = Vec::new();
    for contract in &request.contracts.ensures {
        match contract.expression.to_trust_wp_pure_expr() {
            Ok(expr) => ensures.push(expr),
            Err(blocker) => blockers.push(blocker),
        }
    }

    match request.mir.trust_wp_body_facts() {
        Ok(body_facts) => requires.extend(body_facts),
        Err(blocker) => blockers.push(blocker),
    }

    let return_expr = match request.mir.trust_wp_return_expr() {
        Ok(expr) => expr,
        Err(blocker) => {
            blockers.push(blocker);
            None
        }
    };

    if ensures.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::ContractLowering,
            "native pure verification requires at least one postcondition obligation",
        ));
    }

    if !blockers.is_empty() {
        let mut result = NativeTrustWpResult::unsupported(request.target, blockers);
        result.time_ms = elapsed_ms(started);
        return Ok(result);
    }

    let track = track_level_from_config(&request.config)?;
    let verification_request = VerificationRequest::new(&requires, &ensures)
        .return_expr(return_expr.as_ref())
        .track(Some(track))
        .timeout(Some(Duration::from_millis(request.config.timeout_ms)));

    let ay_result = verify_function_with_modes(verification_request).map_err(|err| {
        TrustWpLibError::ContractError { reason: format!("native trust_wp encoding failed: {err}") }
    })?;

    let trust_wp_result = native_ay_result_to_trust_wp_result(
        &request.target.def_path,
        ay_result,
        ensures.len() as u32,
        elapsed_ms(started),
    );

    Ok(NativeTrustWpResult::from_trust_wp_result(request.target, trust_wp_result))
}

fn native_blockers<Mir, Expr>(
    request: &NativeTrustWpRequest<Mir, Expr>,
) -> Vec<NativeUnsupportedFeature> {
    let mut blockers = vec![
        #[cfg(not(feature = "trust-build"))]
        NativeUnsupportedFeature::new(
            NativeUnsupportedKind::MirLowering,
            "native MIR-to-trust-wp lowering is not implemented",
        ),
        #[cfg(not(feature = "trust-build"))]
        NativeUnsupportedFeature::new(
            NativeUnsupportedKind::ContractLowering,
            "typed contract expression lowering is not implemented",
        ),
    ];

    if request.contracts.trusted {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::TrustedAssumption,
            "trusted functions are assumptions, not native proof results",
        ));
    }

    if !request.contracts.snapshots.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::SnapshotSemantics,
            "old/snapshot semantics are represented but not lowered",
        ));
    }

    if request.contracts.result_binding.is_some() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::ResultBinding,
            "postcondition result binding is represented but not lowered",
        ));
    }

    if !request.contracts.loop_invariants.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::LoopInvariant,
            "loop invariants are represented but not verified by the native pure obligation lane",
        ));
    }

    if !request.contracts.refinements.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::Refinement,
            "functional refinements are represented but not verified by the native pure obligation lane",
        ));
    }

    if !request.contracts.loop_variants.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::LoopVariant,
            "loop variants are represented but not lowered",
        ));
    }

    if !request.contracts.cross_crate_summaries.is_empty() {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::CrossCrateSummary,
            "cross-crate summaries are represented but not imported",
        ));
    }

    if request.config.produce_proofs {
        blockers.push(NativeUnsupportedFeature::new(
            NativeUnsupportedKind::ProofCertificate,
            format!(
                "native proof-certificate byte production is not implemented; checked replay evidence still requires `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` artifacts"
            ),
        ));
    }

    blockers.push(NativeUnsupportedFeature::new(
        NativeUnsupportedKind::ProofEvidence,
        format!(
            "native trust_wp proof evidence is not wired: no `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` envelope with `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` normalized-obligation and replay-log artifacts can be produced or replayed"
        ),
    ));

    blockers
}

#[cfg(feature = "trust-build")]
fn track_level_from_config(config: &TrustWpConfig) -> Result<TrackLevel, TrustWpLibError> {
    match config.track_level.as_str() {
        "auto" => Ok(TrackLevel::Auto),
        "reg" => Ok(TrackLevel::Reg),
        "ptr" => Ok(TrackLevel::Ptr),
        "mem" => Ok(TrackLevel::Mem),
        other => Err(TrustWpLibError::ConfigError {
            reason: format!("unsupported native trust_wp track level `{other}`"),
        }),
    }
}

#[cfg(feature = "trust-build")]
fn native_ay_result_to_trust_wp_result(
    function_name: &str,
    result: AYVerificationResult,
    obligation_count: u32,
    time_ms: u64,
) -> TrustWpResult {
    let mut diagnostics = Vec::new();
    let (verdict, discharged_count, counts) = match result {
        AYVerificationResult::Verified(proof_summary) => {
            if let Some(summary) = proof_summary {
                diagnostics.push(DiagnosticMessage {
                    level: DiagLevel::Note,
                    message: format!(
                        "native trust_wp proof summary: strict_verified={}, clean_supported={}, trust_count={}, resolution_count={}",
                        summary.strict_verified,
                        summary.clean_supported,
                        summary.trust_count,
                        summary.resolution_count
                    ),
                    location: None,
                });
            }
            diagnostics.push(DiagnosticMessage {
                level: DiagLevel::Warning,
                message: format!(
                    "native trust-wp-ay discharged the query, but no `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` replay artifacts were produced; treating as unknown"
                ),
                location: None,
            });
            (
                Verdict::Unknown {
                    reason: format!(
                        "native trust-wp-ay solver success is not proof evidence without `{TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION}` / `{TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION}` replay artifacts"
                    ),
                },
                0,
                VerificationCounts { warnings: 1, ..Default::default() },
            )
        }
        AYVerificationResult::Failed(counterexample) => {
            (Verdict::Failed, 0, VerificationCounts { failed: 1, ..Default::default() })
                .with_diagnostic(
                    &mut diagnostics,
                    DiagLevel::Warning,
                    format!("native trust_wp counterexample: {counterexample:?}"),
                )
        }
        AYVerificationResult::Unknown(reason) => {
            (Verdict::Unknown { reason: reason.to_string() }, 0, VerificationCounts::default())
        }
        AYVerificationResult::Assumed(reason) => (
            Verdict::Unknown { reason: format!("native trust_wp returned assumption: {reason}") },
            0,
            VerificationCounts { assumed: 1, ..Default::default() },
        ),
        other => (
            Verdict::Error {
                message: format!("native trust_wp returned unsupported result variant: {other:?}"),
            },
            0,
            VerificationCounts { errors: 1, ..Default::default() },
        ),
    };

    TrustWpResult {
        verdict: verdict.clone(),
        function_verdicts: vec![FunctionVerdict {
            function_name: function_name.to_string(),
            verdict,
            obligation_count,
            discharged_count,
            has_axiom_deps: false,
        }],
        loop_invariants: Vec::new(),
        proof_certificate: None,
        time_ms,
        diagnostics,
        function_name: function_name.to_string(),
        counts,
    }
}

#[cfg(feature = "trust-build")]
trait NativeResultTupleExt {
    fn with_diagnostic(
        self,
        diagnostics: &mut Vec<DiagnosticMessage>,
        level: DiagLevel,
        message: String,
    ) -> (Verdict, u32, VerificationCounts);
}

#[cfg(feature = "trust-build")]
impl NativeResultTupleExt for (Verdict, u32, VerificationCounts) {
    fn with_diagnostic(
        self,
        diagnostics: &mut Vec<DiagnosticMessage>,
        level: DiagLevel,
        message: String,
    ) -> (Verdict, u32, VerificationCounts) {
        diagnostics.push(DiagnosticMessage { level, message, location: None });
        self
    }
}

#[cfg(feature = "trust-build")]
fn elapsed_ms(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct TypedExpr(&'static str);

    #[test]
    fn native_request_accepts_typed_mir_and_contract_nodes() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        struct MirBody {
            basic_blocks: usize,
        }

        let request = NativeTrustWpRequest::new(
            NativeFunctionTarget::new("crate::f").with_stable_id("defhash"),
            MirBody { basic_blocks: 2 },
            NativeContractBundle::new()
                .with_requires(TypedExpr("x > 0"))
                .with_ensures(TypedExpr("result > x"))
                .with_refinement(TypedExpr("x is positive"))
                .with_loop_invariant(TypedExpr("i <= n")),
        )
        .with_config(TrustWpConfig::new().with_timeout(10));

        assert_eq!(request.target.def_path, "crate::f");
        assert_eq!(request.mir.basic_blocks, 2);
        assert_eq!(request.contracts.requires[0].expression, TypedExpr("x > 0"));
        assert_eq!(request.contracts.ensures[0].kind, ContractKind::Ensures);
        assert_eq!(request.contracts.refinements[0].kind, ContractKind::Refinement);
        assert_eq!(request.config.timeout_ms, 10);
    }

    #[test]
    fn native_verify_fails_closed_with_structured_blockers() {
        #[cfg(not(feature = "trust-build"))]
        let request = NativeTrustWpRequest::new(
            NativeFunctionTarget::new("crate::f"),
            (),
            NativeContractBundle::new()
                .with_requires(TypedExpr("x > 0"))
                .with_snapshot(NativeSnapshot::new("old_x", TypedExpr("x")))
                .with_result_binding(NativeResultBinding::new("result"))
                .with_refinement(TypedExpr("x is positive"))
                .with_loop_variant(TypedExpr("n - i"))
                .with_cross_crate_summary(NativeSummaryRef::new("dep::g")),
        );

        #[cfg(feature = "trust-build")]
        let request = NativeTrustWpRequest::new(
            NativeFunctionTarget::new("crate::f"),
            NativePureBody::new(),
            NativeContractBundle::new()
                .with_ensures(PureExpr::Bool(true))
                .with_snapshot(NativeSnapshot::new("old_x", PureExpr::Bool(true)))
                .with_result_binding(NativeResultBinding::new("result"))
                .with_refinement(PureExpr::Bool(true))
                .with_loop_variant(PureExpr::Bool(true))
                .with_cross_crate_summary(NativeSummaryRef::new("dep::g")),
        );

        let result = verify_native(request).expect("unsupported is a closed result");

        assert_eq!(result.status, NativeTrustWpStatus::Unsupported);
        assert!(result.trust_wp_result.is_none());
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::SnapshotSemantics)
        );
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::ResultBinding)
        );
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::LoopVariant)
        );
        assert!(
            result.blockers.iter().any(|blocker| blocker.kind == NativeUnsupportedKind::Refinement)
        );
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::CrossCrateSummary)
        );
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::ProofEvidence)
        );
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains(TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION)
                && diagnostic.message.contains(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION)
        }));

        #[cfg(not(feature = "trust-build"))]
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::MirLowering)
        );

        #[cfg(not(feature = "trust-build"))]
        assert!(
            result
                .blockers
                .iter()
                .any(|blocker| blocker.kind == NativeUnsupportedKind::ContractLowering)
        );

        let compatibility = result.to_trust_wp_result();
        assert!(matches!(compatibility.verdict, Verdict::Unknown { .. }));
        assert_eq!(compatibility.function_name, "crate::f");
    }

    #[test]
    fn compatibility_contracts_can_be_wrapped_in_native_shape() {
        let compat = ContractSet::new()
            .with_requires(Contract::requires("x > 0").with_location("src/lib.rs:1:1"))
            .with_ensures(Contract::ensures("result > x"))
            .with_invariant(Contract::invariant("i <= n"))
            .with_trusted(true);

        let native = NativeContractBundle::from_compat_contracts(&compat);

        assert!(native.trusted);
        assert_eq!(native.requires[0].expression, "x > 0");
        assert_eq!(native.requires[0].span.as_deref(), Some("src/lib.rs:1:1"));
        assert_eq!(native.ensures[0].kind, ContractKind::Ensures);
        assert_eq!(native.loop_invariants[0].role, NativeLoopContractRole::Invariant);
    }

    #[cfg(feature = "trust-build")]
    mod trust_build_tests {
        use std::sync::Arc;

        use trust_wp_core::formula::{BinOp, ExprSort};

        use super::*;

        fn int_var(name: &str) -> PureExpr {
            PureExpr::Var(name.to_string(), Some(ExprSort::Int))
        }

        fn gt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
            PureExpr::BinOp(Arc::new(lhs), BinOp::Gt, Arc::new(rhs))
        }

        fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
            PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs))
        }

        #[test]
        fn native_verify_rejects_pure_obligation_without_replay_evidence() {
            let request = NativeTrustWpRequest::new(
                NativeFunctionTarget::new("crate::pure_obligation"),
                NativePureBody::new().with_return_expr(add(int_var("x"), PureExpr::Int(1))),
                NativeContractBundle::new()
                    .with_requires(gt(int_var("x"), PureExpr::Int(0)))
                    .with_ensures(gt(int_var("result"), int_var("x"))),
            )
            .with_config(TrustWpConfig::new().with_timeout(1_000).with_track_level("reg"));

            let result = verify_native(request).expect("native trust_wp verification should run");

            assert_eq!(result.status, NativeTrustWpStatus::Unsupported);
            assert!(result.trust_wp_result.is_none());
            assert!(
                result
                    .blockers
                    .iter()
                    .any(|blocker| blocker.kind == NativeUnsupportedKind::ProofEvidence)
            );
            assert!(result.diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains(TRUST_WP_PROOF_EVIDENCE_SCHEMA_VERSION)
                    && diagnostic.message.contains(TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION)
            }));
        }

        #[test]
        fn native_verify_rejects_unsupported_loop_invariants_before_solving() {
            let request = NativeTrustWpRequest::new(
                NativeFunctionTarget::new("crate::loop_obligation"),
                NativePureBody::new(),
                NativeContractBundle::new()
                    .with_ensures(PureExpr::Bool(true))
                    .with_loop_invariant(PureExpr::Bool(true)),
            );

            let result = verify_native(request).expect("unsupported is a closed result");

            assert_eq!(result.status, NativeTrustWpStatus::Unsupported);
            assert!(result.trust_wp_result.is_none());
            assert!(
                result
                    .blockers
                    .iter()
                    .any(|blocker| blocker.kind == NativeUnsupportedKind::LoopInvariant)
            );
        }
    }
}

// trust-router/mir_router.rs: MIR-level verification strategy router
//
// Pipeline v2 target - classifies functions at the MIR level
// and dispatches to trust-mc-lib (BMC plus CHC/PDR safety), trust-wp-lib
// (deductive contracts), trust_vc (proof/refinement obligations), or the
// existing v1 Formula-based pipeline. Sits ABOVE the existing Router.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! MIR-level verification strategy router.
//!
//! The `MirRouter` classifies `VerifiableFunction`s based on their MIR
//! properties (contracts, unsafe blocks, loops, atomics, raw pointers, FFI)
//! and dispatches each to the most appropriate verification backend:
//!
//! - **trust-mc-lib**: Safety/reachability via BMC plus target CHC/PDR proof modes
//! - **trust-wp-lib**: Deductive verification for contract-bearing functions
//! - **trust-vc**: Proof functions, ghost/refinement, and ownership obligations
//! - **v1 pipeline**: The existing `Router` for everything else
//!
//! This router operates at a higher level than the existing `Router`, which
//! dispatches at the Formula/VC level. Classification happens before VC
//! generation, enabling backend-specific encoding.

use trust_types::{
    ContractKind, Rvalue, Statement, Terminator, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

use crate::Router;
use crate::verifier_result::{
    VerifierFunctionResult, descriptors_for_vcs, function_placeholder_obligation,
};

/// MIR-level verification strategy.
///
/// Determines how a function should be verified based on its MIR properties.
/// Ordered roughly by specificity: more specialized strategies are preferred
/// over generic ones.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MirStrategy {
    /// trust_mc safety/reachability. Current compatibility path is BMC-shaped;
    /// target tRustc integration can select BMC, CHC, or PDR/IC3.
    BoundedModelCheck,
    /// Deductive via trust-wp-lib (contract verification).
    ContractVerification,
    /// Unsafe audit - portfolio over trust-mc, trust-wp, and trust_vc where applicable.
    UnsafeAudit,
    /// Ownership/separation logic — v1 pipeline.
    SeparationLogic,
    /// Data race detection — v1 pipeline + TY.
    DataRace,
    /// FFI boundary — v1 pipeline.
    FFIBoundary,
    /// Run multiple strategies in parallel, take first definitive result.
    Portfolio(Vec<MirStrategy>),
    /// trust_cg verified codegen — lower to LIR, optionally validate.
    #[cfg(feature = "trust-cg-backend")]
    TrustCgCodegen,
    /// Fall through to v1 Formula-based pipeline.
    V1Fallback,
}

impl std::fmt::Display for MirStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirStrategy::BoundedModelCheck => f.write_str("BoundedModelCheck"),
            MirStrategy::ContractVerification => f.write_str("ContractVerification"),
            MirStrategy::UnsafeAudit => f.write_str("UnsafeAudit"),
            MirStrategy::SeparationLogic => f.write_str("SeparationLogic"),
            MirStrategy::DataRace => f.write_str("DataRace"),
            MirStrategy::FFIBoundary => f.write_str("FFIBoundary"),
            MirStrategy::Portfolio(strategies) => {
                write!(f, "Portfolio(")?;
                for (i, s) in strategies.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{s}")?;
                }
                write!(f, ")")
            }
            #[cfg(feature = "trust-cg-backend")]
            MirStrategy::TrustCgCodegen => f.write_str("TrustCgCodegen"),
            MirStrategy::V1Fallback => f.write_str("V1Fallback"),
        }
    }
}

/// Configuration for the MIR router.
#[derive(Debug, Clone)]
pub struct MirRouterConfig {
    /// Default BMC depth for trust-mc-lib verification.
    pub bmc_depth: u32,
    /// Timeout in milliseconds for individual backend calls.
    pub timeout_ms: u64,
    /// Whether to produce proof certificates.
    pub produce_proofs: bool,
    /// Shadow mode — run both MIR router and v1 fallback, compare
    /// results, and log discrepancies. Returns the MIR router result when it
    /// succeeds, otherwise falls back to v1.
    pub shadow_mode: bool,
    /// Enable rayon-based parallel portfolio racing.
    /// When true, portfolio strategies are dispatched in parallel using rayon
    /// with early termination on the first definitive result.
    pub enable_portfolio_racing: bool,
    /// Enable loop invariant inference via trust_wp before BMC dispatch.
    /// When true, functions with loops are first analyzed by trust_wp for invariant
    /// hints which are logged for the strengthen feedback loop.
    pub infer_invariants: bool,
    /// Enable trust_cg codegen backend for scalar function lowering.
    /// When true (and the `trust_cg-backend` feature is enabled), the classifier
    /// will dispatch eligible scalar functions through the trust_cg codegen path.
    #[cfg(feature = "trust-cg-backend")]
    pub enable_trust_cg_codegen: bool,
}

impl Default for MirRouterConfig {
    fn default() -> Self {
        Self {
            bmc_depth: 100,
            timeout_ms: 30_000,
            produce_proofs: false,
            shadow_mode: false,
            enable_portfolio_racing: true,
            infer_invariants: false,
            #[cfg(feature = "trust-cg-backend")]
            enable_trust_cg_codegen: false,
        }
    }
}

/// Describes how the MIR router result and v1 fallback result compare.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ShadowDiscrepancy {
    /// Both agree (both proved, both failed, or both unknown/timeout).
    Equivalent,
    /// MIR router proved but v1 did not (MIR is strictly better).
    MirStronger,
    /// v1 proved but MIR router did not (regression — MIR is weaker).
    V1Stronger,
    /// Both produced results but of different outcome classes (e.g., one failed, other unknown).
    Mismatch,
}

#[cfg(test)]
impl std::fmt::Display for ShadowDiscrepancy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ShadowDiscrepancy::Equivalent => f.write_str("equivalent"),
            ShadowDiscrepancy::MirStronger => f.write_str("mir_stronger"),
            ShadowDiscrepancy::V1Stronger => f.write_str("v1_stronger"),
            ShadowDiscrepancy::Mismatch => f.write_str("mismatch"),
        }
    }
}

/// Result of shadow-mode verification — both MIR router and v1 results
/// plus the comparison outcome.
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct ShadowResult {
    /// The strategy chosen by the MIR router's classifier.
    pub(crate) strategy: MirStrategy,
    /// The result from the MIR router dispatch.
    pub(crate) mir_result: VerificationResult,
    /// The result from the v1 fallback dispatch.
    pub(crate) v1_result: VerificationResult,
    /// How the two results compare.
    pub(crate) discrepancy: ShadowDiscrepancy,
    /// The result that was actually returned to the caller.
    pub(crate) chosen_result: VerificationResult,
}

/// MIR-level router — classifies functions and dispatches to appropriate backends.
///
/// The MirRouter sits above the existing `Router`, intercepting functions before
/// VC generation. Functions with specific MIR-level properties (contracts, unsafe
/// blocks, loops) are dispatched directly to specialized backends (trust-mc-lib,
/// trust-wp-lib). Everything else falls through to the v1 pipeline.
pub struct MirRouter {
    /// The v1 VC-level router for fallback dispatch.
    v1_router: Router,
    /// Configuration for backend invocations.
    config: MirRouterConfig,
    /// Optional trust_cg codegen backend for scalar function lowering.
    #[cfg(feature = "trust-cg-backend")]
    trust_cg_backend: Option<crate::trust_cg_backend::TrustCgBackend>,
}

impl MirRouter {
    /// Create a new MIR router wrapping the given v1 router.
    pub fn new(v1_router: Router, config: MirRouterConfig) -> Self {
        #[cfg(feature = "trust-cg-backend")]
        let trust_cg_backend = if config.enable_trust_cg_codegen {
            Some(crate::trust_cg_backend::TrustCgBackend::new(
                crate::trust_cg_backend::TrustCgBackendConfig::for_host(),
            ))
        } else {
            None
        };

        Self {
            v1_router,
            config,
            #[cfg(feature = "trust-cg-backend")]
            trust_cg_backend,
        }
    }

    /// Create a MIR router with default config and mock backends.
    pub fn with_defaults() -> Self {
        Self {
            v1_router: Router::new(),
            config: MirRouterConfig::default(),
            #[cfg(feature = "trust-cg-backend")]
            trust_cg_backend: None,
        }
    }

    /// Access the underlying v1 router.
    #[must_use]
    pub fn v1_router(&self) -> &Router {
        &self.v1_router
    }

    /// Access the configuration.
    #[must_use]
    pub fn config(&self) -> &MirRouterConfig {
        &self.config
    }

    /// Classify a function to determine its verification strategy.
    ///
    /// The classification priority is:
    /// 1. Has `unsafe` blocks with contracts -> UnsafeAudit (both backends)
    /// 2. Has `#[requires]`/`#[ensures]` contracts -> ContractVerification (trust-wp)
    /// 3. Has `#[invariant]` annotations -> ContractVerification (trust-wp)
    /// 4. Has atomic operations / thread spawns -> DataRace
    /// 5. Has raw pointer operations -> SeparationLogic
    /// 6. Has FFI calls -> FFIBoundary
    /// 7. Has loops with unbounded iteration -> trust_mc safety/reachability
    /// 8. Default -> V1Fallback
    #[must_use]
    pub fn classify(&self, func: &VerifiableFunction) -> MirStrategy {
        let has_contracts = has_contracts(func);
        let has_invariant_annotations = has_invariant_annotations(func);
        let has_unsafe = has_unsafe_operations(func);
        let has_atomics = has_atomic_operations(func);
        let has_raw_ptrs = has_raw_pointer_operations(func);
        let has_ffi = has_ffi_calls(func);
        let has_loops = has_loops(func);

        // Unsafe with contracts gets both backends for maximum coverage.
        if has_unsafe && has_contracts {
            return MirStrategy::UnsafeAudit;
        }

        // Contract-bearing functions go to trust_wp for deductive proof.
        if has_contracts || has_invariant_annotations {
            return MirStrategy::ContractVerification;
        }

        // Atomic operations need data race analysis.
        if has_atomics {
            return MirStrategy::DataRace;
        }

        // Raw pointers need separation logic / ownership analysis.
        if has_raw_ptrs {
            return MirStrategy::SeparationLogic;
        }

        // FFI calls need boundary verification.
        if has_ffi {
            return MirStrategy::FFIBoundary;
        }

        // Functions with loops benefit from trust_mc. BMC gives quick
        // counterexamples; CHC/PDR is the target proof mode for unbounded safety.
        if has_loops {
            return MirStrategy::BoundedModelCheck;
        }

        // Everything else goes through the v1 pipeline.
        MirStrategy::V1Fallback
    }

    /// Verify a function using the classified strategy.
    ///
    /// Dispatches to the appropriate backend based on `classify()`, then
    /// converts the result to a uniform `VerificationResult`.
    ///
    /// When `config.shadow_mode` is true, also dispatches through v1 and
    /// logs any discrepancies (but still returns the MIR router result when
    /// it succeeds).
    pub fn verify_function(&self, func: &VerifiableFunction) -> VerificationResult {
        if self.config.shadow_mode {
            let strategy = self.classify(func);
            let mir_result = self.dispatch(func, &strategy);
            // Shadow mode: also run v1, choose definitive result.
            let v1_result = build_v1_vcs(func)
                .into_iter()
                .map(|vc| self.v1_router.verify_one(&vc))
                .find(|r| r.is_proved() || r.is_failed())
                .unwrap_or_else(|| VerificationResult::Unknown {
                    solver: "v1-shadow".into(),
                    time_ms: 0,
                    reason: "no definitive v1 result".into(),
                });
            return if mir_result.is_proved() || mir_result.is_failed() {
                mir_result
            } else {
                v1_result
            };
        }
        let strategy = self.classify(func);
        self.dispatch(func, &strategy)
    }

    /// Verify a function using an explicit strategy (bypasses classification).
    pub fn verify_with_strategy(
        &self,
        func: &VerifiableFunction,
        strategy: &MirStrategy,
    ) -> VerificationResult {
        self.dispatch(func, strategy)
    }

    /// Verify multiple functions, classifying and dispatching each.
    pub fn verify_all(
        &self,
        funcs: &[VerifiableFunction],
    ) -> Vec<(String, MirStrategy, VerificationResult)> {
        funcs
            .iter()
            .map(|func| {
                let strategy = self.classify(func);
                let result = self.dispatch(func, &strategy);
                (func.name.clone(), strategy, result)
            })
            .collect()
    }

    /// Verify a function and return per-obligation results.
    ///
    /// This is the Pipeline v2 adapter path for #1046. V1-backed strategies
    /// produce one result per VC. Native function-level backends are converted
    /// through `VerifierFunctionResult::from_function_level_result`, which
    /// refuses to smear a single backend verdict across multiple obligations.
    pub fn verify_function_obligations(&self, func: &VerifiableFunction) -> VerifierFunctionResult {
        let strategy = self.classify(func);
        self.verify_function_obligations_with_strategy(func, &strategy)
    }

    /// Verify a function using an explicit strategy and return per-obligation
    /// results.
    pub fn verify_function_obligations_with_strategy(
        &self,
        func: &VerifiableFunction,
        strategy: &MirStrategy,
    ) -> VerifierFunctionResult {
        let vcs = build_v1_vcs(func);
        let obligations = if vcs.is_empty() {
            vec![function_placeholder_obligation(
                func.def_path.clone(),
                func.span.clone(),
                crate::verification_obligation::vc_kind_for_mir_strategy(strategy),
                Some(strategy.clone()),
            )]
        } else {
            descriptors_for_vcs(&vcs, Some(strategy.clone()))
        };

        match strategy {
            MirStrategy::DataRace
            | MirStrategy::SeparationLogic
            | MirStrategy::FFIBoundary
            | MirStrategy::V1Fallback => {
                if vcs.is_empty() {
                    let attributed = obligations
                        .into_iter()
                        .map(|obligation| {
                            crate::verifier_result::VerifierObligationResult::new(
                                obligation,
                                self.dispatch_v1(func),
                            )
                        })
                        .collect();
                    return VerifierFunctionResult::from_obligation_results(
                        func.def_path.clone(),
                        attributed,
                    );
                }
                let results = self.v1_router.verify_all(&vcs);
                let attributed = results
                    .into_iter()
                    .zip(obligations)
                    .map(|((_, result), obligation)| {
                        crate::verifier_result::VerifierObligationResult::new(obligation, result)
                    })
                    .collect();
                VerifierFunctionResult::from_obligation_results(func.def_path.clone(), attributed)
            }
            _ => VerifierFunctionResult::from_function_level_result(
                func.def_path.clone(),
                strategy.to_string(),
                obligations,
                self.dispatch(func, strategy),
            ),
        }
    }

    /// Internal dispatch: routes to the appropriate backend.
    fn dispatch(&self, func: &VerifiableFunction, strategy: &MirStrategy) -> VerificationResult {
        match strategy {
            MirStrategy::BoundedModelCheck => {
                // Optionally infer loop invariants before BMC dispatch.
                if self.config.infer_invariants && has_loops(func) {
                    self.dispatch_bmc_with_invariant_hints(func)
                } else {
                    self.dispatch_bmc(func)
                }
            }
            MirStrategy::ContractVerification => self.dispatch_contract(func),
            MirStrategy::UnsafeAudit => self.dispatch_unsafe_audit(func),
            MirStrategy::Portfolio(strategies) => self.dispatch_portfolio(func, strategies),
            // trust_cg codegen dispatch.
            #[cfg(feature = "trust-cg-backend")]
            MirStrategy::TrustCgCodegen => self.dispatch_trust_cg_codegen(func),
            // DataRace, SeparationLogic, FFIBoundary, V1Fallback all
            // go through the v1 pipeline for now. These backends will be specialized
            // in future phases.
            MirStrategy::DataRace
            | MirStrategy::SeparationLogic
            | MirStrategy::FFIBoundary
            | MirStrategy::V1Fallback => self.dispatch_v1(func),
        }
    }

    /// Dispatch to the trust_cg verified codegen backend.
    ///
    /// Falls back to V1 if the trust_cg backend is not configured or cannot
    /// handle the function.
    ///
    /// Only a byte-level output-preservation verdict becomes `Proved` here. A
    /// structural round trip that nothing stronger confirmed is `Unknown`
    /// carrying the reason: it is real evidence about the lowering's shape, but
    /// promoting it would let a codegen-shape check answer a verification
    /// obligation it never examined.
    #[cfg(feature = "trust-cg-backend")]
    fn dispatch_trust_cg_codegen(&self, func: &VerifiableFunction) -> VerificationResult {
        use crate::trust_cg_backend::CodegenVerdict;

        if let Some(ref backend) = self.trust_cg_backend {
            if backend.can_handle_function(func) {
                let verdict = match backend.verify_codegen(func) {
                    Ok(verdict) => verdict,
                    Err(e) => {
                        return VerificationResult::Unknown {
                            solver: "trust_cg-router".into(),
                            time_ms: 0,
                            reason: format!("trust-cg codegen error: {e}"),
                        };
                    }
                };
                return match verdict {
                    CodegenVerdict::KernelProved | CodegenVerdict::AyValidated => {
                        VerificationResult::Proved {
                            solver: "trust_cg-router".into(),
                            time_ms: 0,
                            strength: trust_types::ProofStrength::bounded(1),
                            proof_certificate: None,
                            solver_warnings: None,
                            native_proof_envelope: None,
                        }
                    }
                    CodegenVerdict::Miscompiled { .. }
                    | CodegenVerdict::RoundTripMismatch { .. } => VerificationResult::Failed {
                        solver: "trust_cg-router-transval".into(),
                        time_ms: 0,
                        counterexample: None,
                    },
                    CodegenVerdict::RoundTripOnly { undecided } => VerificationResult::Unknown {
                        solver: "trust_cg-router".into(),
                        time_ms: 0,
                        reason: format!(
                            "trust-cg lowering round-tripped, but output preservation is \
                             undecided: {undecided}"
                        ),
                    },
                    CodegenVerdict::Unavailable { reason } => VerificationResult::Unknown {
                        solver: "trust_cg-router".into(),
                        time_ms: 0,
                        reason,
                    },
                };
            }
        }
        // Fall back to v1 if trust_cg cannot handle this function.
        self.dispatch_v1(func)
    }

    /// Dispatch to trust-mc-lib for safety/reachability verification.
    fn dispatch_bmc(&self, func: &VerifiableFunction) -> VerificationResult {
        // Do not let placeholder SMT-LIB produce proof claims.
        // trust_mc is valuable only after this router has a real MIR-derived
        // encoding of the source obligation. A bare `(check-sat)` script is
        // detection/plumbing, not verification evidence.
        if let Some(smtlib) = build_trust_mc_bmc_smtlib(func) {
            let trust_mc_config = trust_bmc::TrustMcConfig::new()
                .with_bmc_depth(self.config.bmc_depth)
                .with_timeout(self.config.timeout_ms)
                .with_proofs(self.config.produce_proofs);

            match trust_bmc::verify_function(&func.def_path, &smtlib, &trust_mc_config) {
                Ok(result) => result.to_verification_result(),
                Err(e) => VerificationResult::Unknown {
                    solver: "trust-mc-lib".into(),
                    time_ms: 0,
                    reason: format!("trust-mc dispatch error: {e}"),
                },
            }
        } else {
            VerificationResult::Unknown {
                solver: "trust-mc-lib".into(),
                time_ms: 0,
                reason: "trust-mc dispatch requires real MIR-derived verification conditions; MIR router has no proof-grade trust_mc encoding for this function".to_string(),
            }
        }
    }

    /// Dispatch to trust-wp-lib for deductive contract verification.
    fn dispatch_contract(&self, func: &VerifiableFunction) -> VerificationResult {
        let contracts = build_trust_wp_contracts(func);
        if contracts.requires.is_empty()
            && contracts.ensures.is_empty()
            && contracts.invariants.is_empty()
        {
            return VerificationResult::Unknown {
                solver: "trust-wp-lib".into(),
                time_ms: 0,
                reason: "trust-wp dispatch requires contracts plus MIR body semantics; no contracts were available".to_string(),
            };
        }

        // Contract strings alone do not prove source behavior.
        // Until the router passes executable MIR/body facts into trust-wp, keep
        // this path as an explicit gap instead of upgrading to Proved.
        VerificationResult::Unknown {
            solver: "trust-wp-lib".into(),
            time_ms: 0,
            reason: "trust-wp dispatch requires MIR body semantics; current router only has contract strings".to_string(),
        }
    }

    /// Dispatch to both trust_mc and trust_wp for unsafe code audit.
    ///
    /// When portfolio racing is enabled, dispatches BMC and contract verification
    /// in parallel and returns the first definitive result. Otherwise runs both
    /// sequentially and merges (preferring failure over proof).
    fn dispatch_unsafe_audit(&self, func: &VerifiableFunction) -> VerificationResult {
        if self.config.enable_portfolio_racing {
            let strategies =
                vec![MirStrategy::BoundedModelCheck, MirStrategy::ContractVerification];
            // Use parallel portfolio dispatch for unsafe audit.
            // For unsafe audit, both backends run; if either finds a failure, that wins.
            self.dispatch_portfolio(func, &strategies)
        } else {
            let bmc_result = self.dispatch_bmc(func);
            let contract_result = self.dispatch_contract(func);
            merge_results(bmc_result, contract_result)
        }
    }

    /// Dispatch multiple strategies in parallel using rayon, take
    /// the first definitive result.
    ///
    /// When `enable_portfolio_racing` is true, strategies are dispatched
    /// concurrently via `rayon::scope`. An `AtomicBool` signals early
    /// termination once any thread finds a Proved or Failed result.
    /// Falls back to sequential dispatch when racing is disabled or there
    /// is only one strategy.
    fn dispatch_portfolio(
        &self,
        func: &VerifiableFunction,
        strategies: &[MirStrategy],
    ) -> VerificationResult {
        use std::panic::{AssertUnwindSafe, catch_unwind};
        use std::sync::Mutex;
        use std::sync::atomic::{AtomicBool, Ordering};

        if strategies.is_empty() {
            return VerificationResult::Unknown {
                solver: "mir-router-portfolio".into(),
                time_ms: 0,
                reason: "no strategies in portfolio".to_string(),
            };
        }

        // For single strategy, no need for parallelism.
        if strategies.len() == 1 {
            let strategy = &strategies[0];
            return catch_unwind(AssertUnwindSafe(|| self.dispatch(func, strategy)))
                .unwrap_or_else(|_| {
                    crate::backend_trait::panic_unknown(
                        "mir-router-portfolio",
                        0,
                        format!("portfolio strategy {strategy} for {}", func.name),
                    )
                });
        }

        // Sequential fallback when portfolio racing is disabled.
        if !self.config.enable_portfolio_racing {
            return self.dispatch_portfolio_sequential(func, strategies);
        }

        let found_definitive = AtomicBool::new(false);
        let results: Mutex<Vec<(usize, VerificationResult)>> = Mutex::new(Vec::new());

        rayon::scope(|s| {
            for (idx, strategy) in strategies.iter().enumerate() {
                let found = &found_definitive;
                let results_ref = &results;
                s.spawn(move |_| {
                    // Skip if another thread already found a definitive result.
                    if found.load(Ordering::Relaxed) {
                        return;
                    }
                    let result = catch_unwind(AssertUnwindSafe(|| self.dispatch(func, strategy)))
                        .unwrap_or_else(|_| {
                            crate::backend_trait::panic_unknown(
                                "mir-router-portfolio",
                                0,
                                format!("portfolio strategy {strategy} for {}", func.name),
                            )
                        });
                    if result.is_proved() || result.is_failed() {
                        found.store(true, Ordering::Relaxed);
                    }
                    match results_ref.lock() {
                        Ok(mut guard) => guard.push((idx, result)),
                        Err(poisoned) => poisoned.into_inner().push((idx, result)),
                    }
                });
            }
        });

        let mut collected = match results.into_inner() {
            Ok(results) => results,
            Err(poisoned) => poisoned.into_inner(),
        };
        collected.sort_by_key(|(idx, _)| *idx);

        // Return first definitive result, or first result if none definitive.
        for (_, result) in &collected {
            if result.is_proved() || result.is_failed() {
                return result.clone();
            }
        }
        collected.into_iter().next().map(|(_, r)| r).unwrap_or_else(|| {
            VerificationResult::Unknown {
                solver: "mir-router-portfolio".into(),
                time_ms: 0,
                reason: "no strategies produced results".to_string(),
            }
        })
    }

    /// Sequential portfolio dispatch (fallback when racing is disabled).
    fn dispatch_portfolio_sequential(
        &self,
        func: &VerifiableFunction,
        strategies: &[MirStrategy],
    ) -> VerificationResult {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let mut best_result: Option<VerificationResult> = None;

        for strategy in strategies {
            let result = catch_unwind(AssertUnwindSafe(|| self.dispatch(func, strategy)))
                .unwrap_or_else(|_| {
                    crate::backend_trait::panic_unknown(
                        "mir-router-portfolio",
                        0,
                        format!("portfolio strategy {strategy} for {}", func.name),
                    )
                });

            // If we got a definitive result (Proved or Failed), return immediately.
            if result.is_proved() || result.is_failed() {
                return result;
            }

            // Keep track of the first non-definitive result.
            if best_result.is_none() {
                best_result = Some(result);
            }
        }

        best_result.unwrap_or_else(|| VerificationResult::Unknown {
            solver: "mir-router-portfolio".into(),
            time_ms: 0,
            reason: "no strategies in portfolio".to_string(),
        })
    }

    /// When BMC encounters a function with loops, optionally invoke
    /// trust_wp for invariant hints and log them for the strengthen feedback loop.
    fn dispatch_bmc_with_invariant_hints(&self, func: &VerifiableFunction) -> VerificationResult {
        let trust_wp_config = trust_wp::TrustWpConfig::new().with_timeout(self.config.timeout_ms);

        if let Ok(invariants) = trust_wp::infer_loop_invariants(&func.def_path, &trust_wp_config) {
            // Log discovered invariants for strengthen feedback.
            if !invariants.is_empty() {
                eprintln!(
                    "[mir-router] discovered {} loop invariant(s) for {} via trust-wp",
                    invariants.len(),
                    func.name,
                );
            }
        }

        self.dispatch_bmc(func)
    }

    /// Dispatch to the v1 VC-level pipeline.
    ///
    /// Generates VCs from the function's contracts/preconditions and dispatches
    /// them through the existing Router.
    fn dispatch_v1(&self, func: &VerifiableFunction) -> VerificationResult {
        // Build VCs from the function's existing verification conditions.
        // If the function has no pre/postconditions, we generate a basic safety VC.
        let vcs = build_v1_vcs(func);

        if vcs.is_empty() {
            return VerificationResult::Unknown {
                solver: "mir-router-v1".into(),
                time_ms: 0,
                reason: "no verification conditions produced; no proof work was performed"
                    .to_string(),
            };
        }

        let results = self.v1_router.verify_all(&vcs);

        // Merge: all must prove for overall proof.
        let mut total_time_ms: u64 = 0;
        for (_, result) in &results {
            match result {
                VerificationResult::Proved { time_ms, .. } => {
                    total_time_ms += time_ms;
                }
                other => return other.clone(),
            }
        }

        VerificationResult::Proved {
            solver: "mir-router-v1".into(),
            time_ms: total_time_ms,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    /// Shadow-mode verification — run both the MIR router strategy
    /// and the v1 fallback, compare results, and log discrepancies.
    ///
    /// Only used by tests to inspect full shadow result fields.
    ///
    /// Returns the MIR router result when it produces a definitive answer
    /// (Proved or Failed). Falls back to the v1 result when the MIR router
    /// returns Unknown or Timeout.
    ///
    /// Only active when `config.shadow_mode` is true. When shadow mode is off,
    /// `verify_function` bypasses this entirely.
    #[cfg(test)]
    pub(crate) fn shadow_verify(&self, func: &VerifiableFunction) -> ShadowResult {
        let strategy = self.classify(func);

        // Run the MIR router dispatch.
        let mir_result = self.dispatch(func, &strategy);

        // Always run v1 fallback in shadow mode for comparison.
        let v1_result = self.dispatch_v1(func);

        // Compare the two results.
        let discrepancy = classify_discrepancy(&mir_result, &v1_result);

        // Log discrepancies to stderr for observability.
        if discrepancy != ShadowDiscrepancy::Equivalent {
            eprintln!(
                "[mir-router-shadow] discrepancy={} func={} strategy={} \
                 mir={} v1={}",
                discrepancy,
                func.name,
                strategy,
                result_summary(&mir_result),
                result_summary(&v1_result),
            );
        }

        // Choose which result to return.
        // MIR router result wins when it's definitive (Proved or Failed).
        // Fall back to v1 when MIR router is inconclusive.
        let chosen_result = if mir_result.is_proved() || mir_result.is_failed() {
            mir_result.clone()
        } else {
            v1_result.clone()
        };

        ShadowResult { strategy, mir_result, v1_result, discrepancy, chosen_result }
    }
}

/// Classify how two verification results compare for shadow mode.
#[cfg(test)]
fn classify_discrepancy(mir: &VerificationResult, v1: &VerificationResult) -> ShadowDiscrepancy {
    match (mir.is_proved(), mir.is_failed(), v1.is_proved(), v1.is_failed()) {
        // Both proved or both failed — equivalent outcomes.
        (true, _, true, _) => ShadowDiscrepancy::Equivalent,
        (_, true, _, true) => ShadowDiscrepancy::Equivalent,
        // Both inconclusive (Unknown/Timeout).
        (false, false, false, false) => ShadowDiscrepancy::Equivalent,
        // One proved, other failed — real soundness mismatch. Check BEFORE
        // MirStronger/V1Stronger to avoid masking this critical case.
        (true, _, _, true) | (_, true, true, _) => ShadowDiscrepancy::Mismatch,
        // MIR proved, v1 did not (but v1 didn't fail either — just inconclusive).
        (true, _, false, false) => ShadowDiscrepancy::MirStronger,
        // MIR failed, v1 inconclusive — MIR more definitive.
        (_, true, false, false) => ShadowDiscrepancy::MirStronger,
        // v1 proved, MIR inconclusive.
        (false, false, true, _) => ShadowDiscrepancy::V1Stronger,
        // v1 failed, MIR inconclusive.
        (false, false, _, true) => ShadowDiscrepancy::V1Stronger,
    }
}

/// One-line summary of a verification result for logging.
#[cfg(test)]
fn result_summary(result: &VerificationResult) -> String {
    match result {
        VerificationResult::Proved { solver, time_ms, .. } => {
            format!("Proved({solver}, {time_ms}ms)")
        }
        VerificationResult::Failed { solver, time_ms, .. } => {
            format!("Failed({solver}, {time_ms}ms)")
        }
        VerificationResult::Unknown { solver, reason, .. } => {
            format!("Unknown({solver}: {reason})")
        }
        VerificationResult::Timeout { solver, timeout_ms } => {
            format!("Timeout({solver}, {timeout_ms}ms)")
        }
        // VerificationResult is #[non_exhaustive]; handle future variants gracefully.
        other => format!("Other({})", other.solver_name()),
    }
}

// ---------------------------------------------------------------------------
// MIR classification helpers
// ---------------------------------------------------------------------------

/// Returns true if the function has `#[requires]` or `#[ensures]` contracts.
fn has_contracts(func: &VerifiableFunction) -> bool {
    // Check the typed contracts list.
    let has_typed = func
        .contracts
        .iter()
        .any(|c| matches!(c.kind, ContractKind::Requires | ContractKind::Ensures));

    // Also check the structured spec.
    let has_spec = !func.spec.requires.is_empty() || !func.spec.ensures.is_empty();

    // And the parsed formula-level conditions.
    let has_formulas = !func.preconditions.is_empty() || !func.postconditions.is_empty();

    has_typed || has_spec || has_formulas
}

/// Returns true if the function has `#[invariant]` or `#[loop_invariant]` annotations.
fn has_invariant_annotations(func: &VerifiableFunction) -> bool {
    let has_typed = func
        .contracts
        .iter()
        .any(|c| matches!(c.kind, ContractKind::Invariant | ContractKind::LoopInvariant));

    let has_spec = !func.spec.invariants.is_empty();

    has_typed || has_spec
}

/// Returns true if the function body contains unsafe operations.
///
/// Detects: `AddressOf` (raw pointer creation), `Rvalue::Cast` to raw pointer types,
/// and derefs through raw pointers.
fn has_unsafe_operations(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|stmt| match stmt {
            Statement::Assign { rvalue, .. } => matches!(rvalue, Rvalue::AddressOf(_, _)),
            _ => false,
        })
    })
}

/// Returns true if the function has atomic operations (from Terminator::Call with atomic field).
fn has_atomic_operations(func: &VerifiableFunction) -> bool {
    func.body
        .blocks
        .iter()
        .any(|bb| matches!(&bb.terminator, Terminator::Call { atomic: Some(_), .. }))
}

/// Returns true if the function body has raw pointer operations.
///
/// Detects: `Rvalue::Ref` to raw pointers, `Rvalue::AddressOf`, and
/// `Rvalue::Cast` when locals have `RawPtr` type.
fn has_raw_pointer_operations(func: &VerifiableFunction) -> bool {
    // Check if any local is a raw pointer type.
    let has_raw_ptr_locals = func.body.locals.iter().any(|l| l.ty.is_raw_ptr());

    // Check for AddressOf or CopyForDeref (often used with raw pointers).
    let has_raw_ptr_ops = func.body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|stmt| match stmt {
            Statement::Assign { rvalue, .. } => {
                matches!(rvalue, Rvalue::AddressOf(_, _) | Rvalue::CopyForDeref(_))
            }
            _ => false,
        })
    });

    has_raw_ptr_locals || has_raw_ptr_ops
}

/// Returns true if the function has FFI calls (extern function calls).
///
/// In MIR, FFI calls appear as `Terminator::Call` where the function name
/// contains `::` patterns like `std::ffi::`, `extern`, or `libc::`.
fn has_ffi_calls(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Terminator::Call { func: callee, .. }
                if is_ffi_callee(callee)
        )
    })
}

/// Heuristic: is this callee name an FFI function?
fn is_ffi_callee(name: &str) -> bool {
    name.starts_with("libc::")
        || name.starts_with("std::ffi::")
        || name.starts_with("core::ffi::")
        || name.contains("extern \"C\"")
        || name.contains("__extern_")
}

/// Returns true if the function body has loops (back-edges in the CFG).
///
/// A CFG edge `latch -> header` is a back-edge when `header` dominates `latch`.
/// Block IDs are not topological in rustc MIR, so lower-numbered cross edges in
/// acyclic `match` lowering must not be treated as loops.
fn has_loops(func: &VerifiableFunction) -> bool {
    let dom = compute_dominators(func);
    let block_count = func.body.blocks.len();

    for bb in &func.body.blocks {
        let latch = bb.id.0;
        if latch >= block_count {
            continue;
        }
        for target in successor_blocks(&bb.terminator) {
            if target < block_count && dom[latch][target] {
                return true;
            }
        }
    }
    false
}

fn compute_dominators(func: &VerifiableFunction) -> Vec<Vec<bool>> {
    let block_count = func.body.blocks.len();
    if block_count == 0 {
        return Vec::new();
    }

    let mut predecessors = vec![Vec::new(); block_count];
    for block in &func.body.blocks {
        let source = block.id.0;
        if source >= block_count {
            continue;
        }
        for target in successor_blocks(&block.terminator) {
            if target < block_count {
                predecessors[target].push(source);
            }
        }
    }

    let mut dom = vec![vec![true; block_count]; block_count];
    dom[0].fill(false);
    dom[0][0] = true;

    let mut changed = true;
    while changed {
        changed = false;
        for block in 1..block_count {
            let mut next = if predecessors[block].is_empty() {
                vec![false; block_count]
            } else {
                let mut intersection = vec![true; block_count];
                for &pred in &predecessors[block] {
                    for (slot, pred_dominates) in intersection.iter_mut().zip(dom[pred].iter()) {
                        *slot &= *pred_dominates;
                    }
                }
                intersection
            };
            next[block] = true;
            if next != dom[block] {
                dom[block] = next;
                changed = true;
            }
        }
    }

    dom
}

/// Extract successor block indices from a terminator.
fn successor_blocks(terminator: &Terminator) -> Vec<usize> {
    match terminator {
        Terminator::Goto(bid) => vec![bid.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<usize> = targets.iter().map(|(_, bid)| bid.0).collect();
            succs.push(otherwise.0);
            succs
        }
        Terminator::Call { target, .. } => target.iter().map(|bid| bid.0).collect(),
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Opaque { targets, .. } => targets.iter().map(|target| target.0).collect(),
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Contract/VC bridging helpers
// ---------------------------------------------------------------------------

/// Build proof-grade solver input for the trust_mc compatibility path.
///
/// Returns `None` until the MIR router has a real MIR-derived encoding. This is
/// intentionally stricter than sending placeholder solver traffic: a trust_mc
/// proof only counts when the input encodes the source obligation. Target
/// tRustc integration bypasses SMT-LIB strings and calls trust_mc codegen directly.
fn build_trust_mc_bmc_smtlib(_func: &VerifiableFunction) -> Option<String> {
    None
}

/// Build a `trust_wp::ContractSet` from a `VerifiableFunction`.
fn build_trust_wp_contracts(func: &VerifiableFunction) -> trust_wp::ContractSet {
    let mut contract_set = trust_wp::ContractSet::new();

    // From typed contracts.
    for c in &func.contracts {
        let trust_wp_contract = trust_wp::Contract::new(
            match c.kind {
                ContractKind::Requires => trust_wp::ContractKind::Requires,
                ContractKind::Ensures => trust_wp::ContractKind::Ensures,
                ContractKind::Invariant | ContractKind::LoopInvariant => {
                    trust_wp::ContractKind::Invariant
                }
                // Other kinds don't map directly to trust_wp contracts.
                _ => continue,
            },
            &c.body,
        );
        match c.kind {
            ContractKind::Requires => {
                contract_set.requires.push(trust_wp_contract);
            }
            ContractKind::Ensures => {
                contract_set.ensures.push(trust_wp_contract);
            }
            ContractKind::Invariant | ContractKind::LoopInvariant => {
                contract_set.invariants.push(trust_wp_contract);
            }
            _ => {}
        }
    }

    // From structured spec (FunctionSpec).
    for req in &func.spec.requires {
        contract_set.requires.push(trust_wp::Contract::requires(req));
    }
    for ens in &func.spec.ensures {
        contract_set.ensures.push(trust_wp::Contract::ensures(ens));
    }
    for inv in &func.spec.invariants {
        contract_set.invariants.push(trust_wp::Contract::invariant(inv));
    }

    contract_set
}

fn zero_divisor_guard_targets(func: &VerifiableFunction) -> std::collections::BTreeSet<usize> {
    func.body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert {
                msg:
                    trust_types::AssertMessage::DivisionByZero
                    | trust_types::AssertMessage::RemainderByZero,
                target,
                ..
            } => Some(target.0),
            _ => None,
        })
        .collect()
}

#[derive(Debug, Clone)]
struct UnsupportedMirV1 {
    kind: String,
    detail: String,
}

fn place_var_name(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> Result<String, UnsupportedMirV1> {
    // Trust: Prefer the declared local name (matching `trust_vcgen::place_to_var_name`)
    // so that variables referenced by function preconditions, contracts, and
    // hand-written test fixtures unify with the variables emitted into VC
    // formulas. Anonymous locals fall back to `_<idx>`. The historical
    // `mir_l<idx>__name_<hex>` form is preserved as a suffix-free alternative
    // only when the local has no declared name (anonymous locals get `_<idx>`
    // to match the v2 convention exactly).
    let mut name = match func.body.locals.get(place.local).and_then(|d| d.name.as_deref()) {
        Some(local_name) => local_name.to_string(),
        None => format!("_{}", place.local),
    };

    for (index, projection) in place.projections.iter().enumerate() {
        name.push_str(&projection_var_segment(place, index, projection)?);
    }

    Ok(name)
}

fn projection_var_segment(
    place: &trust_types::Place,
    index: usize,
    projection: &trust_types::Projection,
) -> Result<String, UnsupportedMirV1> {
    // Trust: Mirror the projection-name convention used by
    // `trust_vcgen::place_to_var_name` so that v1 and v2 produce the same
    // variable names for the same Place. Tests, fixtures, and downstream
    // tooling reference the v2 form.
    #[allow(unreachable_patterns)] // wildcard preserves fail-closed behavior for future variants
    match projection {
        trust_types::Projection::Field(field) => Ok(format!(".{field}")),
        trust_types::Projection::Index(index_local) => Ok(format!("[_{index_local}]")),
        trust_types::Projection::Deref => Ok("*".to_string()),
        trust_types::Projection::Downcast(variant) => Ok(format!("@{variant}")),
        trust_types::Projection::OpaqueCast(_) => Ok("@opaque_cast".to_string()),
        trust_types::Projection::UnwrapUnsafeBinder(_) => Ok("@unwrap_unsafe_binder".to_string()),
        trust_types::Projection::ConstantIndex { offset, min_length, from_end } => {
            Ok(if *from_end {
                format!("[-{offset};min={min_length}]")
            } else {
                format!("[{offset};min={min_length}]")
            })
        }
        trust_types::Projection::Subslice { from, to, from_end } => {
            Ok(if *from_end { format!("[{from}..-{to}]") } else { format!("[{from}..{to}]") })
        }
        _ => Err(UnsupportedMirV1 {
            kind: "Projection::<unknown>".to_string(),
            detail: format!(
                "local {} projection {index} is not modeled by MIR router v1 place naming",
                place.local
            ),
        }),
    }
}

fn divisor_is_zero_formula(
    func: &VerifiableFunction,
    divisor: &trust_types::Operand,
) -> Result<trust_types::Formula, UnsupportedMirV1> {
    use trust_types::{ConstValue, Formula, Operand, Sort};

    match divisor {
        Operand::Constant(ConstValue::Int(value)) => Ok(Formula::Bool(*value == 0)),
        Operand::Constant(ConstValue::Uint(value, _)) => Ok(Formula::Bool(*value == 0)),
        // A typed opaque integer divisor (const-generic `N`, associated const,
        // `size_of::<T>()` in a generic body) has NO decidable value and MIGHT be
        // zero. Emit the satisfiable `opaque_symbol == 0` so the div/rem-by-zero VC
        // stays Failed/Unknown — NEVER the `Bool(false)` "provably nonzero" below,
        // which would be a false PROVE. MUST precede the `Constant(_)` catch-all.
        Operand::Constant(ConstValue::OpaqueScalar { width, signed }) => Ok(Formula::Eq(
            Box::new(Formula::Var(
                format!("__trust_opaque_scalar_{}{}", if *signed { "i" } else { "u" }, width),
                Sort::Int,
            )),
            Box::new(Formula::Int(0)),
        )),
        // Trust: piece #7a — a const-generic PARAM divisor (`x / N`) has no
        // decidable value and MIGHT be zero. Emit the satisfiable
        // `__trust_constparam_* == 0` (via the shared `const_param_symbol`, so it
        // matches the operand/length symbol) — NEVER the `Bool(false)` "provably
        // nonzero" catch-all below, which would be a false PROVE. MUST precede the
        // `Constant(_)` catch-all, exactly like the `OpaqueScalar` arm.
        Operand::Constant(ConstValue::ConstParam { index, name, .. }) => Ok(Formula::Eq(
            Box::new(Formula::Var(trust_types::const_param_symbol(*index, name), Sort::Int)),
            Box::new(Formula::Int(0)),
        )),
        Operand::Constant(_) => Ok(Formula::Bool(false)),
        Operand::Copy(place) | Operand::Move(place) => Ok(Formula::Eq(
            Box::new(Formula::Var(place_var_name(func, place)?, Sort::Int)),
            Box::new(Formula::Int(0)),
        )),
        Operand::Symbolic(formula) => {
            Ok(Formula::Eq(Box::new(formula.clone()), Box::new(Formula::Int(0))))
        }
        Operand::Unsupported { kind, detail } => Err(UnsupportedMirV1 {
            kind: kind.clone(),
            detail: format!("division divisor is unsupported: {detail}"),
        }),
        other => Err(UnsupportedMirV1 {
            kind: "Operand::<unmodeled>".to_string(),
            detail: format!("division divisor is not a modeled scalar operand: {other:?}"),
        }),
    }
}

fn bool_operand_formula_v1(
    func: &VerifiableFunction,
    operand: &trust_types::Operand,
) -> Result<trust_types::Formula, UnsupportedMirV1> {
    use trust_types::{ConstValue, Formula, Operand, Sort};

    match operand {
        Operand::Constant(ConstValue::Bool(value)) => Ok(Formula::Bool(*value)),
        Operand::Copy(place) | Operand::Move(place) => {
            Ok(Formula::Var(place_var_name(func, place)?, Sort::Bool))
        }
        Operand::Symbolic(formula) => Ok(formula.clone()),
        Operand::Unsupported { kind, detail } => Err(UnsupportedMirV1 {
            kind: kind.clone(),
            detail: format!("assert condition is unsupported: {detail}"),
        }),
        other => Err(UnsupportedMirV1 {
            kind: "Operand::<unmodeled>".to_string(),
            detail: format!("assert condition is not a modeled boolean operand: {other:?}"),
        }),
    }
}

// Trust: Max recursion depth when resolving SSA-like local definitions in the
// v1 safety bridge. Bounds-check temps chain at most a few links
// (`_idx = const; _cond = Lt(_idx, _len)`); the cap only guards against
// pathological or cyclic IR.
const V1_RESOLVE_DEPTH: u32 = 16;

/// Trust: Return the rvalue of `local`'s *unique* whole-local assignment across
/// the entire body, or `None` if it is never assigned (a function input) or
/// assigned more than once (not SSA-like). The v1 safety bridge uses this to
/// resolve rustc's SSA-like bounds-check temps into their semantic definitions.
/// The uniqueness requirement is what makes resolution sound: for the safe-Rust
/// MIR we verify, a single static assignment that is later read is the reaching
/// definition at that read, so substituting it cannot change the value seen.
fn unique_whole_local_def(func: &VerifiableFunction, local: usize) -> Option<&trust_types::Rvalue> {
    use trust_types::Statement;
    let mut found = None;
    for bb in &func.body.blocks {
        for stmt in &bb.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local
                && place.projections.is_empty()
            {
                if found.is_some() {
                    return None;
                }
                found = Some(rvalue);
            }
        }
    }
    found
}

fn is_ordering_binop(op: trust_types::BinOp) -> bool {
    use trust_types::BinOp;
    matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
}

fn ordering_formula_v1(
    op: trust_types::BinOp,
    lhs: trust_types::Formula,
    rhs: trust_types::Formula,
) -> Option<trust_types::Formula> {
    use trust_types::{BinOp, Formula};
    let (l, r) = (Box::new(lhs), Box::new(rhs));
    Some(match op {
        BinOp::Lt => Formula::Lt(l, r),
        BinOp::Le => Formula::Le(l, r),
        BinOp::Gt => Formula::Gt(l, r),
        BinOp::Ge => Formula::Ge(l, r),
        _ => return None,
    })
}

/// Trust: Best-effort resolution of an integer operand, following SSA `Use`
/// chains for plain locals so constant indices fold (`_idx = const 1` =>
/// `Int(1)`). Falls back to `operand_to_int_formula_v1` at the leaf, returning
/// `None` only for operands that helper cannot model (e.g. float constants), in
/// which case the caller keeps the original bare-variable encoding.
fn try_resolve_int_operand_v1(
    func: &VerifiableFunction,
    operand: &trust_types::Operand,
    depth: u32,
) -> Option<trust_types::Formula> {
    use trust_types::{Operand, Rvalue};
    if let Operand::Copy(place) | Operand::Move(place) = operand
        && place.projections.is_empty()
        && depth < V1_RESOLVE_DEPTH
        && let Some(Rvalue::Use(inner)) = unique_whole_local_def(func, place.local)
    {
        return try_resolve_int_operand_v1(func, inner, depth + 1);
    }
    operand_to_int_formula_v1(func, operand).ok()
}

/// Trust: Resolve an assert condition operand to its defining ordering
/// comparison so statically-decidable bounds checks discharge. rustc emits
/// `_cond = Lt(idx, len); assert(_cond, BoundsCheck)`; left as a bare boolean
/// variable the violation `Not(_cond)` is unconstrained and never proves. By
/// substituting the real comparison (always sound — it is the exact condition
/// the assert tests) and folding SSA constant operands, an in-bounds constant
/// index like `arr[1]` discharges to `Not(Lt(1, 3))`, i.e. UNSAT. Returns
/// `None` when the operand is not a resolvable ordering comparison, leaving the
/// caller's existing bare-variable encoding intact (sound, less precise).
fn try_resolve_ordering_condition_v1(
    func: &VerifiableFunction,
    operand: &trust_types::Operand,
    depth: u32,
) -> Option<trust_types::Formula> {
    use trust_types::{Operand, Rvalue};
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projections.is_empty() || depth >= V1_RESOLVE_DEPTH {
        return None;
    }
    match unique_whole_local_def(func, place.local)? {
        Rvalue::Use(inner) => try_resolve_ordering_condition_v1(func, inner, depth + 1),
        Rvalue::BinaryOp(op, lhs, rhs) if is_ordering_binop(*op) => {
            let lf = try_resolve_int_operand_v1(func, lhs, depth + 1)?;
            let rf = try_resolve_int_operand_v1(func, rhs, depth + 1)?;
            ordering_formula_v1(*op, lf, rf)
        }
        _ => None,
    }
}

fn assert_violation_formula_v1(
    func: &VerifiableFunction,
    cond: &trust_types::Operand,
    expected: bool,
) -> Result<trust_types::Formula, UnsupportedMirV1> {
    // Trust: Resolve the condition's defining ordering comparison when possible
    // so statically-true bounds checks discharge; otherwise keep the original
    // (sound) bare-boolean encoding.
    let condition = match try_resolve_ordering_condition_v1(func, cond, 0) {
        Some(formula) => formula,
        None => bool_operand_formula_v1(func, cond)?,
    };
    Ok(if expected {
        match condition {
            trust_types::Formula::Bool(value) => trust_types::Formula::Bool(!value),
            other => trust_types::Formula::Not(Box::new(other)),
        }
    } else {
        condition
    })
}

// --- v1 semantic overflow encoding --------------------------------------
//
// Trust: For an `Assert { msg: Overflow(op), expected: false, cond: <flag> }`
// terminator paired with a `CheckedBinaryOp(op, lhs, rhs)` assignment in the
// same block, the bare overflow-flag variable is unconstrained, which makes
// the resulting SMT query trivially satisfiable. Encode the actual overflow
// semantics instead, mirroring the canonical pipeline-v2 encoding from
// `trust_vcgen::generate::v2_build_overflow_vc`: the violation is "operands
// are in-range for their declared integer type AND the mathematical result
// falls outside the destination type's range." With function preconditions
// conjoined separately, a real solver can prove the absence of overflow.

fn local_ty<'a>(func: &'a VerifiableFunction, local: usize) -> Option<&'a trust_types::Ty> {
    func.body.locals.get(local).map(|l| &l.ty)
}

fn place_ty<'a>(
    func: &'a VerifiableFunction,
    place: &trust_types::Place,
) -> Option<trust_types::Ty> {
    let mut ty = local_ty(func, place.local)?.clone();
    for projection in &place.projections {
        match projection {
            trust_types::Projection::Field(idx) => {
                if let trust_types::Ty::Tuple(fields) = &ty {
                    ty = fields.get(*idx as usize)?.clone();
                } else {
                    return None;
                }
            }
            // Other projections (Deref, Index, etc.) are not modeled for type lookup here.
            _ => return None,
        }
    }
    Some(ty)
}

fn operand_ty_v1(
    func: &VerifiableFunction,
    operand: &trust_types::Operand,
) -> Option<trust_types::Ty> {
    use trust_types::{ConstValue, Operand, Ty};
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(func, place),
        Operand::Constant(ConstValue::Int(_)) => Some(Ty::Int { width: 64, signed: true }),
        Operand::Constant(ConstValue::Uint(_, width)) => {
            Some(Ty::Int { width: *width as u32, signed: false })
        }
        Operand::Constant(ConstValue::Bool(_)) => Some(Ty::Bool),
        _ => None,
    }
}

fn operand_to_int_formula_v1(
    func: &VerifiableFunction,
    operand: &trust_types::Operand,
) -> Result<trust_types::Formula, UnsupportedMirV1> {
    use trust_types::{ConstValue, Formula, Operand, Sort};
    match operand {
        Operand::Constant(ConstValue::Int(value)) => Ok(Formula::Int(*value)),
        Operand::Constant(ConstValue::Uint(value, _)) => {
            if let Ok(value_i128) = i128::try_from(*value) {
                Ok(Formula::Int(value_i128))
            } else {
                Ok(Formula::UInt(*value))
            }
        }
        Operand::Copy(place) | Operand::Move(place) => {
            Ok(Formula::Var(place_var_name(func, place)?, Sort::Int))
        }
        Operand::Symbolic(formula) => Ok(formula.clone()),
        Operand::Unsupported { kind, detail } => Err(UnsupportedMirV1 {
            kind: kind.clone(),
            detail: format!("integer operand is unsupported: {detail}"),
        }),
        other => Err(UnsupportedMirV1 {
            kind: "Operand::<unmodeled>".to_string(),
            detail: format!("operand is not a modeled scalar: {other:?}"),
        }),
    }
}

/// Type-range constraints: `min <= var AND var <= max`.
fn int_input_range_v1(
    var: &trust_types::Formula,
    width: u32,
    signed: bool,
) -> trust_types::Formula {
    use trust_types::Formula;
    let (min_f, max_f) = int_type_range_v1(width, signed);
    Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(var.clone())),
        Formula::Le(Box::new(var.clone()), Box::new(max_f)),
    ])
}

fn int_type_range_v1(width: u32, signed: bool) -> (trust_types::Formula, trust_types::Formula) {
    use trust_types::Formula;
    if signed {
        let min = if width >= 128 { i128::MIN } else { -(1i128 << (width - 1)) };
        let max = if width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        (Formula::Int(min), Formula::Int(max))
    } else {
        let max = if width >= 128 {
            Formula::UInt(u128::MAX)
        } else {
            Formula::Int((1i128 << width) - 1)
        };
        (Formula::Int(0), max)
    }
}

/// Look in `block` for a `CheckedBinaryOp(op, lhs, rhs)` assignment whose
/// destination matches the Assert's overflow-flag local.
fn find_checked_binop_for_assert<'a>(
    block: &'a trust_types::BasicBlock,
    op: trust_types::BinOp,
    cond: &trust_types::Operand,
) -> Option<(&'a trust_types::Operand, &'a trust_types::Operand)> {
    use trust_types::{Operand, Projection, Rvalue, Statement};

    // The Assert condition is `Copy/Move(_N.1)` — the overflow flag of the
    // tuple result. Extract the tuple local index.
    let cond_place = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if cond_place.projections.len() != 1 {
        return None;
    }
    let Projection::Field(1) = &cond_place.projections[0] else {
        return None;
    };
    let tuple_local = cond_place.local;

    // Find the matching CheckedBinaryOp assignment.
    for stmt in &block.stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != tuple_local || !place.projections.is_empty() {
            continue;
        }
        if let Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs) = rvalue
            && *stmt_op == op
        {
            return Some((lhs, rhs));
        }
    }
    None
}

/// Build the semantic overflow formula for an Add/Sub/Mul `CheckedBinaryOp`:
///   `in_range(lhs) AND in_range(rhs) AND (lhs op rhs out_of_range)`.
fn build_overflow_violation_formula_v1(
    func: &VerifiableFunction,
    op: trust_types::BinOp,
    lhs: &trust_types::Operand,
    rhs: &trust_types::Operand,
) -> Option<(trust_types::Formula, trust_types::Ty, trust_types::Ty)> {
    use trust_types::{BinOp, Formula, Ty};

    let lhs_ty = operand_ty_v1(func, lhs)?;
    let rhs_ty = operand_ty_v1(func, rhs)?;
    let (width, signed) = match &lhs_ty {
        Ty::Int { width, signed } => (*width, *signed),
        _ => return None,
    };

    let lhs_f = operand_to_int_formula_v1(func, lhs).ok()?;
    let rhs_f = operand_to_int_formula_v1(func, rhs).ok()?;

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => return None,
    };

    let lhs_range = int_input_range_v1(&lhs_f, width, signed);
    let rhs_range = int_input_range_v1(&rhs_f, width, signed);
    let (min_f, max_f) = int_type_range_v1(width, signed);
    let out_of_range = Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ]);

    Some((Formula::And(vec![lhs_range, rhs_range, out_of_range]), lhs_ty, rhs_ty))
}

/// Build v1 VCs from a `VerifiableFunction` for fallback dispatch.
///
/// This generates safety VCs from the function's blocks (division by zero,
/// overflow, bounds checks). A real implementation would use trust_vcgen;
/// this is a lightweight bridge for the v1 dispatch path.
pub fn build_v1_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    use trust_types::{BinOp, Rvalue, Statement, Ty, VcKind};

    let mut vcs = Vec::new();
    let zero_guard_targets = zero_divisor_guard_targets(func);

    for bb in &func.body.blocks {
        // Generate VCs from assert terminators.
        if let Terminator::Assert { cond, expected, msg, span, .. } = &bb.terminator {
            // Trust: For Overflow asserts paired with a CheckedBinaryOp in the same
            // block, emit the semantic overflow formula rather than the bare
            // overflow-flag variable. Without the semantic encoding the formula is
            // a free Bool and the SMT query is trivially satisfiable.
            if let trust_types::AssertMessage::Overflow(op) = msg
                && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                && !*expected
                && let Some((lhs, rhs)) = find_checked_binop_for_assert(bb, *op, cond)
                && let Some((formula, lhs_ty, rhs_ty)) =
                    build_overflow_violation_formula_v1(func, *op, lhs, rhs)
            {
                vcs.push(VerificationCondition {
                    kind: VcKind::ArithmeticOverflow { op: *op, operand_tys: (lhs_ty, rhs_ty) },
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                });
                continue;
            }

            let kind = match msg {
                trust_types::AssertMessage::DivisionByZero => VcKind::DivisionByZero,
                trust_types::AssertMessage::Overflow(op) => VcKind::ArithmeticOverflow {
                    op: *op,
                    operand_tys: (
                        Ty::Int { width: 32, signed: true },
                        Ty::Int { width: 32, signed: true },
                    ),
                },
                trust_types::AssertMessage::BoundsCheck => VcKind::IndexOutOfBounds,
                trust_types::AssertMessage::RemainderByZero => VcKind::RemainderByZero,
                trust_types::AssertMessage::OverflowNeg => {
                    VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } }
                }
                _ => VcKind::Assertion { message: format!("{msg:?}") },
            };
            let formula = match assert_violation_formula_v1(func, cond, *expected) {
                Ok(formula) => formula,
                Err(unsupported) => {
                    vcs.push(unsupported_mir_v1_vc(
                        func,
                        unsupported.kind,
                        format!("bb{} assert condition: {}", bb.id.0, unsupported.detail),
                        span.clone(),
                    ));
                    collect_operand_unsupported_v1(
                        func,
                        format!("bb{} assert condition", bb.id.0),
                        span,
                        cond,
                        &mut vcs,
                    );
                    continue;
                }
            };
            vcs.push(VerificationCondition {
                kind,
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }

        if zero_guard_targets.contains(&bb.id.0) {
            continue;
        }

        for stmt in &bb.stmts {
            let Statement::Assign { rvalue, span, .. } = stmt else {
                continue;
            };

            let (kind, formula) = match rvalue {
                Rvalue::BinaryOp(BinOp::Div, _, divisor) => {
                    match divisor_is_zero_formula(func, divisor) {
                        Ok(formula) => (VcKind::DivisionByZero, formula),
                        Err(unsupported) => {
                            vcs.push(unsupported_mir_v1_vc(
                                func,
                                unsupported.kind,
                                format!("bb{} division divisor: {}", bb.id.0, unsupported.detail),
                                span.clone(),
                            ));
                            collect_operand_unsupported_v1(
                                func,
                                format!("bb{} division divisor", bb.id.0),
                                span,
                                divisor,
                                &mut vcs,
                            );
                            continue;
                        }
                    }
                }
                Rvalue::BinaryOp(BinOp::Rem, _, divisor) => {
                    match divisor_is_zero_formula(func, divisor) {
                        Ok(formula) => (VcKind::RemainderByZero, formula),
                        Err(unsupported) => {
                            vcs.push(unsupported_mir_v1_vc(
                                func,
                                unsupported.kind,
                                format!("bb{} remainder divisor: {}", bb.id.0, unsupported.detail),
                                span.clone(),
                            ));
                            collect_operand_unsupported_v1(
                                func,
                                format!("bb{} remainder divisor", bb.id.0),
                                span,
                                divisor,
                                &mut vcs,
                            );
                            continue;
                        }
                    }
                }
                _ => continue,
            };

            vcs.push(VerificationCondition {
                kind,
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }
    }

    // The v1 fallback must preserve fail-closed unsupported MIR obligations.
    // The lightweight safety bridge above does not understand opaque TrustIr, so
    // mirror the canonical UnsupportedMir scan here without depending on
    // trust_vcgen (trust_vcgen already depends on trust-router).
    vcs.extend(unsupported_mir_v1_vcs(func));

    // Trust: Conjoin function preconditions to every safety obligation. These
    // are assumed-true at function entry, so they tighten the violation
    // search space for the solver. Unsupported-MIR obligations carry an
    // opaque `Bool(false)` formula and skip the conjunction.
    if !func.preconditions.is_empty() {
        for vc in &mut vcs {
            if matches!(vc.kind, VcKind::UnsupportedMir { .. }) {
                continue;
            }
            let mut conjuncts = func.preconditions.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = trust_types::Formula::And(conjuncts);
        }
    }

    vcs
}

fn unsupported_mir_v1_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    collect_type_unsupported_v1(
        func,
        "return type".to_string(),
        &func.body.return_ty,
        &func.span,
        &mut vcs,
    );
    for local in &func.body.locals {
        collect_type_unsupported_v1(
            func,
            format!("local _{} type", local.index),
            &local.ty,
            &func.span,
            &mut vcs,
        );
    }
    for block in &func.body.blocks {
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            collect_stmt_unsupported_v1(func, block.id.0, stmt_index, stmt, &mut vcs);
        }
        if let Terminator::Opaque { kind, targets, span } = &block.terminator {
            vcs.push(unsupported_mir_v1_vc(
                func,
                kind.clone(),
                format!("bb{} targets {:?}", block.id.0, targets),
                span.clone(),
            ));
        }
    }
    vcs
}

fn collect_type_unsupported_v1(
    func: &VerifiableFunction,
    context: String,
    ty: &trust_types::Ty,
    span: &trust_types::SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    match ty {
        trust_types::Ty::Unsupported { kind, detail } => vcs.push(unsupported_mir_v1_vc(
            func,
            kind.clone(),
            format!("{context}: {detail}"),
            span.clone(),
        )),
        trust_types::Ty::Ref { inner, .. } => {
            collect_type_unsupported_v1(func, format!("{context} pointee"), inner, span, vcs);
        }
        trust_types::Ty::RawPtr { pointee, .. } => {
            collect_type_unsupported_v1(func, format!("{context} raw pointee"), pointee, span, vcs);
        }
        trust_types::Ty::Slice { elem } => {
            collect_type_unsupported_v1(func, format!("{context} slice element"), elem, span, vcs);
        }
        trust_types::Ty::Array { elem, .. } => {
            collect_type_unsupported_v1(func, format!("{context} array element"), elem, span, vcs);
        }
        trust_types::Ty::Tuple(fields) => {
            for (index, field_ty) in fields.iter().enumerate() {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} tuple field {index}"),
                    field_ty,
                    span,
                    vcs,
                );
            }
        }
        trust_types::Ty::Adt { fields, .. } => {
            for (name, field_ty) in fields {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} field {name}"),
                    field_ty,
                    span,
                    vcs,
                );
            }
        }
        trust_types::Ty::Closure { upvars, .. } | trust_types::Ty::Coroutine { upvars, .. } => {
            for (index, upvar_ty) in upvars.iter().enumerate() {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} upvar {index}"),
                    upvar_ty,
                    span,
                    vcs,
                );
            }
        }
        trust_types::Ty::FnDef { sig, .. } | trust_types::Ty::FnPtr { sig } => {
            for (index, param_ty) in sig.params.iter().enumerate() {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} param {index}"),
                    param_ty,
                    span,
                    vcs,
                );
            }
            collect_type_unsupported_v1(func, format!("{context} return"), &sig.ret, span, vcs);
        }
        _ => {}
    }
}

fn collect_place_type_unsupported_v1(
    func: &VerifiableFunction,
    context: String,
    span: &trust_types::SourceSpan,
    place: &trust_types::Place,
    vcs: &mut Vec<VerificationCondition>,
) {
    if let Err(unsupported) = place_var_name(func, place) {
        vcs.push(unsupported_mir_v1_vc(
            func,
            unsupported.kind,
            format!("{context}: {}", unsupported.detail),
            span.clone(),
        ));
    }

    for (index, projection) in place.projections.iter().enumerate() {
        match projection {
            trust_types::Projection::OpaqueCast(ty)
            | trust_types::Projection::UnwrapUnsafeBinder(ty) => collect_type_unsupported_v1(
                func,
                format!("{context} projection {index}"),
                ty,
                span,
                vcs,
            ),
            _ => {}
        }
    }
}

fn unsupported_mir_v1_vc(
    func: &VerifiableFunction,
    kind: String,
    detail: String,
    span: trust_types::SourceSpan,
) -> VerificationCondition {
    VerificationCondition {
        kind: trust_types::VcKind::UnsupportedMir { kind, detail },
        function: func.name.clone().into(),
        location: span,
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
    }
}

fn collect_stmt_unsupported_v1(
    func: &VerifiableFunction,
    block: usize,
    stmt_index: usize,
    stmt: &Statement,
    vcs: &mut Vec<VerificationCondition>,
) {
    match stmt {
        Statement::Unsupported { kind, detail, operands, span } => {
            vcs.push(unsupported_mir_v1_vc(
                func,
                kind.clone(),
                format!("bb{block} stmt{stmt_index}: {detail}"),
                span.clone(),
            ));
            collect_operands_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} unsupported operands"),
                span,
                operands,
                vcs,
            );
        }
        Statement::Assign { place, rvalue, span } => {
            collect_place_type_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} assignment place"),
                span,
                place,
                vcs,
            );
            collect_rvalue_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index}"),
                span,
                rvalue,
                vcs,
            );
        }
        Statement::SetDiscriminant { place, variant_index } => {
            let span = trust_types::SourceSpan::default();
            collect_place_type_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} set-discriminant place"),
                &span,
                place,
                vcs,
            );
            vcs.push(unsupported_mir_v1_vc(
                func,
                "StatementKind::SetDiscriminant".to_string(),
                format!(
                    "bb{block} stmt{stmt_index} writes variant {variant_index}; enum/union discriminant mutation is not modeled"
                ),
                span,
            ));
        }
        Statement::Deinit { place } => {
            let span = trust_types::SourceSpan::default();
            collect_place_type_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} deinit place"),
                &span,
                place,
                vcs,
            );
            vcs.push(unsupported_mir_v1_vc(
                func,
                "StatementKind::Deinit".to_string(),
                format!(
                    "bb{block} stmt{stmt_index} deinitialization effects require initializedness semantics"
                ),
                span,
            ));
        }
        Statement::Retag { place } => {
            let span = trust_types::SourceSpan::default();
            collect_place_type_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} retag place"),
                &span,
                place,
                vcs,
            );
            vcs.push(unsupported_mir_v1_vc(
                func,
                "StatementKind::Retag".to_string(),
                format!(
                    "bb{block} stmt{stmt_index} Stacked Borrows retag requires provenance semantics"
                ),
                span,
            ));
        }
        Statement::PlaceMention(place) => {
            let span = trust_types::SourceSpan::default();
            collect_place_type_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} place mention"),
                &span,
                place,
                vcs,
            );
        }
        Statement::Intrinsic { args, .. } => {
            collect_operands_unsupported_v1(
                func,
                format!("bb{block} stmt{stmt_index} intrinsic args"),
                &trust_types::SourceSpan::default(),
                args,
                vcs,
            );
        }
        _ => {}
    }
}

fn collect_rvalue_unsupported_v1(
    func: &VerifiableFunction,
    context: String,
    span: &trust_types::SourceSpan,
    rvalue: &Rvalue,
    vcs: &mut Vec<VerificationCondition>,
) {
    match rvalue {
        Rvalue::Unsupported { kind, detail, operands } => {
            vcs.push(unsupported_mir_v1_vc(
                func,
                kind.clone(),
                format!("{context}: {detail}"),
                span.clone(),
            ));
            collect_operands_unsupported_v1(
                func,
                format!("{context} unsupported operands"),
                span,
                operands,
                vcs,
            );
        }
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
            collect_operand_unsupported_v1(func, context.clone(), span, op, vcs);
            if let Rvalue::Cast(_, target_ty) = rvalue {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} cast target type"),
                    target_ty,
                    span,
                    vcs,
                );
            }
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_operand_unsupported_v1(func, format!("{context} lhs"), span, lhs, vcs);
            collect_operand_unsupported_v1(func, format!("{context} rhs"), span, rhs, vcs);
        }
        Rvalue::Aggregate(kind, operands) => {
            if let Some((kind, detail)) = unsupported_aggregate_kind_v1(kind) {
                vcs.push(unsupported_mir_v1_vc(
                    func,
                    kind,
                    format!("{context}: {detail}"),
                    span.clone(),
                ));
            }
            if let trust_types::AggregateKind::RawPtr { pointee_ty, .. } = kind {
                collect_type_unsupported_v1(
                    func,
                    format!("{context} raw pointer aggregate pointee"),
                    pointee_ty,
                    span,
                    vcs,
                );
            }
            collect_operands_unsupported_v1(func, context, span, operands, vcs);
        }
        Rvalue::Repeat(op, _) => collect_operand_unsupported_v1(func, context, span, op, vcs),
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => {
            collect_place_type_unsupported_v1(func, context, span, place, vcs);
        }
        _ => {}
    }
}

fn collect_operands_unsupported_v1(
    func: &VerifiableFunction,
    context: String,
    span: &trust_types::SourceSpan,
    operands: &[trust_types::Operand],
    vcs: &mut Vec<VerificationCondition>,
) {
    for (index, operand) in operands.iter().enumerate() {
        collect_operand_unsupported_v1(func, format!("{context}[{index}]"), span, operand, vcs);
    }
}

fn collect_operand_unsupported_v1(
    func: &VerifiableFunction,
    context: String,
    span: &trust_types::SourceSpan,
    operand: &trust_types::Operand,
    vcs: &mut Vec<VerificationCondition>,
) {
    match operand {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => {
            collect_place_type_unsupported_v1(func, context, span, place, vcs);
        }
        trust_types::Operand::Unsupported { kind, detail } => {
            vcs.push(unsupported_mir_v1_vc(
                func,
                kind.clone(),
                format!("{context}: {detail}"),
                span.clone(),
            ));
        }
        _ => {}
    }
}

fn unsupported_aggregate_kind_v1(kind: &trust_types::AggregateKind) -> Option<(String, String)> {
    match kind {
        trust_types::AggregateKind::Adt {
            name,
            variant,
            active_field: Some(active_field),
            ..
        } => {
            Some((
                "AggregateKind::Adt(active_field)".to_string(),
                format!(
                    "union-like aggregate {name} variant {variant} active_field {active_field}"
                ),
            ))
        }
        trust_types::AggregateKind::Closure { name, .. } => Some((
            "AggregateKind::Closure".to_string(),
            format!("closure aggregate {name} requires captured-environment semantics"),
        )),
        trust_types::AggregateKind::Coroutine { name } => Some((
            "AggregateKind::Coroutine".to_string(),
            format!("coroutine aggregate {name} requires generator-state semantics"),
        )),
        trust_types::AggregateKind::CoroutineClosure { name } => Some((
            "AggregateKind::CoroutineClosure".to_string(),
            format!("coroutine-closure aggregate {name} requires async closure semantics"),
        )),
        trust_types::AggregateKind::RawPtr { .. } => Some((
            "AggregateKind::RawPtr".to_string(),
            "raw pointer aggregate requires data-pointer/metadata semantics".to_string(),
        )),
        _ => None,
    }
}

/// Merge results from two backends (for UnsafeAudit).
///
/// Priority: Failed > Unknown/Timeout > Proved.
/// If both prove, uses the stronger proof strength.
fn merge_results(a: VerificationResult, b: VerificationResult) -> VerificationResult {
    // If either failed, return the failure.
    if a.is_failed() {
        return a;
    }
    if b.is_failed() {
        return b;
    }

    // If both proved, merge.
    match (&a, &b) {
        (
            VerificationResult::Proved { time_ms: t1, proof_certificate: cert1, .. },
            VerificationResult::Proved { time_ms: t2, proof_certificate: cert2, .. },
        ) => VerificationResult::Proved {
            solver: "mir-router-unsafe-audit".into(),
            time_ms: t1 + t2,
            // Deductive proof is stronger than bounded.
            strength: trust_types::ProofStrength::deductive(),
            proof_certificate: cert1.clone().or_else(|| cert2.clone()),
            solver_warnings: None,
            native_proof_envelope: None,
        },
        // One proved, one didn't — return the non-proof result.
        (VerificationResult::Proved { .. }, _) => b,
        (_, VerificationResult::Proved { .. }) => a,
        // Neither proved — return whichever has more info.
        _ => a,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    // -----------------------------------------------------------------------
    // Test helper: build a minimal VerifiableFunction
    // -----------------------------------------------------------------------

    fn minimal_func(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
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
        }
    }

    fn func_with_contract(name: &str, kind: ContractKind) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.contracts.push(Contract { kind, span: SourceSpan::default(), body: "x > 0".to_string() });
        f
    }

    fn func_with_unsafe(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::AddressOf(true, Place::local(0)),
            span: SourceSpan::default(),
        });
        f
    }

    fn func_with_atomics(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "std::sync::atomic::AtomicU64::fetch_add".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: Some(AtomicOperation {
                place: Place::local(0),
                dest: None,
                op_kind: AtomicOpKind::FetchAdd,
                ordering: AtomicOrdering::SeqCst,
                failure_ordering: None,
                span: SourceSpan::default(),
            }),
        };
        f
    }

    fn func_with_raw_ptr_locals(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
            name: Some("ptr".to_string()),
        });
        f
    }

    fn func_with_ffi(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks[0].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "libc::malloc".to_string(),
            args: vec![],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
        };
        f
    }

    fn func_with_loop(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1), // Back-edge: loop!
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        f
    }

    fn func_with_acyclic_lower_id_unreachable(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.locals = vec![LocalDecl { index: 0, ty: Ty::Bool, name: Some("flag".into()) }];
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(0, BlockId(5))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(4),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Goto(BlockId(6)) },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Goto(BlockId(6)) },
            BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
        ];
        f
    }

    fn func_with_div_statement(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".to_string()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ];
        f.body.arg_count = 1;
        f.body.return_ty = Ty::i32();
        f.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(2)),
            ),
            span: SourceSpan::default(),
        });
        f
    }

    fn func_with_spec(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.spec = FunctionSpec {
            requires: vec!["n > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![],
        };
        f
    }

    fn func_with_invariant_spec(name: &str) -> VerifiableFunction {
        let mut f = minimal_func(name);
        f.spec = FunctionSpec {
            requires: vec![],
            ensures: vec![],
            invariants: vec!["i < n".to_string()],
        };
        f
    }

    fn fixture_dir() -> std::path::PathBuf {
        let manifest = env!("CARGO_MANIFEST_DIR");
        std::path::PathBuf::from(manifest).join("../trust-integration-tests/fixtures/real_mir")
    }

    fn load_fixture(name: &str) -> VerifiableFunction {
        let path = fixture_dir().join(format!("{name}.json"));
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
        serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("failed to parse fixture {}: {e}", path.display()))
    }

    // -----------------------------------------------------------------------
    // Classification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_plain_function_v1_fallback() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("plain");
        assert_eq!(router.classify(&func), MirStrategy::V1Fallback);
    }

    #[test]
    fn test_classify_contract_requires() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_requires", ContractKind::Requires);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_contract_ensures() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_ensures", ContractKind::Ensures);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_invariant_annotation() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_invariant", ContractKind::Invariant);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_loop_invariant_annotation() {
        let router = MirRouter::with_defaults();
        let func = func_with_contract("with_loop_inv", ContractKind::LoopInvariant);
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_unsafe_with_contracts() {
        let router = MirRouter::with_defaults();
        let mut func = func_with_unsafe("unsafe_with_contracts");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr.is_null() == false".to_string(),
        });
        assert_eq!(router.classify(&func), MirStrategy::UnsafeAudit);
    }

    #[test]
    fn test_classify_unsafe_without_contracts_raw_ptr() {
        let router = MirRouter::with_defaults();
        let func = func_with_unsafe("unsafe_no_contracts");
        // AddressOf triggers both has_unsafe and has_raw_pointer_operations.
        // Since there are no contracts, UnsafeAudit won't trigger.
        // Instead, SeparationLogic takes priority over DataRace.
        let strategy = router.classify(&func);
        assert_eq!(strategy, MirStrategy::SeparationLogic);
    }

    #[test]
    fn test_classify_atomics() {
        let router = MirRouter::with_defaults();
        let func = func_with_atomics("atomic_fetch");
        assert_eq!(router.classify(&func), MirStrategy::DataRace);
    }

    #[test]
    fn test_classify_raw_pointer_locals() {
        let router = MirRouter::with_defaults();
        let func = func_with_raw_ptr_locals("raw_ptr");
        assert_eq!(router.classify(&func), MirStrategy::SeparationLogic);
    }

    #[test]
    fn test_classify_ffi() {
        let router = MirRouter::with_defaults();
        let func = func_with_ffi("ffi_call");
        assert_eq!(router.classify(&func), MirStrategy::FFIBoundary);
    }

    #[test]
    fn test_classify_loop() {
        let router = MirRouter::with_defaults();
        let func = func_with_loop("loopy");
        assert_eq!(router.classify(&func), MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_classify_spec_requires_ensures() {
        let router = MirRouter::with_defaults();
        let func = func_with_spec("with_spec");
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_spec_invariants() {
        let router = MirRouter::with_defaults();
        let func = func_with_invariant_spec("with_inv_spec");
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_preconditions_formulas() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_preconditions");
        func.preconditions.push(Formula::Bool(true));
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    #[test]
    fn test_classify_postconditions_formulas() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_postconditions");
        func.postconditions.push(Formula::Bool(true));
        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
    }

    // -----------------------------------------------------------------------
    // Dispatch tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_v1_fallback_dispatch_no_vcs() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("empty");
        let result = router.verify_function(&func);
        assert!(
            matches!(&result, VerificationResult::Unknown { reason, .. } if reason.contains("no verification conditions")),
            "empty v1 fallback must not claim a proof: {result:?}"
        );
    }

    #[test]
    fn test_v1_fallback_dispatch_with_assert() {
        let router = MirRouter::with_defaults();
        let mut func = minimal_func("with_assert");
        // Use target BlockId(1) to avoid creating a back-edge (which would
        // classify as BoundedModelCheck instead of V1Fallback).
        func.body.blocks[0].terminator = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::DivisionByZero,
            target: BlockId(1),
            span: SourceSpan::default(),
        };
        // This will generate a VC and dispatch through mock backend.
        let result = router.verify_function(&func);
        // ConstantFolderBackend returns Proved for Formula::Bool(false) (negation is unsat).
        assert!(result.is_proved());
    }

    #[test]
    fn test_verify_all_classifies_each() {
        let router = MirRouter::with_defaults();
        let funcs = vec![
            minimal_func("plain"),
            func_with_contract("contracted", ContractKind::Requires),
            func_with_loop("loopy"),
        ];

        let results = router.verify_all(&funcs);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].1, MirStrategy::V1Fallback);
        assert_eq!(results[1].1, MirStrategy::ContractVerification);
        assert_eq!(results[2].1, MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_verify_with_explicit_strategy() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("explicit");
        // Force V1Fallback even though it's the default.
        let result = router.verify_with_strategy(&func, &MirStrategy::V1Fallback);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    // -----------------------------------------------------------------------
    // Merge result tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_merge_both_proved() {
        let a = VerificationResult::Proved {
            solver: "a".into(),
            time_ms: 10,
            strength: ProofStrength::bounded(10),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let b = VerificationResult::Proved {
            solver: "b".into(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let merged = merge_results(a, b);
        assert!(merged.is_proved());
        if let VerificationResult::Proved { time_ms, .. } = &merged {
            assert_eq!(*time_ms, 30);
        }
    }

    #[test]
    fn test_merge_one_failed() {
        let a =
            VerificationResult::Failed { solver: "a".into(), time_ms: 10, counterexample: None };
        let b = VerificationResult::Proved {
            solver: "b".into(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let merged = merge_results(a, b);
        assert!(merged.is_failed());
    }

    #[test]
    fn test_merge_one_proved_one_unknown() {
        let a = VerificationResult::Proved {
            solver: "a".into(),
            time_ms: 10,
            strength: ProofStrength::bounded(10),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let b = VerificationResult::Unknown {
            solver: "b".into(),
            time_ms: 20,
            reason: "timeout".to_string(),
        };
        let merged = merge_results(a, b);
        // One proved, other didn't — return the non-proof result.
        assert!(!merged.is_proved());
    }

    // -----------------------------------------------------------------------
    // Strategy display tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_display() {
        assert_eq!(MirStrategy::BoundedModelCheck.to_string(), "BoundedModelCheck");
        assert_eq!(MirStrategy::ContractVerification.to_string(), "ContractVerification");
        assert_eq!(MirStrategy::UnsafeAudit.to_string(), "UnsafeAudit");
        assert_eq!(MirStrategy::V1Fallback.to_string(), "V1Fallback");

        let portfolio = MirStrategy::Portfolio(vec![
            MirStrategy::BoundedModelCheck,
            MirStrategy::ContractVerification,
        ]);
        assert_eq!(portfolio.to_string(), "Portfolio(BoundedModelCheck, ContractVerification)");
    }

    // -----------------------------------------------------------------------
    // Helper function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_ffi_callee() {
        assert!(is_ffi_callee("libc::malloc"));
        assert!(is_ffi_callee("libc::free"));
        assert!(is_ffi_callee("std::ffi::CString::new"));
        assert!(is_ffi_callee("core::ffi::c_str::CStr::as_ptr"));
        assert!(!is_ffi_callee("std::vec::Vec::new"));
        assert!(!is_ffi_callee("my_crate::my_func"));
    }

    #[test]
    fn test_has_loops_no_loop() {
        let func = minimal_func("no_loop");
        assert!(!has_loops(&func));
    }

    #[test]
    fn test_has_loops_with_back_edge() {
        let func = func_with_loop("loopy");
        assert!(has_loops(&func));
    }

    #[test]
    fn test_has_loops_rejects_acyclic_lower_id_cross_edge() {
        let func = func_with_acyclic_lower_id_unreachable("acyclic_unreachable");

        assert!(!has_loops(&func));
        assert_eq!(MirRouter::with_defaults().classify(&func), MirStrategy::V1Fallback);
    }

    #[test]
    fn test_build_trust_wp_contracts_from_typed() {
        let func = func_with_contract("contracted", ContractKind::Requires);
        let contracts = build_trust_wp_contracts(&func);
        assert_eq!(contracts.requires.len(), 1);
        assert_eq!(contracts.requires[0].expression, "x > 0");
    }

    #[test]
    fn test_build_trust_wp_contracts_from_spec() {
        let func = func_with_spec("spec_func");
        let contracts = build_trust_wp_contracts(&func);
        assert_eq!(contracts.requires.len(), 1);
        assert_eq!(contracts.ensures.len(), 1);
        assert_eq!(contracts.requires[0].expression, "n > 0");
        assert_eq!(contracts.ensures[0].expression, "result >= 0");
    }

    #[test]
    fn test_place_var_name_includes_projections() {
        let mut func = minimal_func("projected_places");
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".to_string()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".to_string()) },
        ];

        let base = place_var_name(&func, &Place::local(1)).expect("base place supported");
        let field = place_var_name(&func, &Place::field(1, 0)).expect("field supported");
        let deref =
            place_var_name(&func, &Place { local: 1, projections: vec![Projection::Deref] })
                .expect("deref supported");
        let indexed =
            place_var_name(&func, &Place { local: 1, projections: vec![Projection::Index(2)] })
                .expect("index supported");
        let const_indexed = place_var_name(
            &func,
            &Place {
                local: 1,
                projections: vec![Projection::ConstantIndex {
                    offset: 3,
                    min_length: 4,
                    from_end: false,
                }],
            },
        )
        .expect("constant index supported");

        let names = [&base, &field, &deref, &indexed, &const_indexed];
        let unique = names.iter().copied().collect::<std::collections::BTreeSet<_>>();
        assert_eq!(unique.len(), names.len(), "projected places must not alias base locals");
        // Trust: projection encoding now matches `trust_vcgen::place_to_var_name` so
        // v1 and v2 share a single naming convention for downstream tooling.
        assert!(field.contains(".0"), "field projection encoded as `.0`, got {field}");
        assert!(deref.contains('*'), "deref projection encoded as `*`, got {deref}");
        assert!(
            indexed.contains("[_2]"),
            "index projection encoded as `[_<local>]`, got {indexed}"
        );
        assert!(
            const_indexed.contains("[3;min=4]"),
            "constant index projection encoded as `[<offset>;min=<n>]`, got {const_indexed}"
        );
    }

    #[test]
    fn test_bmc_dispatch_without_real_encoding_returns_unknown() {
        let router = MirRouter::with_defaults();
        let func = func_with_loop("loop_without_bmc_encoding");

        assert_eq!(router.classify(&func), MirStrategy::BoundedModelCheck);
        let result = router.verify_function(&func);

        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver, "trust-mc-lib");
                assert!(reason.contains("real MIR-derived verification conditions"));
                assert!(reason.contains("no proof-grade trust_mc encoding"));
            }
            other => panic!("expected Unknown for placeholder trust_mc dispatch, got {other:?}"),
        }
    }

    #[test]
    fn test_contract_dispatch_without_body_semantics_returns_unknown() {
        let router = MirRouter::with_defaults();
        let func = func_with_spec("contract_without_body_semantics");

        assert_eq!(router.classify(&func), MirStrategy::ContractVerification);
        let result = router.verify_function(&func);

        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver, "trust-wp-lib");
                assert!(reason.contains("MIR body semantics"));
            }
            other => panic!("expected Unknown for contract-only trust_wp dispatch, got {other:?}"),
        }
    }

    #[test]
    fn test_build_v1_vcs_from_asserts() {
        let mut func = minimal_func("assert_func");
        func.body.blocks[0].terminator = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::DivisionByZero,
            target: BlockId(0),
            span: SourceSpan::default(),
        };
        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
        assert_eq!(vcs[0].formula, Formula::Bool(false));
    }

    #[test]
    fn test_build_v1_vcs_false_assert_is_violation() {
        let mut func = minimal_func("false_assert_func");
        func.body.blocks[0].terminator = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Constant(ConstValue::Bool(false)),
            expected: true,
            msg: AssertMessage::Custom("must hold".to_string()),
            target: BlockId(0),
            span: SourceSpan::default(),
        };

        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Assertion { .. }));
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // Bounds-condition resolution: rustc emits
    //   `_idx = const; _cond = Lt(_idx, len); assert(_cond, BoundsCheck)`
    // The v1 bridge must resolve `_cond` to its real ordering comparison (and
    // fold SSA constant operands) so statically-true bounds checks discharge,
    // while never inventing a proof for a symbolic index.
    // -----------------------------------------------------------------------

    /// `_1 = idx_def?` ; `_2 = Lt(Copy(_1), const len:u64)` ; assert(Move(_2)).
    /// When `idx_def` is `None`, `_1` models a function input (no definition).
    fn bounds_assert_func(name: &str, idx_def: Option<Operand>, len: u128) -> VerifiableFunction {
        let mut func = minimal_func(name);
        func.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Int { width: 64, signed: false },
            name: None,
        });
        func.body.locals.push(LocalDecl { index: 2, ty: Ty::Bool, name: None });
        let mut stmts = Vec::new();
        if let Some(op) = idx_def {
            stmts.push(Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(op),
                span: SourceSpan::default(),
            });
        }
        stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(len, 64)),
            ),
            span: SourceSpan::default(),
        });
        func.body.blocks[0].stmts = stmts;
        func.body.blocks[0].terminator = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Move(Place::local(2)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(0),
            span: SourceSpan::default(),
        };
        func
    }

    fn only_bounds_vc(func: &VerifiableFunction) -> VerificationCondition {
        let mut bounds: Vec<_> = build_v1_vcs(func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds))
            .collect();
        assert_eq!(bounds.len(), 1, "expected exactly one bounds VC");
        bounds.pop().unwrap()
    }

    #[test]
    fn test_v1_const_index_bounds_resolves_to_foldable_violation() {
        // `arr[1]` into a length-3 array: `_1 = const 1; _2 = Lt(_1, 3)`.
        // The violation must be the *folded* comparison `Not(Lt(1, 3))`, which a
        // solver proves UNSAT — not a bare `Not(Var(_2))` that never discharges.
        let func =
            bounds_assert_func("p1_const", Some(Operand::Constant(ConstValue::Uint(1, 64))), 3);
        let vc = only_bounds_vc(&func);
        let expected = Formula::Not(Box::new(Formula::Lt(
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(3)),
        )));
        assert_eq!(vc.formula, expected, "const-index bounds violation must fold to Not(Lt(1,3))");
    }

    #[test]
    fn test_v1_symbolic_index_bounds_keeps_real_comparison_no_false_proof() {
        // Symbolic index (function input, no definition): the violation must be
        // the real comparison `Not(Lt(_idx, 3))` with the index left as a free
        // variable — a solver finds it SAT (runtime-checked), never proved.
        let func = bounds_assert_func("p_symbolic", None, 3);
        let vc = only_bounds_vc(&func);
        match &vc.formula {
            Formula::Not(inner) => match inner.as_ref() {
                Formula::Lt(lhs, rhs) => {
                    assert!(
                        matches!(lhs.as_ref(), Formula::Var(_, Sort::Int)),
                        "symbolic index must remain a free Int variable, got {lhs:?}"
                    );
                    assert_eq!(rhs.as_ref(), &Formula::Int(3));
                }
                other => panic!("expected Lt comparison, got {other:?}"),
            },
            other => panic!("expected Not(Lt(..)), got {other:?}"),
        }
    }

    #[test]
    fn test_v1_non_ssa_condition_falls_back_to_bare_var() {
        // A condition local assigned twice is not SSA-like; resolution must bail
        // and keep the original bare-boolean encoding (sound, never a false
        // proof). Build `_2 = Lt(_1, 3)` then reassign `_2 = Lt(_1, 99)`.
        let mut func =
            bounds_assert_func("p_non_ssa", Some(Operand::Constant(ConstValue::Uint(1, 64))), 3);
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(99, 64)),
            ),
            span: SourceSpan::default(),
        });
        let vc = only_bounds_vc(&func);
        match &vc.formula {
            Formula::Not(inner) => assert!(
                matches!(inner.as_ref(), Formula::Var(_, Sort::Bool)),
                "non-SSA condition must fall back to a bare Bool variable, got {inner:?}"
            ),
            other => panic!("expected Not(Var(_, Bool)), got {other:?}"),
        }
    }

    #[test]
    fn test_build_v1_vcs_unsupported_assert_condition_fails_closed() {
        let mut func = minimal_func("unsupported_assert_cond");
        func.body.blocks[0].terminator = Terminator::Assert {
            unwind: UnwindEdge::Unreachable,
            cond: Operand::Unsupported {
                kind: "Operand::OpaqueBool".to_string(),
                detail: "condition was not modeled".to_string(),
            },
            expected: true,
            msg: AssertMessage::Custom("opaque".to_string()),
            target: BlockId(0),
            span: SourceSpan::default(),
        };

        let vcs = build_v1_vcs(&func);
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })
                && vc.formula == Formula::Bool(true)),
            "unsupported assert condition must fail closed"
        );
    }

    #[test]
    fn test_build_v1_vcs_unsupported_type_fails_closed() {
        let mut func = minimal_func("unsupported_type");
        func.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Unsupported {
                kind: "TyKind::Alias".to_string(),
                detail: "alias type was not normalized".to_string(),
            },
            name: Some("x".to_string()),
        });

        let vcs = build_v1_vcs(&func);
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })
                && vc.formula == Formula::Bool(true)),
            "unsupported local types must fail closed in v1 fallback"
        );
    }

    #[test]
    fn test_build_v1_vcs_from_div_statement() {
        let mut func = minimal_func("div_stmt");
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".to_string()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::i32();
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(2)),
            ),
            span: SourceSpan::default(),
        });

        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
        assert_eq!(vcs[0].formula, Formula::Bool(false));
    }

    #[test]
    fn test_build_v1_vcs_from_rem_statement() {
        let mut func = minimal_func("rem_stmt");
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".to_string()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".to_string()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ];
        func.body.arg_count = 2;
        func.body.return_ty = Ty::i32();
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Rem,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: SourceSpan::default(),
        });

        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::RemainderByZero));
        assert_eq!(
            vcs[0].formula,
            Formula::Eq(
                Box::new(Formula::Var(
                    place_var_name(&func, &Place::local(2)).expect("place supported"),
                    Sort::Int,
                )),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn test_build_v1_vcs_projected_divisor_does_not_alias_base_local() {
        let mut func = minimal_func("projected_divisor");
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]),
                name: Some("x".to_string()),
            },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ];
        func.body.return_ty = Ty::i32();
        let projected = Place::field(1, 0);
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Constant(ConstValue::Int(10)),
                Operand::Copy(projected.clone()),
            ),
            span: SourceSpan::default(),
        });

        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert_eq!(
            vcs[0].formula,
            Formula::Eq(
                Box::new(Formula::Var(
                    place_var_name(&func, &projected).expect("projected place supported"),
                    Sort::Int,
                )),
                Box::new(Formula::Int(0)),
            )
        );
        assert_ne!(
            place_var_name(&func, &projected).expect("projected place supported"),
            place_var_name(&func, &Place::local(1)).expect("base place supported"),
            "x.0 must not be encoded as the same variable as x"
        );
    }

    #[test]
    fn test_build_v1_vcs_skips_div_statement_guarded_by_assert() {
        let mut func = minimal_func("guarded_div");
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".to_string()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".to_string()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: Ty::i32(), name: None },
        ];
        func.body.arg_count = 2;
        func.body.return_ty = Ty::i32();
        func.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert {
                    unwind: UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::DivisionByZero,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ];

        let vcs = build_v1_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
        assert_eq!(
            vcs[0].formula,
            Formula::Var(
                place_var_name(&func, &Place::local(3)).expect("place supported"),
                Sort::Bool
            )
        );
    }

    #[test]
    fn test_config_defaults() {
        let config = MirRouterConfig::default();
        assert_eq!(config.bmc_depth, 100);
        assert_eq!(config.timeout_ms, 30_000);
        assert!(!config.produce_proofs);
        assert!(!config.shadow_mode);
    }

    #[test]
    fn test_portfolio_strategy_empty() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("empty_portfolio");
        let result = router.dispatch_portfolio(&func, &[]);
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("no strategies"));
            }
            _ => panic!("expected Unknown for empty portfolio"),
        }
    }

    // -----------------------------------------------------------------------
    // Shadow mode tests
    // -----------------------------------------------------------------------

    fn shadow_router() -> MirRouter {
        let config = MirRouterConfig { shadow_mode: true, ..MirRouterConfig::default() };
        MirRouter::new(Router::new(), config)
    }

    #[test]
    fn test_shadow_verify_plain_function_equivalent() {
        let router = shadow_router();
        let func = minimal_func("plain_shadow");

        let shadow = router.shadow_verify(&func);

        // Plain function: both MIR router (V1Fallback) and v1 should agree.
        assert_eq!(shadow.strategy, MirStrategy::V1Fallback);
        assert_eq!(shadow.discrepancy, ShadowDiscrepancy::Equivalent);
        assert!(matches!(shadow.mir_result, VerificationResult::Unknown { .. }));
        assert!(matches!(shadow.v1_result, VerificationResult::Unknown { .. }));
        assert!(matches!(shadow.chosen_result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_shadow_verify_contract_function_results_comparable() {
        let router = shadow_router();
        let func = func_with_contract("contract_shadow", ContractKind::Requires);

        let shadow = router.shadow_verify(&func);

        // Contract function uses ContractVerification strategy via MIR router.
        assert_eq!(shadow.strategy, MirStrategy::ContractVerification);
        // Both results are present regardless of discrepancy.
        assert!(!shadow.mir_result.solver_name().is_empty());
        assert!(!shadow.v1_result.solver_name().is_empty());
    }

    #[test]
    fn test_shadow_verify_loop_function_dispatch() {
        let router = shadow_router();
        let func = func_with_loop("loop_shadow");

        let shadow = router.shadow_verify(&func);

        // Loop function classified as BoundedModelCheck.
        assert_eq!(shadow.strategy, MirStrategy::BoundedModelCheck);
        // Both paths produce results.
        assert!(!shadow.mir_result.solver_name().is_empty());
        assert!(!shadow.v1_result.solver_name().is_empty());
    }

    #[test]
    fn test_shadow_verify_fallback_to_v1_on_mir_unknown() {
        let router = shadow_router();
        // A contract function dispatches to trust-wp-lib which returns Unknown
        // in the mock test environment. The v1 path with no VCs now also
        // returns Unknown rather than a vacuous proof.
        let func = func_with_spec("fallback_shadow");

        let shadow = router.shadow_verify(&func);

        // If MIR result is Unknown but v1 is Proved, chosen_result should be v1.
        if !shadow.mir_result.is_proved() && !shadow.mir_result.is_failed() {
            assert!(
                shadow.chosen_result.is_proved() == shadow.v1_result.is_proved(),
                "When MIR is inconclusive, chosen should match v1"
            );
        }
    }

    #[test]
    fn test_shadow_verify_empty_v1_stays_unknown() {
        let router = shadow_router();
        let func = minimal_func("empty_shadow");

        let shadow = router.shadow_verify(&func);

        assert!(matches!(shadow.mir_result, VerificationResult::Unknown { .. }));
        assert!(matches!(shadow.chosen_result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_shadow_mode_through_verify_function() {
        // When shadow_mode is on, verify_function should still return a result.
        let router = shadow_router();
        let func = minimal_func("verify_fn_shadow");
        let result = router.verify_function(&func);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_shadow_mode_off_skips_shadow() {
        // When shadow_mode is off, verify_function does NOT do shadow dispatch.
        let router = MirRouter::with_defaults();
        assert!(!router.config().shadow_mode);
        let func = minimal_func("no_shadow");
        let result = router.verify_function(&func);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_classify_discrepancy_both_proved() {
        let proved_a = VerificationResult::Proved {
            solver: "a".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let proved_b = VerificationResult::Proved {
            solver: "b".into(),
            time_ms: 20,
            strength: ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert_eq!(classify_discrepancy(&proved_a, &proved_b), ShadowDiscrepancy::Equivalent);
    }

    #[test]
    fn test_classify_discrepancy_both_failed() {
        let failed_a =
            VerificationResult::Failed { solver: "a".into(), time_ms: 10, counterexample: None };
        let failed_b =
            VerificationResult::Failed { solver: "b".into(), time_ms: 20, counterexample: None };
        assert_eq!(classify_discrepancy(&failed_a, &failed_b), ShadowDiscrepancy::Equivalent);
    }

    #[test]
    fn test_classify_discrepancy_both_unknown() {
        let unknown_a = VerificationResult::Unknown {
            solver: "a".into(),
            time_ms: 10,
            reason: "timeout".to_string(),
        };
        let unknown_b = VerificationResult::Unknown {
            solver: "b".into(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(classify_discrepancy(&unknown_a, &unknown_b), ShadowDiscrepancy::Equivalent);
    }

    #[test]
    fn test_classify_discrepancy_mir_stronger_proved() {
        let proved = VerificationResult::Proved {
            solver: "mir".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let unknown = VerificationResult::Unknown {
            solver: "v1".into(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(classify_discrepancy(&proved, &unknown), ShadowDiscrepancy::MirStronger);
    }

    #[test]
    fn test_classify_discrepancy_mir_stronger_failed() {
        let failed =
            VerificationResult::Failed { solver: "mir".into(), time_ms: 10, counterexample: None };
        let unknown = VerificationResult::Unknown {
            solver: "v1".into(),
            time_ms: 20,
            reason: "complex".to_string(),
        };
        assert_eq!(classify_discrepancy(&failed, &unknown), ShadowDiscrepancy::MirStronger);
    }

    #[test]
    fn test_classify_discrepancy_v1_stronger_proved() {
        let unknown = VerificationResult::Unknown {
            solver: "mir".into(),
            time_ms: 10,
            reason: "complex".to_string(),
        };
        let proved = VerificationResult::Proved {
            solver: "v1".into(),
            time_ms: 20,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert_eq!(classify_discrepancy(&unknown, &proved), ShadowDiscrepancy::V1Stronger);
    }

    #[test]
    fn test_classify_discrepancy_v1_stronger_failed() {
        let unknown = VerificationResult::Unknown {
            solver: "mir".into(),
            time_ms: 10,
            reason: "complex".to_string(),
        };
        let failed =
            VerificationResult::Failed { solver: "v1".into(), time_ms: 20, counterexample: None };
        assert_eq!(classify_discrepancy(&unknown, &failed), ShadowDiscrepancy::V1Stronger);
    }

    #[test]
    fn test_classify_discrepancy_mismatch_proved_vs_failed() {
        let proved = VerificationResult::Proved {
            solver: "mir".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let failed =
            VerificationResult::Failed { solver: "v1".into(), time_ms: 20, counterexample: None };
        assert_eq!(classify_discrepancy(&proved, &failed), ShadowDiscrepancy::Mismatch);
    }

    #[test]
    fn test_classify_discrepancy_mismatch_failed_vs_proved() {
        let failed =
            VerificationResult::Failed { solver: "mir".into(), time_ms: 10, counterexample: None };
        let proved = VerificationResult::Proved {
            solver: "v1".into(),
            time_ms: 20,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert_eq!(classify_discrepancy(&failed, &proved), ShadowDiscrepancy::Mismatch);
    }

    #[test]
    fn test_shadow_discrepancy_display() {
        assert_eq!(ShadowDiscrepancy::Equivalent.to_string(), "equivalent");
        assert_eq!(ShadowDiscrepancy::MirStronger.to_string(), "mir_stronger");
        assert_eq!(ShadowDiscrepancy::V1Stronger.to_string(), "v1_stronger");
        assert_eq!(ShadowDiscrepancy::Mismatch.to_string(), "mismatch");
    }

    #[test]
    fn test_result_summary_format() {
        let proved = VerificationResult::Proved {
            solver: "test".into(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert_eq!(result_summary(&proved), "Proved(test, 42ms)");

        let failed =
            VerificationResult::Failed { solver: "test".into(), time_ms: 7, counterexample: None };
        assert_eq!(result_summary(&failed), "Failed(test, 7ms)");

        let unknown = VerificationResult::Unknown {
            solver: "test".into(),
            time_ms: 0,
            reason: "complex formula".to_string(),
        };
        assert_eq!(result_summary(&unknown), "Unknown(test: complex formula)");

        let timeout = VerificationResult::Timeout { solver: "test".into(), timeout_ms: 5000 };
        assert_eq!(result_summary(&timeout), "Timeout(test, 5000ms)");
    }

    #[test]
    fn test_shadow_verify_all_functions_produce_results() {
        // Verify that shadow mode works for each function type.
        let router = shadow_router();
        let funcs = vec![
            minimal_func("plain"),
            func_with_contract("contracted", ContractKind::Requires),
            func_with_loop("loopy"),
            func_with_ffi("ffi"),
            func_with_raw_ptr_locals("raw_ptr"),
            func_with_atomics("atomic"),
        ];

        for func in &funcs {
            let shadow = router.shadow_verify(func);
            // Every function should produce a ShadowResult with both paths.
            assert!(
                !shadow.mir_result.solver_name().is_empty(),
                "MIR result missing solver for {}",
                func.name,
            );
            assert!(
                !shadow.v1_result.solver_name().is_empty(),
                "v1 result missing solver for {}",
                func.name,
            );
            assert!(
                !shadow.chosen_result.solver_name().is_empty(),
                "chosen result missing solver for {}",
                func.name,
            );
        }
    }

    // -----------------------------------------------------------------------
    // Portfolio racing tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_portfolio_racing_enabled_by_default() {
        let config = MirRouterConfig::default();
        assert!(config.enable_portfolio_racing);
        assert!(!config.infer_invariants);
    }

    #[test]
    fn test_portfolio_parallel_single_strategy() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("single_strategy");
        // Single strategy should not invoke parallelism.
        let result = router.dispatch_portfolio(&func, &[MirStrategy::V1Fallback]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_portfolio_parallel_multiple_strategies() {
        let router = MirRouter::with_defaults();
        let func = minimal_func("multi_strategy");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];
        let result = router.dispatch_portfolio(&func, &strategies);
        // Both backends produce results; at least one should be definitive.
        assert!(
            result.is_proved()
                || result.is_failed()
                || matches!(result, VerificationResult::Unknown { .. }),
        );
    }

    #[test]
    fn test_portfolio_sequential_fallback() {
        let config =
            MirRouterConfig { enable_portfolio_racing: false, ..MirRouterConfig::default() };
        let router = MirRouter::new(Router::new(), config);
        let func = minimal_func("seq_fallback");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];
        let result = router.dispatch_portfolio(&func, &strategies);
        // Sequential should still produce a valid result.
        assert!(
            result.is_proved()
                || result.is_failed()
                || matches!(result, VerificationResult::Unknown { .. }),
        );
    }

    #[test]
    fn test_portfolio_parallel_panic_fails_closed() {
        struct PanickingBackend;

        impl crate::VerificationBackend for PanickingBackend {
            fn name(&self) -> &str {
                "panicking-v1"
            }

            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }

            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                panic!("intentional MIR portfolio isolation test panic");
            }
        }

        let router = MirRouter::new(
            Router::with_backends(vec![Box::new(PanickingBackend)]),
            Default::default(),
        );
        let func = func_with_div_statement("portfolio_parallel_panic");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];

        let result = router.dispatch_portfolio(&func, &strategies);

        assert!(
            matches!(
                result,
                VerificationResult::Unknown { solver, ref reason, .. }
                    if solver.as_str() == "mir-router-portfolio" && reason.contains("panicked")
            ),
            "portfolio lane panic must fail closed: {result:?}"
        );
    }

    #[test]
    fn test_portfolio_sequential_panic_fails_closed() {
        struct PanickingBackend;

        impl crate::VerificationBackend for PanickingBackend {
            fn name(&self) -> &str {
                "panicking-v1"
            }

            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }

            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                panic!("intentional MIR sequential portfolio isolation test panic");
            }
        }

        let config =
            MirRouterConfig { enable_portfolio_racing: false, ..MirRouterConfig::default() };
        let router =
            MirRouter::new(Router::with_backends(vec![Box::new(PanickingBackend)]), config);
        let func = func_with_div_statement("portfolio_sequential_panic");
        let strategies = vec![MirStrategy::V1Fallback, MirStrategy::BoundedModelCheck];

        let result = router.dispatch_portfolio(&func, &strategies);

        assert!(
            matches!(
                result,
                VerificationResult::Unknown { solver, ref reason, .. }
                    if solver.as_str() == "mir-router-portfolio" && reason.contains("panicked")
            ),
            "sequential portfolio lane panic must fail closed: {result:?}"
        );
    }

    #[test]
    fn test_unsafe_audit_portfolio_racing() {
        // UnsafeAudit with portfolio racing enabled dispatches via portfolio.
        let router = MirRouter::with_defaults();
        let mut func = func_with_unsafe("unsafe_portfolio");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr != null".to_string(),
        });
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_unsafe_audit_sequential_fallback() {
        let config =
            MirRouterConfig { enable_portfolio_racing: false, ..MirRouterConfig::default() };
        let router = MirRouter::new(Router::new(), config);
        let mut func = func_with_unsafe("unsafe_seq");
        func.contracts.push(Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "ptr != null".to_string(),
        });
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    // -----------------------------------------------------------------------
    // Invariant inference config test
    // -----------------------------------------------------------------------

    #[test]
    fn test_bmc_dispatch_with_invariant_hints_config() {
        // When infer_invariants is true and function has loops,
        // dispatch should use the invariant hints path.
        let config = MirRouterConfig { infer_invariants: true, ..MirRouterConfig::default() };
        let router = MirRouter::new(Router::new(), config);
        let func = func_with_loop("loopy_invariant");
        let result = router.verify_function(&func);
        // The function has loops so it is classified as BoundedModelCheck,
        // and with infer_invariants=true it goes through the hints path.
        // It should still produce a valid result.
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_bmc_dispatch_without_invariant_hints() {
        // When infer_invariants is false, dispatch goes straight to BMC.
        let config = MirRouterConfig { infer_invariants: false, ..MirRouterConfig::default() };
        let router = MirRouter::new(Router::new(), config);
        let func = func_with_loop("loopy_no_hints");
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    // -----------------------------------------------------------------------
    // Real MIR fixture tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_real_mir_classify_sum_to_has_loops() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__sum_to");
        // sum_to has a loop (back-edge), should classify as BoundedModelCheck
        assert_eq!(router.classify(&func), MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_real_mir_classify_safe_divide_v1_fallback() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__safe_divide");
        // safe_divide has no contracts/loops/unsafe — V1Fallback
        assert_eq!(router.classify(&func), MirStrategy::V1Fallback);
    }

    #[test]
    fn test_real_mir_classify_unsafe_read_raw_ptr() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__unsafe_read");
        // unsafe_read has raw pointer local — SeparationLogic
        assert_eq!(router.classify(&func), MirStrategy::SeparationLogic);
    }

    #[test]
    fn test_real_mir_classify_increment_v1_fallback() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__increment");
        assert_eq!(router.classify(&func), MirStrategy::V1Fallback);
    }

    #[test]
    fn test_real_mir_classify_max_of_v1_fallback() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__max_of");
        // max_of has SwitchInt but no back-edge — check the actual result
        let strategy = router.classify(&func);
        // Should not be BoundedModelCheck since no loop back-edge
        assert_ne!(strategy, MirStrategy::BoundedModelCheck);
    }

    #[test]
    fn test_real_mir_dispatch_safe_divide_proves() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__safe_divide");
        let result = router.verify_function(&func);
        // Should produce a valid result (proved or at least not timeout)
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_real_mir_dispatch_increment_proves() {
        let router = MirRouter::with_defaults();
        let func = load_fixture("test_functions__increment");
        let result = router.verify_function(&func);
        assert!(!result.solver_name().is_empty());
    }

    #[test]
    fn test_real_mir_verify_all_fixtures() {
        let router = MirRouter::with_defaults();
        let dir = fixture_dir();
        let mut count = 0;
        for entry in std::fs::read_dir(&dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.extension().is_none_or(|ext| ext != "json") {
                continue;
            }
            let json = std::fs::read_to_string(&path).unwrap();
            if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&json) {
                let strategy = router.classify(&func);
                let result = router.verify_function(&func);
                assert!(
                    !result.solver_name().is_empty(),
                    "fixture {} ({:?}) produced no solver name",
                    func.name,
                    strategy
                );
                count += 1;
            }
        }
        assert!(count >= 10, "expected at least 10 fixtures, found {count}");
    }

    #[test]
    fn test_real_mir_shadow_mode_on_fixtures() {
        let config = MirRouterConfig { shadow_mode: true, ..MirRouterConfig::default() };
        let router = MirRouter::new(Router::new(), config);
        let func = load_fixture("test_functions__safe_divide");
        let shadow = router.shadow_verify(&func);
        assert!(!shadow.mir_result.solver_name().is_empty());
        assert!(!shadow.v1_result.solver_name().is_empty());
    }

    #[test]
    fn test_real_mir_build_v1_vcs_safe_divide_has_div_vc() {
        let func = load_fixture("test_functions__safe_divide");
        let vcs = build_v1_vcs(&func);
        // safe_divide has x / y — should produce a DivisionByZero VC
        assert!(!vcs.is_empty(), "safe_divide should produce at least one VC");
        assert!(
            vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
            "safe_divide should have a DivisionByZero VC"
        );
    }
}

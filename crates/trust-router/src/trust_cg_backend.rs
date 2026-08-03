// trust-router/trust_cg_backend.rs: trust_cg verified codegen backend for the MIR router
//
// Activates the trust_cg codegen path in trust-router. When the
// `trust_cg-backend` feature is enabled, scalar functions can be dispatched to
// the trust-cg-bridge lowering pipeline for verified code generation.
//
// The backend implements `VerificationBackend` so it can participate in the
// standard Router dispatch, and also exposes `verify_codegen` for direct use
// by the MirRouter's codegen strategy and by `#[trust::verified_codegen]`.
//
// `verify_codegen` returns a graded `CodegenVerdict` rather than a
// `VerificationResult` because the two checks it runs sit on opposite sides of
// the line between "the lowering kept its shape" and "these bytes compute this
// function". Collapsing them into one `Proved` is how a structural comparison
// ends up in front of a user as a proof of verified codegen.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_bridge::BridgeError;
use trust_types::{VerifiableFunction, VerificationCondition, VerificationResult};

use crate::{BackendRole, VerificationBackend};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from the trust_cg codegen backend in the router.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustCgBackendError {
    /// The trust_cg bridge returned an error during lowering.
    #[error("trust-cg bridge error: {0}")]
    Bridge(#[from] BridgeError),

    /// The function is not suitable for trust_cg codegen (e.g., uses unsupported ops).
    #[error("function `{function}` not suitable for trust_cg codegen: {reason}")]
    Unsupported { function: String, reason: String },
}

// ---------------------------------------------------------------------------
// Backend configuration
// ---------------------------------------------------------------------------

/// Configuration for the trust_cg codegen backend.
#[derive(Debug, Clone)]
pub struct TrustCgBackendConfig {
    /// Whether the backend is available for dispatch.
    pub available: bool,
    /// The rustc target the caller is compiling for, as `(arch, triple)`.
    ///
    /// A codegen claim is a claim about machine code for ONE target. Left
    /// `None`, the backend checks host emission, which is only the same thing
    /// when the caller is not cross-compiling — so a caller that knows its
    /// target must say so, or the verdict describes a different machine than
    /// the one being compiled for.
    pub target: Option<(String, String)>,
}

impl Default for TrustCgBackendConfig {
    fn default() -> Self {
        Self::for_host()
    }
}

impl TrustCgBackendConfig {
    /// An available backend that checks host emission.
    #[must_use]
    pub fn for_host() -> Self {
        Self { available: true, target: None }
    }

    /// An available backend that checks emission for the given rustc target
    /// architecture and triple.
    #[must_use]
    pub fn for_target(arch: impl Into<String>, triple: impl Into<String>) -> Self {
        Self { available: true, target: Some((arch.into(), triple.into())) }
    }

    /// A backend that must not run at all.
    #[must_use]
    pub fn unavailable() -> Self {
        Self { available: false, target: None }
    }
}

// ---------------------------------------------------------------------------
// Codegen verdict
// ---------------------------------------------------------------------------

/// What a verified-codegen claim about one function is actually backed by.
///
/// The distinction between the first two variants and [`Self::RoundTripOnly`] is
/// the whole point of this type. A structural round trip
/// (`lift(lower(f))` agrees with `f` on block count, argument count, and the
/// arithmetic-operation multiset) is a NECESSARY condition on a faithful
/// lowering and a cheap way to catch lowering-shape drift, but it says nothing
/// about the bytes: it never emits an instruction, never decodes one, and never
/// discharges an equality. Reporting it as a proof would put a claim in front of
/// users that no evidence in this crate supports.
///
/// Deliberately exhaustive: a new grade must break every consumer that reports
/// one, so nobody can add evidence tiers that silently fall into whichever arm
/// happens to be the catch-all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenVerdict {
    /// The emitted machine code was proved equal to the function's auto-derived
    /// IR semantics on every input, and the Clean kernel re-checked the
    /// certificate with an empty axiom closure. The solver is a producer only.
    KernelProved,
    /// The same equality, discharged by `ay` alone: the obligation is outside
    /// the fragment that exports a kernel-re-checkable certificate, so `ay` is
    /// in the trusted base for this claim.
    AyValidated,
    /// A concrete input makes the emitted machine code compute a different value
    /// from the function's IR semantics. A miscompile.
    Miscompiled {
        /// Which obligation was refuted.
        detail: String,
    },
    /// The lowering round-tripped structurally and nothing else was checked:
    /// necessary, not sufficient.
    RoundTripOnly {
        /// Why the byte-level output-preservation gate could not decide.
        undecided: String,
    },
    /// `lift(lower(f))` disagrees with `f`, so the lowering does not even
    /// preserve the function's shape.
    RoundTripMismatch {
        /// Which structural property diverged.
        detail: String,
    },
    /// The backend was not configured to run.
    Unavailable {
        /// Why nothing was checked.
        reason: String,
    },
}

impl CodegenVerdict {
    /// Whether a machine-level output-preservation proof backs this verdict.
    ///
    /// [`Self::RoundTripOnly`] is deliberately excluded: it is the verdict that
    /// exists to be distinguishable from a proof.
    #[must_use]
    pub fn is_output_preserving(&self) -> bool {
        matches!(self, Self::KernelProved | Self::AyValidated)
    }
}

// ---------------------------------------------------------------------------
// trust_cg codegen backend
// ---------------------------------------------------------------------------

/// trust_cg verified codegen backend for the trust-router.
///
/// Lowers `VerifiableFunction`s to trust_cg LIR via `trust-cg-bridge` and
/// decides how faithfully that lowering — and, where the machine-semantics lane
/// reaches, the machine code it produces — preserves the function.
///
/// This backend operates at the MIR level (on `VerifiableFunction`, not on
/// `VerificationCondition`), so the `VerificationBackend` trait implementation
/// is a thin wrapper that always returns `Unknown` (codegen is not a VC solver).
/// The real entry point is `verify_codegen`.
pub struct TrustCgBackend {
    config: TrustCgBackendConfig,
}

impl TrustCgBackend {
    /// Create a new trust_cg backend with the given configuration.
    #[must_use]
    pub fn new(config: TrustCgBackendConfig) -> Self {
        Self { config }
    }

    /// Create a backend with default configuration: available, checking host
    /// emission.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self { config: TrustCgBackendConfig::default() }
    }

    /// Whether the backend is available for dispatch.
    #[must_use]
    pub fn is_available(&self) -> bool {
        self.config.available
    }

    /// Verify a function through the trust_cg codegen pipeline.
    ///
    /// Two checks run, in increasing strength, and the returned
    /// [`CodegenVerdict`] names which one actually carried:
    ///
    /// 1. **Structural round trip.** Lower the `VerifiableFunction` to trust_cg
    ///    LIR, lift it back, and compare block count, argument count, and the
    ///    multiset of arithmetic/logic operations. This catches lowering-shape
    ///    drift (a dropped, duplicated, or substituted arithmetic op) for the
    ///    cost of no code emission, but it never looks at an instruction, so it
    ///    cannot witness a miscompile that lives in the encoding, the register
    ///    allocation, or the ABI. Necessary, not sufficient.
    /// 2. **Byte-level output preservation.** Emit the function to a real
    ///    object, decode the emitted bytes, compute their machine semantics, and
    ///    discharge equality against the semantics auto-derived from the IR. This
    ///    is the check that can return [`CodegenVerdict::Miscompiled`].
    ///
    /// Step 2 has a bounded frontier (AArch64 machine semantics, straight-line
    /// integer scalar shapes) and reports [`CodegenVerdict::RoundTripOnly`] with
    /// the reason outside it, rather than borrowing step 1's success to look like
    /// a proof.
    pub fn verify_codegen(
        &self,
        func: &VerifiableFunction,
    ) -> Result<CodegenVerdict, TrustCgBackendError> {
        if !self.config.available {
            return Ok(CodegenVerdict::Unavailable {
                reason: "trust-cg backend not available".to_string(),
            });
        }

        let lir_func = trust_cg_bridge::lower_to_lir(func)?;
        let lifted = trust_cg_bridge::lift_from_lir(&lir_func)?;

        if let Some(detail) = round_trip_divergence(func, &lifted) {
            return Ok(CodegenVerdict::RoundTripMismatch { detail });
        }

        Ok(self.output_preservation_verdict(func))
    }

    /// Byte-level output preservation for `func`, or the reason it is undecided.
    ///
    /// Without the `trust-cg-output-gate` feature the emitter, disassembler,
    /// machine semantics, and kernel re-check are not linked in, so no verdict
    /// stronger than the structural round trip is derivable — and that must be
    /// visible in what the caller reports, not swallowed.
    #[cfg(not(feature = "trust-cg-output-gate"))]
    fn output_preservation_verdict(&self, _func: &VerifiableFunction) -> CodegenVerdict {
        CodegenVerdict::RoundTripOnly {
            undecided: "this build does not link the byte-level output-preservation gate \
                        (trust-cg-output-gate)"
                .to_string(),
        }
    }

    #[cfg(feature = "trust-cg-output-gate")]
    fn output_preservation_verdict(&self, func: &VerifiableFunction) -> CodegenVerdict {
        use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
        use trust_cg_bridge::verify_output::OutputVerdict;

        let emitter = match &self.config.target {
            Some((arch, triple)) => {
                let Some(arch) = TrustCgTargetArch::from_rustc_arch(arch) else {
                    return CodegenVerdict::RoundTripOnly {
                        undecided: format!("trust-cg does not target architecture `{arch}`"),
                    };
                };
                match TrustCgCodegenBackend::try_new_for_triple(arch, triple.clone()) {
                    Ok(backend) => backend,
                    Err(error) => {
                        return CodegenVerdict::RoundTripOnly {
                            undecided: format!("no audited trust-cg target `{triple}`: {error}"),
                        };
                    }
                }
            }
            None => TrustCgCodegenBackend::host(),
        };

        let verdict =
            trust_cg_bridge::verify_output::verify_output_preserved_with_backend(func, &emitter);
        // `is_kernel_proved` covers both kernel grades (SAT-reflection re-check
        // and O(1) structured instantiation); reading the evidence enum here
        // instead would silently demote a future kernel grade to ay authority.
        if verdict.is_kernel_proved() {
            return CodegenVerdict::KernelProved;
        }
        match verdict {
            OutputVerdict::Proven { .. } => CodegenVerdict::AyValidated,
            OutputVerdict::Refuted { detail } => CodegenVerdict::Miscompiled { detail },
            OutputVerdict::Unknown { reason } => {
                CodegenVerdict::RoundTripOnly { undecided: reason }
            }
            // `OutputVerdict` is `#[non_exhaustive]`. A verdict this crate does
            // not recognize is not evidence of anything, so it degrades to the
            // structural claim instead of being folded into whichever known
            // variant it superficially resembles.
            other => CodegenVerdict::RoundTripOnly {
                undecided: format!("unrecognized output-preservation verdict: {other:?}"),
            },
        }
    }

    /// Check whether a function is suitable for trust_cg codegen.
    ///
    /// The bridge supports scalar functions only: no references, raw pointers,
    /// slices, arrays, tuples, or ADTs. This method checks the function's
    /// locals for unsupported types.
    #[must_use]
    pub fn can_handle_function(&self, func: &VerifiableFunction) -> bool {
        if !self.config.available {
            return false;
        }

        // Check all locals have types the bridge can map.
        func.body.locals.iter().all(|local| trust_cg_bridge::map_type(&local.ty).is_ok())
    }
}

/// Name the first structural property on which `lifted` diverges from `func`,
/// or `None` when the trust-cg round trip preserved all of them.
///
/// Returning the property rather than a bare bool is what lets a failed round
/// trip be reported to the user as something they can act on: "the lowering
/// dropped an arithmetic operation" and "the lowering lost a basic block" are
/// different defects with different fixes.
fn round_trip_divergence(func: &VerifiableFunction, lifted: &VerifiableFunction) -> Option<String> {
    if func.body.blocks.len() != lifted.body.blocks.len() {
        return Some(format!(
            "block count {} became {} across the round trip",
            func.body.blocks.len(),
            lifted.body.blocks.len()
        ));
    }
    if func.body.arg_count != lifted.body.arg_count {
        return Some(format!(
            "argument count {} became {} across the round trip",
            func.body.arg_count, lifted.body.arg_count
        ));
    }
    let before = arith_op_signature(func);
    let after = arith_op_signature(lifted);
    if before != after {
        return Some(format!(
            "arithmetic operation multiset {before:?} became {after:?} across the round trip"
        ));
    }
    None
}

/// The sorted multiset of arithmetic/logic operation tags (binary ops, unary
/// ops, casts) across a function's statements — the operation signature the
/// round-trip check compares before vs. after the trust-cg lowering.
/// Constant/`Use`/aggregate/structural rvalues are intentionally excluded: the
/// LIR's explicit `Iconst`s and temporaries reshape those without changing
/// program meaning, so including them would false-fail a faithful lowering.
fn arith_op_signature(func: &VerifiableFunction) -> Vec<String> {
    use trust_types::{Rvalue, Statement};
    let mut sig = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                match rvalue {
                    Rvalue::BinaryOp(op, ..) | Rvalue::CheckedBinaryOp(op, ..) => {
                        sig.push(format!("bin:{op:?}"));
                    }
                    Rvalue::UnaryOp(op, ..) => sig.push(format!("un:{op:?}")),
                    Rvalue::Cast(..) => sig.push("cast".to_string()),
                    _ => {}
                }
            }
        }
    }
    sig.sort_unstable();
    sig
}

// ---------------------------------------------------------------------------
// VerificationBackend trait implementation
// ---------------------------------------------------------------------------

impl VerificationBackend for TrustCgBackend {
    fn name(&self) -> &str {
        "trust_cg-router"
    }

    fn role(&self) -> BackendRole {
        // Codegen is not a solver role; use General as the fallback category.
        BackendRole::General
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        // The trust_cg backend operates on VerifiableFunctions, not VCs.
        // It cannot handle VC dispatch directly.
        false
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) =
            crate::backend_trait::unsupported_mir_unknown(vc, "trust_cg-router", 0)
        {
            return result;
        }

        // This backend does not verify VCs. Use `verify_codegen` instead.
        VerificationResult::Unknown {
            solver: "trust_cg-router".into(),
            time_ms: 0,
            reason: "trust-cg codegen backend does not handle VCs directly; \
                     use verify_codegen() for function-level codegen verification"
                .to_string(),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    /// Build `fn add(a: i32, b: i32) -> i32 { a + b }` for testing.
    fn make_add_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with unsupported types (reference).
    fn make_ref_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "ref_fn".to_string(),
            def_path: "test::ref_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                        name: Some("r".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_trust_cg_backend_name() {
        let backend = TrustCgBackend::with_defaults();
        assert_eq!(backend.name(), "trust_cg-router");
    }

    #[test]
    fn test_trust_cg_backend_is_available() {
        let backend = TrustCgBackend::with_defaults();
        assert!(backend.is_available());

        let unavailable =
            TrustCgBackend::new(TrustCgBackendConfig { available: false, ..Default::default() });
        assert!(!unavailable.is_available());
    }

    #[test]
    fn test_trust_cg_backend_can_handle_scalar_function() {
        let backend = TrustCgBackend::with_defaults();
        let func = make_add_function();
        assert!(backend.can_handle_function(&func));
    }

    #[test]
    fn test_trust_cg_backend_cannot_handle_ref_function() {
        let backend = TrustCgBackend::with_defaults();
        let func = make_ref_function();
        assert!(!backend.can_handle_function(&func));
    }

    /// A lowering that substitutes one arithmetic operation for another —
    /// exactly the miscompile class the round-trip check exists to catch.
    fn mutate_first_binop(func: &VerifiableFunction, replacement: BinOp) -> VerifiableFunction {
        let mut mutated = func.clone();
        for block in &mut mutated.body.blocks {
            for stmt in &mut block.stmts {
                if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, ..), .. } = stmt {
                    *op = replacement;
                    return mutated;
                }
            }
        }
        panic!("fixture has no binary operation to mutate");
    }

    #[test]
    fn test_trust_cg_backend_cannot_handle_when_unavailable() {
        let backend = TrustCgBackend::new(TrustCgBackendConfig::unavailable());
        let func = make_add_function();
        assert!(!backend.can_handle_function(&func));
    }

    #[test]
    fn test_trust_cg_backend_verify_codegen_scalar_function() {
        let backend = TrustCgBackend::with_defaults();
        let func = make_add_function();

        let verdict = backend.verify_codegen(&func).expect("should succeed for scalar function");
        assert!(
            !matches!(
                verdict,
                CodegenVerdict::RoundTripMismatch { .. } | CodegenVerdict::Miscompiled { .. }
            ),
            "a faithful scalar lowering must not be rejected: {verdict:?}"
        );
    }

    /// The negative control for the structural round trip. Without it, nothing
    /// distinguishes a round-trip check with teeth from one that accepts every
    /// lowering: the only other rejecting fixture in this lane is a function
    /// outside the lowerable fragment, which fails before the comparison runs.
    #[test]
    fn round_trip_rejects_a_substituted_arithmetic_operation() {
        let func = make_add_function();
        let miscompiled = mutate_first_binop(&func, BinOp::Sub);

        assert!(
            round_trip_divergence(&func, &func).is_none(),
            "a function must round-trip against itself"
        );
        let divergence = round_trip_divergence(&func, &miscompiled)
            .expect("Add lowered as Sub must diverge from the source operation multiset");
        assert!(
            divergence.contains("arithmetic operation multiset"),
            "the reported divergence must name the substituted operation: {divergence}"
        );
    }

    #[test]
    fn round_trip_rejects_a_dropped_block() {
        let func = make_add_function();
        let mut truncated = func.clone();
        truncated.body.blocks.clear();

        let divergence = round_trip_divergence(&func, &truncated)
            .expect("a lowering that loses every block must diverge");
        assert!(
            divergence.contains("block count"),
            "the reported divergence must name the lost blocks: {divergence}"
        );
    }

    #[test]
    fn test_trust_cg_backend_verify_codegen_unavailable() {
        let backend = TrustCgBackend::new(TrustCgBackendConfig::unavailable());
        let func = make_add_function();

        let verdict = backend.verify_codegen(&func).expect("should report unavailable, not error");
        assert!(matches!(verdict, CodegenVerdict::Unavailable { .. }));
    }

    /// The honesty invariant this lane exists to hold: a verdict may only claim
    /// output preservation when the byte-level gate actually decided it.
    #[test]
    fn structural_round_trip_alone_is_not_output_preserving() {
        assert!(
            !CodegenVerdict::RoundTripOnly { undecided: "gate not linked".into() }
                .is_output_preserving()
        );
        assert!(CodegenVerdict::KernelProved.is_output_preserving());
        assert!(CodegenVerdict::AyValidated.is_output_preserving());
    }

    /// With the byte-level gate linked in, a straight-line scalar function on an
    /// AArch64 host must reach a machine-checked grade. This is the test that
    /// fails if the gate ever goes vacuous — an unreadable object container, a
    /// decoder gap, a solver that stops answering — instead of the whole lane
    /// quietly degrading to the structural claim while still looking healthy.
    #[cfg(all(feature = "trust-cg-output-gate", target_arch = "aarch64"))]
    #[test]
    fn scalar_function_reaches_a_machine_checked_grade_on_this_host() {
        let backend = TrustCgBackend::with_defaults();
        let verdict = backend.verify_codegen(&make_add_function()).expect("scalar lowering");
        assert!(
            verdict.is_output_preserving(),
            "the byte-level gate must decide a straight-line scalar add here: {verdict:?}"
        );
    }

    /// A function whose body ends in a call is inside the lowerable fragment but
    /// outside the byte-level gate's: with no callee environment, both the IR
    /// interpreter and the machine-side executor fail closed on the call. It must
    /// report the structural claim and say so, never borrow the grade above.
    #[cfg(feature = "trust-cg-output-gate")]
    #[test]
    fn a_call_is_reported_as_round_trip_only() {
        let mut func = make_add_function();
        func.name = "calls_out".to_string();
        func.def_path = "test::calls_out".to_string();
        func.body.blocks[0].terminator = Terminator::Call {
            func: "callee".to_string(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: Default::default(),
        };

        match TrustCgBackend::with_defaults().verify_codegen(&func) {
            Ok(CodegenVerdict::RoundTripOnly { .. }) => {}
            other => panic!("an unmodelled call must not reach a machine-checked grade: {other:?}"),
        }
    }

    #[test]
    fn test_trust_cg_backend_verify_codegen_unsupported_type() {
        let backend = TrustCgBackend::with_defaults();
        let func = make_ref_function();

        // Lowering a function with reference types should fail with a bridge error.
        // Note: the function body has no statements using the ref, so lower_to_lir
        // may succeed (it only fails when encountering unsupported operations).
        // The can_handle_function check is the intended guard.
        let _result = backend.verify_codegen(&func);
        // Whether it errors or returns Unknown depends on the function body.
        // The important thing is it does not panic.
    }

    #[test]
    fn test_trust_cg_backend_does_not_handle_vcs() {
        let backend = TrustCgBackend::with_defaults();
        let vc = VerificationCondition {
            kind: trust_types::VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!backend.can_handle(&vc));

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_trust_cg_backend_config_defaults() {
        let config = TrustCgBackendConfig::default();
        assert!(config.available);
        assert!(config.target.is_none());
    }

    #[test]
    fn test_trust_cg_backend_error_display() {
        let err = TrustCgBackendError::Unsupported {
            function: "test::foo".into(),
            reason: "uses references".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "function `test::foo` not suitable for trust_cg codegen: uses references"
        );

        let bridge_err = BridgeError::UnsupportedType("Ref".to_string());
        let err: TrustCgBackendError = bridge_err.into();
        assert!(err.to_string().contains("trust-cg bridge error"));
    }
}

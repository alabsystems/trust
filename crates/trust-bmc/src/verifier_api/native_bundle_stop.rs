//! Preserve reviewed native causes through adapter transport boundaries.

use std::fmt;

/// A transport error remains terminal. This phase bit grants no proof or retry.
#[derive(Debug)]
pub(super) struct NativeBundleTransportError {
    reason: String,
    before_solver_dispatch: bool,
}

impl NativeBundleTransportError {
    pub(super) fn from_driver(error: trust_mc_driver::NativeSolveError) -> Self {
        // Reviewed at trust-mc a77f9d3c3097b18343fc67889c224a20196a105b:
        // trust-mc-driver/src/native.rs:1969 calls
        // validate_native_bundle_proof_authority_input before translation and
        // before its per-request solve loop. Its instruction checks (including
        // the Alloca rejection at :2655) use this EXACT field via
        // native_bundle_proof_authority_input_error (:3053).
        // Post-solve transport binding uses evidence.* fields (:3152).
        // Do not generalize InvalidInput: that variant also occurs after solves.
        let before_solver_dispatch = matches!(
            &error,
            trust_mc_driver::NativeSolveError::InvalidInput { field, .. }
                if field == "native_trust_ir_bundle.module.functions.instructions"
        );
        Self { reason: super::native_typed_chc_pdr_error_reason(error), before_solver_dispatch }
    }

    pub(super) fn before_solver_dispatch(&self) -> bool {
        self.before_solver_dispatch
    }
}

impl From<String> for NativeBundleTransportError {
    fn from(reason: String) -> Self {
        Self { reason, before_solver_dispatch: false }
    }
}

impl fmt::Display for NativeBundleTransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.reason.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use trust_mc_driver::NativeSolveError;

    use super::*;

    const FIELD: &str = "native_trust_ir_bundle.module.functions.instructions";

    #[test]
    fn native_bundle_stop_classifies_only_the_exact_typed_pre_solve_field() {
        let classified = NativeBundleTransportError::from_driver(NativeSolveError::InvalidInput {
            field: FIELD.into(),
            detail: "Alloca has no internally bound representation".into(),
        });
        assert!(classified.before_solver_dispatch());
        for field in [
            "native_trust_ir_bundle.evidence.native_id",
            "native_trust_ir_bundle.evidence.request_id",
            "native_trust_ir_bundle.evidence.proof_id",
            "native_trust_ir_bundle.module.functions.instructions.future",
            "future",
        ] {
            let error = NativeBundleTransportError::from_driver(NativeSolveError::InvalidInput {
                field: field.into(),
                detail: format!("invalid native solve input `{FIELD}`: Alloca rejected"),
            });
            assert!(!error.before_solver_dispatch(), "wrong typed field: {field}");
        }
    }

    #[test]
    fn native_bundle_stop_keeps_post_solve_and_untyped_failures_unclassified() {
        let rejection = NativeSolveError::ProofGradeRejected {
            rejection: trust_mc_core::ProofEvidenceRejection {
                problem_kind: None,
                reasons: vec![format!("invalid native solve input `{FIELD}`")],
            },
        };
        let solver = NativeSolveError::SolverFailed {
            reason: format!("invalid native solve input `{FIELD}`"),
        };
        for error in [rejection, solver] {
            assert!(!NativeBundleTransportError::from_driver(error).before_solver_dispatch());
        }
        let untyped = NativeBundleTransportError::from(format!(
            "invalid native solve input `{FIELD}`: Alloca rejected"
        ));
        assert!(!untyped.before_solver_dispatch());
    }

    #[test]
    fn not_proved_text_cannot_recover_a_lost_typed_demotion() {
        let row = super::NativeTransportNotProved {
            reason: "fail-closed lowering reachable: 1 unsupported trust_ir construct(s) lowered to unconditional error rules; refutation demoted to unknown (constructs: UnsupportedDirectCallSummary)".into(),
            refutation_demotion: None,
        };
        assert!(!row.refutation_was_demoted(), "original human text is not a typed cause");
    }

    #[test]
    fn option_refusal_keeps_its_exact_reason_without_a_solve_or_demotion() {
        let refusal = trust_mc_trust_bmc::NativeMcRequestOptionsRefusal {
            request_id: trust_ir::NativeRequestId::new(7),
            function: trust_ir::FuncId::new(0),
            obligations: vec![trust_ir::ProofId::new(0)],
            lineage_roots: vec![],
            native_obligation_id: "native-request-7-proof-0".into(),
            field: "chc.pdr.max_frames",
            requested: "Some(0)".into(),
            reason: "the frame limit must be positive".into(),
        };
        let row = NativeTransportNotProved::from_options_refusal(&refusal).unwrap();
        assert_eq!(row.reason, refusal.to_string());
        assert!(!row.refutation_was_demoted());
        let overlong = "x".repeat(16 * 1024);
        for suffix in ["\n", "\0", overlong.as_str()] {
            let mut changed = refusal.clone();
            changed.reason.push_str(suffix);
            assert!(NativeTransportNotProved::from_options_refusal(&changed).is_err());
        }
    }
}

/// Preserve the live producer's typed per-row cause through the adapter map.
/// The human reason remains unchanged and grants no proof or retry authority.
#[derive(Debug)]
pub(super) struct NativeTransportNotProved {
    pub(super) reason: String,
    refutation_demotion: Option<trust_mc_driver::NativeRefutationDemotion>,
}

impl NativeTransportNotProved {
    pub(super) fn from_driver(row: trust_mc_driver::NativeTrustIrChcPdrNotProved) -> Self {
        let refutation_demotion = row.refutation_demotion();
        Self { reason: row.reason, refutation_demotion }
    }

    pub(super) fn from_options_refusal(
        row: &trust_mc_trust_bmc::NativeMcRequestOptionsRefusal,
    ) -> Result<Self, String> {
        let reason = row.to_string();
        if reason.is_empty()
            || reason.trim() != reason
            || reason.len() > 16 * 1024
            || reason.chars().any(char::is_control)
        {
            return Err(format!(
                "native trust_mc bundle returned a non-canonical options refusal for `{}`",
                row.native_obligation_id,
            ));
        }
        Ok(Self { reason, refutation_demotion: None })
    }

    pub(super) fn refutation_was_demoted(&self) -> bool {
        self.refutation_demotion.is_some_and(|cause| {
            cause.fail_closed_lowering_sites > 0 || cause.inductive_hypothesis_sites > 0
        })
    }
}

// trust-transval: Translation validation error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::BlockId;
use trust_types::TranslationValidationError;

/// Errors from the translation validation pipeline.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TransvalError {
    /// Source and target functions have incompatible signatures.
    #[error("signature mismatch: source has {source_args} args, target has {target_args}")]
    SignatureMismatch { source_args: usize, target_args: usize },

    /// A source block has no corresponding target block in the simulation relation.
    #[error("unmapped source block {0:?} has no target correspondence")]
    UnmappedBlock(BlockId),

    /// The simulation relation is structurally invalid.
    #[error("invalid simulation relation: {0}")]
    InvalidRelation(String),

    /// Source or target function body is empty.
    #[error("empty function body: {0}")]
    EmptyBody(String),

    /// Solver returned an error or timed out.
    #[error("solver error: {0}")]
    SolverError(String),

    /// The detected optimization is not yet supported.
    #[error("unsupported optimization: {0}")]
    UnsupportedOptimization(String),
}

// Convert from trust-types TranslationValidationError (shared type)
// instead of trust_vcgen's duplicate.
impl From<TranslationValidationError> for TransvalError {
    fn from(e: TranslationValidationError) -> Self {
        match e {
            TranslationValidationError::SignatureMismatch { source_args, target_args } => {
                Self::SignatureMismatch { source_args, target_args }
            }
            TranslationValidationError::UnmappedBlock(id) => Self::UnmappedBlock(id),
            TranslationValidationError::InvalidRelation(s) => Self::InvalidRelation(s),
            TranslationValidationError::EmptyBody(s) => Self::EmptyBody(s),
            _ => Self::InvalidRelation(e.to_string()),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests for all TransvalError variants
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Existing tests cover SignatureMismatch and EmptyBody via refinement.rs
    // and simulation.rs. These tests cover the 4 untested variants.

    #[test]
    fn test_invalid_relation_error() {
        let err = TransvalError::InvalidRelation("missing entry block mapping".to_string());
        let msg = err.to_string();
        assert!(
            msg.contains("invalid simulation relation"),
            "error message should include variant prefix: {msg}"
        );
        assert!(
            msg.contains("missing entry block mapping"),
            "error message should include detail: {msg}"
        );
        // Verify pattern matching works.
        assert!(matches!(err, TransvalError::InvalidRelation(ref s) if s.contains("missing")));
    }

    #[test]
    fn test_solver_error() {
        let err = TransvalError::SolverError("ay timed out after 30s".to_string());
        let msg = err.to_string();
        assert!(msg.contains("solver error"), "error message should include variant prefix: {msg}");
        assert!(
            msg.contains("ay timed out after 30s"),
            "error message should include detail: {msg}"
        );
        assert!(matches!(err, TransvalError::SolverError(ref s) if s.contains("timed out")));
    }

    #[test]
    fn test_unsupported_optimization_error() {
        let err = TransvalError::UnsupportedOptimization("loop_unrolling".to_string());
        let msg = err.to_string();
        assert!(
            msg.contains("unsupported optimization"),
            "error message should include variant prefix: {msg}"
        );
        assert!(msg.contains("loop_unrolling"), "error message should include pass name: {msg}");
        assert!(
            matches!(err, TransvalError::UnsupportedOptimization(ref s) if s == "loop_unrolling")
        );
    }

    #[test]
    fn test_unmapped_block_error() {
        let block_id = BlockId(42);
        let err = TransvalError::UnmappedBlock(block_id);
        let msg = err.to_string();
        assert!(
            msg.contains("unmapped source block"),
            "error message should include variant prefix: {msg}"
        );
        assert!(msg.contains("42"), "error message should include block id: {msg}");
        assert!(matches!(err, TransvalError::UnmappedBlock(BlockId(42))));
    }

    #[test]
    fn test_from_translation_validation_error_unmapped_block() {
        let tve = TranslationValidationError::UnmappedBlock(BlockId(7));
        let err: TransvalError = tve.into();
        assert!(
            matches!(err, TransvalError::UnmappedBlock(BlockId(7))),
            "should convert UnmappedBlock: {err:?}"
        );
    }

    #[test]
    fn test_from_translation_validation_error_invalid_relation() {
        let tve = TranslationValidationError::InvalidRelation("bad mapping".to_string());
        let err: TransvalError = tve.into();
        assert!(
            matches!(err, TransvalError::InvalidRelation(ref s) if s == "bad mapping"),
            "should convert InvalidRelation: {err:?}"
        );
    }

    #[test]
    fn test_error_clone() {
        // TransvalError derives Clone -- verify all 4 untested variants clone correctly.
        let errors = vec![
            TransvalError::InvalidRelation("test".into()),
            TransvalError::SolverError("timeout".into()),
            TransvalError::UnsupportedOptimization("pass".into()),
            TransvalError::UnmappedBlock(BlockId(0)),
        ];
        for err in &errors {
            let cloned = err.clone();
            assert_eq!(err.to_string(), cloned.to_string());
        }
    }

    // -----------------------------------------------------------------------
    // Proptest: TransvalError variant coverage
    // -----------------------------------------------------------------------

    mod proptest_transval_error {
        use super::*;
        use proptest::prelude::*;

        fn arb_transval_error() -> impl Strategy<Value = TransvalError> {
            prop_oneof![
                (1..100usize, 1..100usize).prop_map(|(s, t)| {
                    TransvalError::SignatureMismatch { source_args: s, target_args: t }
                }),
                any::<usize>().prop_map(|id| TransvalError::UnmappedBlock(BlockId(id))),
                "[a-z ]{5,50}".prop_map(TransvalError::InvalidRelation),
                "[a-z ]{5,50}".prop_map(TransvalError::EmptyBody),
                "[a-z ]{5,50}".prop_map(TransvalError::SolverError),
                "[a-z ]{5,50}".prop_map(TransvalError::UnsupportedOptimization),
            ]
        }

        proptest! {
            /// Every TransvalError variant produces a non-empty Display string.
            #[test]
            fn all_variants_display_non_empty(err in arb_transval_error()) {
                let msg = err.to_string();
                prop_assert!(!msg.is_empty(), "Display must produce non-empty output");
            }

            /// Every TransvalError variant has a Debug representation.
            #[test]
            fn all_variants_debug_non_empty(err in arb_transval_error()) {
                let dbg = format!("{err:?}");
                prop_assert!(!dbg.is_empty(), "Debug must produce non-empty output");
            }

            /// TransvalError::clone produces an equal value (compared via Debug).
            #[test]
            fn all_variants_clone_eq(err in arb_transval_error()) {
                let cloned = err.clone();
                prop_assert_eq!(format!("{err:?}"), format!("{cloned:?}"));
            }

            /// SignatureMismatch Display includes both argument counts.
            #[test]
            fn signature_mismatch_display(
                source_args in 0..1000usize,
                target_args in 0..1000usize,
            ) {
                let err = TransvalError::SignatureMismatch { source_args, target_args };
                let msg = err.to_string();
                prop_assert!(msg.contains(&source_args.to_string()));
                prop_assert!(msg.contains(&target_args.to_string()));
            }

            /// UnmappedBlock Display includes the variant prefix.
            #[test]
            fn unmapped_block_display(id in any::<usize>()) {
                let err = TransvalError::UnmappedBlock(BlockId(id));
                let msg = err.to_string();
                prop_assert!(msg.contains("unmapped source block"));
            }

            /// SolverError Display includes the detail string.
            #[test]
            fn solver_error_display(detail in "[a-z0-9 ]{1,50}") {
                let err = TransvalError::SolverError(detail.clone());
                let msg = err.to_string();
                prop_assert!(msg.contains("solver error"));
                prop_assert!(msg.contains(&detail));
            }

            /// UnsupportedOptimization Display includes the detail string.
            #[test]
            fn unsupported_optimization_display(detail in "[a-z0-9 ]{1,50}") {
                let err = TransvalError::UnsupportedOptimization(detail.clone());
                let msg = err.to_string();
                prop_assert!(msg.contains("unsupported optimization"));
                prop_assert!(msg.contains(&detail));
            }

            /// InvalidRelation Display includes the detail string.
            #[test]
            fn invalid_relation_display(detail in "[a-z0-9 ]{1,50}") {
                let err = TransvalError::InvalidRelation(detail.clone());
                let msg = err.to_string();
                prop_assert!(msg.contains("invalid simulation relation"));
                prop_assert!(msg.contains(&detail));
            }
        }
    }
}

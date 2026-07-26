// Structured VcGenError with MIR span context for trust_vcgen
//
// Provides a single error enum for the trust_vcgen crate, covering
// unsupported operations, type mismatches, missing function bodies,
// invalid operand references, formula construction failures, and
// invalid VC kinds. Each variant optionally carries MIR source span
// context for diagnostic precision.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::SourceSpan;

// Imports for unified error type — all module-level errors funnel into VcgenError.
use crate::binary_analysis::lifter::LiftError;
use crate::certified_transval::CertificationError;
use crate::chc::ChcError;
use crate::instantiation::InstantiationError;
use crate::interpolant_gen::InterpolantError;
use crate::persistent_specdb::SpecDbError;
use crate::proof_term::ProofError;
use crate::quantifier_tiers::QuantifierError;
use crate::typestate::TransitionError;
use crate::witness_gen::WitnessError;

// Helper to format an optional SourceSpan for error messages.
fn format_span(span: &Option<SourceSpan>) -> String {
    match span {
        Some(s) if !s.file.is_empty() => {
            format!(" at {}:{}:{}", s.file, s.line_start, s.col_start)
        }
        Some(s) => {
            format!(" at <unknown>:{}:{}", s.line_start, s.col_start)
        }
        None => String::new(),
    }
}

/// Errors that can occur during verification condition generation.
///
/// Extended with MIR span context and additional variants for
/// unsupported MIR operations, unsupported types, formula construction
/// failures, and invalid VC kinds.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum VcgenError {
    /// An operation that the VC generator does not yet support was encountered.
    #[error("unsupported operation: {0}")]
    UnsupportedOp(String),

    /// A type mismatch between expected and actual types.
    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    /// The function has no body to generate VCs from.
    #[error("missing function body for `{0}`")]
    MissingBody(String),

    /// An operand references a local that does not exist.
    #[error("invalid local index {index} (function has {num_locals} locals)")]
    InvalidLocal { index: usize, num_locals: usize },

    /// A block reference is invalid.
    #[error("invalid block {block:?} in function `{function}`")]
    InvalidBlock { block: String, function: String },

    /// The serialized Trust MIR body violates a structural invariant required
    /// by positional VC-generation lookups.
    #[error("malformed Trust MIR for `{function}`: {detail}")]
    MalformedMir { function: String, detail: String },

    // New variants with MIR span context below.
    /// A MIR operation that the VC generator cannot translate to a formula.
    ///
    /// Carries the operation name, a human-readable context string, and an
    /// optional MIR source span for diagnostic precision.
    #[error("unsupported MIR operation `{op}` in {context}{}", format_span(.span))]
    UnsupportedMirOp { op: String, context: String, span: Option<SourceSpan> },

    /// A type mismatch with MIR span context.
    ///
    /// Like `TypeMismatch` but includes the surrounding context and optional
    /// source location for richer diagnostics.
    #[error("type mismatch: expected {expected}, got {got} in {context}{}", format_span(.span))]
    TypeMismatchWithContext {
        expected: String,
        got: String,
        context: String,
        span: Option<SourceSpan>,
    },

    /// A type that the VC generator does not support.
    #[error("unsupported type `{ty}` in {context}{}", format_span(.span))]
    UnsupportedType { ty: String, context: String, span: Option<SourceSpan> },

    /// A failure during formula construction (e.g., invalid sort, arity error).
    #[error("formula construction error: {detail}{}", format_span(.span))]
    FormulaConstruction { detail: String, span: Option<SourceSpan> },

    /// An invalid or unrecognized `VcKind` was produced or requested.
    #[error("invalid VC kind `{kind}`: {reason}")]
    InvalidVcKind { kind: String, reason: String },

    // Wrapping variants for module-level error types.
    // Each uses `#[from]` for automatic `Into`/`From` conversion,
    // enabling `?` propagation from module-specific functions into
    // functions returning `Result<T, VcgenError>`.
    /// Error from binary analysis lifter.
    #[error(transparent)]
    Lift(#[from] LiftError),

    /// Error from certified translation validation.
    #[error(transparent)]
    Certification(#[from] CertificationError),

    /// Error from CHC encoding (`chc` module).
    #[error(transparent)]
    Chc(#[from] ChcError),

    // HornClause(CHCError) removed — horn_clause.rs deleted.
    /// Error from quantifier instantiation.
    #[error(transparent)]
    Instantiation(#[from] InstantiationError),

    /// Error from interpolant generation.
    #[error(transparent)]
    Interpolant(#[from] InterpolantError),

    /// Error from persistent spec database.
    #[error(transparent)]
    SpecDb(#[from] SpecDbError),

    /// Error from proof term construction.
    #[error(transparent)]
    Proof(#[from] ProofError),

    /// Error from quantifier tier management.
    #[error(transparent)]
    Quantifier(#[from] QuantifierError),

    // Spacer(SpacerError) removed — spacer_bridge.rs deleted.
    /// Error from typestate transition checking.
    #[error(transparent)]
    Transition(#[from] TransitionError),

    /// Error from witness generation.
    #[error(transparent)]
    Witness(#[from] WitnessError),
}

/// Convenience alias for results using the unified crate error type.
pub type Result<T> = std::result::Result<T, VcgenError>;

// Convenience constructors for common error patterns.
impl VcgenError {
    /// Create an `UnsupportedMirOp` error with a span.
    #[must_use]
    pub fn unsupported_mir_op(
        op: impl Into<String>,
        context: impl Into<String>,
        span: Option<SourceSpan>,
    ) -> Self {
        Self::UnsupportedMirOp { op: op.into(), context: context.into(), span }
    }

    /// Create a `TypeMismatchWithContext` error with a span.
    #[must_use]
    pub fn type_mismatch_ctx(
        expected: impl Into<String>,
        got: impl Into<String>,
        context: impl Into<String>,
        span: Option<SourceSpan>,
    ) -> Self {
        Self::TypeMismatchWithContext {
            expected: expected.into(),
            got: got.into(),
            context: context.into(),
            span,
        }
    }

    /// Create an `UnsupportedType` error with a span.
    #[must_use]
    pub fn unsupported_type(
        ty: impl Into<String>,
        context: impl Into<String>,
        span: Option<SourceSpan>,
    ) -> Self {
        Self::UnsupportedType { ty: ty.into(), context: context.into(), span }
    }

    /// Create a `FormulaConstruction` error with a span.
    #[must_use]
    pub fn formula_construction(detail: impl Into<String>, span: Option<SourceSpan>) -> Self {
        Self::FormulaConstruction { detail: detail.into(), span }
    }

    /// Create an `InvalidVcKind` error.
    #[must_use]
    pub fn invalid_vc_kind(kind: impl Into<String>, reason: impl Into<String>) -> Self {
        Self::InvalidVcKind { kind: kind.into(), reason: reason.into() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests for Display output of all VcgenError variants.

    #[test]
    fn test_vcgen_error_unsupported_op_display() {
        let err = VcgenError::UnsupportedOp("BitReverse".to_string());
        assert_eq!(err.to_string(), "unsupported operation: BitReverse");
    }

    #[test]
    fn test_vcgen_error_type_mismatch_display() {
        let err =
            VcgenError::TypeMismatch { expected: "u32".to_string(), actual: "bool".to_string() };
        assert_eq!(err.to_string(), "type mismatch: expected u32, got bool");
    }

    #[test]
    fn test_vcgen_error_missing_body_display() {
        let err = VcgenError::MissingBody("foo::bar".to_string());
        assert_eq!(err.to_string(), "missing function body for `foo::bar`");
    }

    #[test]
    fn test_vcgen_error_invalid_local_display() {
        let err = VcgenError::InvalidLocal { index: 5, num_locals: 3 };
        assert_eq!(err.to_string(), "invalid local index 5 (function has 3 locals)");
    }

    #[test]
    fn test_vcgen_error_invalid_block_display() {
        let err = VcgenError::InvalidBlock { block: "bb7".to_string(), function: "my_func".into() };
        assert_eq!(err.to_string(), "invalid block \"bb7\" in function `my_func`");
    }

    #[test]
    fn test_vcgen_error_malformed_mir_display() {
        let err = VcgenError::MalformedMir {
            function: "my_func".to_string(),
            detail: "local declaration 1 carries index 7".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "malformed Trust MIR for `my_func`: local declaration 1 carries index 7"
        );
    }

    // Tests for new variants with MIR span context.

    #[test]
    fn test_vcgen_error_unsupported_mir_op_with_span() {
        let span = SourceSpan {
            file: "src/main.rs".to_string(),
            line_start: 42,
            col_start: 5,
            line_end: 42,
            col_end: 20,
        };
        let err = VcgenError::unsupported_mir_op("Discriminant", "match arm lowering", Some(span));
        assert_eq!(
            err.to_string(),
            "unsupported MIR operation `Discriminant` in match arm lowering at src/main.rs:42:5"
        );
    }

    #[test]
    fn test_vcgen_error_unsupported_mir_op_no_span() {
        let err = VcgenError::unsupported_mir_op("InlineAsm", "asm block", None);
        assert_eq!(err.to_string(), "unsupported MIR operation `InlineAsm` in asm block");
    }

    #[test]
    fn test_vcgen_error_type_mismatch_with_context_and_span() {
        let span = SourceSpan {
            file: "lib.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 10,
            col_end: 30,
        };
        let err = VcgenError::type_mismatch_ctx("i64", "f64", "binary add operands", Some(span));
        assert_eq!(
            err.to_string(),
            "type mismatch: expected i64, got f64 in binary add operands at lib.rs:10:1"
        );
    }

    #[test]
    fn test_vcgen_error_type_mismatch_with_context_no_span() {
        let err = VcgenError::type_mismatch_ctx("bool", "u8", "assert condition", None);
        assert_eq!(err.to_string(), "type mismatch: expected bool, got u8 in assert condition");
    }

    #[test]
    fn test_vcgen_error_unsupported_type_with_span() {
        let span = SourceSpan {
            file: "foo.rs".to_string(),
            line_start: 99,
            col_start: 12,
            line_end: 99,
            col_end: 25,
        };
        let err = VcgenError::unsupported_type("dyn Trait", "vtable dispatch", Some(span));
        assert_eq!(
            err.to_string(),
            "unsupported type `dyn Trait` in vtable dispatch at foo.rs:99:12"
        );
    }

    #[test]
    fn test_vcgen_error_unsupported_type_no_span() {
        let err = VcgenError::unsupported_type("fn()", "function pointer cast", None);
        assert_eq!(err.to_string(), "unsupported type `fn()` in function pointer cast");
    }

    #[test]
    fn test_vcgen_error_formula_construction_with_span() {
        let span = SourceSpan {
            file: "arith.rs".to_string(),
            line_start: 7,
            col_start: 3,
            line_end: 7,
            col_end: 18,
        };
        let err = VcgenError::formula_construction("sort mismatch: Int vs Bool in Eq", Some(span));
        assert_eq!(
            err.to_string(),
            "formula construction error: sort mismatch: Int vs Bool in Eq at arith.rs:7:3"
        );
    }

    #[test]
    fn test_vcgen_error_formula_construction_no_span() {
        let err = VcgenError::formula_construction("arity error in And: expected 2, got 0", None);
        assert_eq!(
            err.to_string(),
            "formula construction error: arity error in And: expected 2, got 0"
        );
    }

    #[test]
    fn test_vcgen_error_invalid_vc_kind() {
        let err = VcgenError::invalid_vc_kind("CustomKind", "not recognized by the solver router");
        assert_eq!(
            err.to_string(),
            "invalid VC kind `CustomKind`: not recognized by the solver router"
        );
    }

    #[test]
    fn test_vcgen_error_is_std_error() {
        // Verify VcgenError implements std::error::Error via thiserror.
        let err: Box<dyn std::error::Error> = Box::new(VcgenError::MissingBody("f".to_string()));
        assert!(err.to_string().contains("missing function body"));
    }

    #[test]
    fn test_vcgen_error_debug_format() {
        // Verify Debug is derived and includes variant name.
        let err = VcgenError::InvalidVcKind { kind: "X".to_string(), reason: "Y".to_string() };
        let debug = format!("{err:?}");
        assert!(debug.contains("InvalidVcKind"), "Debug should contain variant name");
    }

    #[test]
    fn test_vcgen_error_span_with_empty_file() {
        // Edge case: span with empty file should use <unknown>.
        let span = SourceSpan {
            file: String::new(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 1,
        };
        let err = VcgenError::unsupported_type("RawPtr", "deref", Some(span));
        assert!(err.to_string().contains("<unknown>:1:1"), "empty file should render as <unknown>");
    }

    #[test]
    fn test_vcgen_error_convenience_constructors_accept_str_refs() {
        // Verify convenience constructors accept &str (impl Into<String>).
        let _e1 = VcgenError::unsupported_mir_op("op", "ctx", None);
        let _e2 = VcgenError::type_mismatch_ctx("a", "b", "c", None);
        let _e3 = VcgenError::unsupported_type("ty", "ctx", None);
        let _e4 = VcgenError::formula_construction("detail", None);
        let _e5 = VcgenError::invalid_vc_kind("k", "r");
    }

    // Tests for #[from] conversions from module-level errors.

    #[test]
    fn test_vcgen_error_from_chc_error() {
        let chc_err = ChcError::NoLoops { function: "foo".into() };
        let vcgen_err: VcgenError = chc_err.into();
        assert!(matches!(vcgen_err, VcgenError::Chc(_)));
        assert!(vcgen_err.to_string().contains("no loops found"));
    }

    // test_vcgen_error_from_spacer_error removed — SpacerError deleted.
    #[test]
    fn test_vcgen_error_question_mark_propagation() {
        // Verify ? operator works for converting module errors into VcgenError.
        fn inner() -> std::result::Result<(), ChcError> {
            Err(ChcError::NoLoops { function: "bar".into() })
        }
        fn outer() -> super::Result<()> {
            inner()?;
            Ok(())
        }
        let result = outer();
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), VcgenError::Chc(_)));
    }

    #[test]
    fn test_vcgen_result_alias() {
        // Verify the Result type alias works.
        let ok: super::Result<i32> = Ok(42);
        #[allow(clippy::unnecessary_literal_unwrap)]
        let val = ok.unwrap();
        assert_eq!(val, 42);
        let err: super::Result<i32> = Err(VcgenError::UnsupportedOp("test".into()));
        assert!(err.is_err());
    }
}

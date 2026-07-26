// trust_vcgen/cross_check/warnings.rs: Warning types for cross-checking
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ---------------------------------------------------------------------------
// Warning types
// ---------------------------------------------------------------------------

/// A warning from cross-checking a verification condition.
///
/// Cross-check warnings indicate potential translation bugs in the VC
/// generator. They do not necessarily mean the VC is wrong, but they
/// flag structural anomalies that warrant investigation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CrossCheckWarning {
    /// A formula variable does not correspond to any function parameter or local.
    UnknownVariable { var_name: String, function: String },
    /// An overflow VC's type bounds do not match the declared operand types.
    OverflowBoundsMismatch { expected_min: i128, expected_max_approx: i128, vc_description: String },
    /// A division-by-zero VC does not test the divisor for equality with zero.
    DivZeroMissingDivisorCheck { function: String },
    /// A formula mixes Sort::Int and Sort::BitVec in comparisons or arithmetic
    /// without explicit conversion.
    SortMismatch { context: String, lhs_sort: SortClass, rhs_sort: SortClass },
    /// An And/Or formula has zero or one child (degenerate).
    DegenerateConnective { connective: String, child_count: usize },
    /// An empty formula (Bool(true) or Bool(false)) used as the entire VC,
    /// which is likely a placeholder or auto-proved stub.
    TrivialFormula { function: String, value: bool },
}

impl CrossCheckWarning {
    /// Human-readable description of this warning.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            CrossCheckWarning::UnknownVariable { var_name, function } => {
                format!(
                    "variable `{var_name}` in VC for `{function}` does not match any function local"
                )
            }
            CrossCheckWarning::OverflowBoundsMismatch {
                expected_min,
                expected_max_approx,
                vc_description,
            } => {
                format!(
                    "overflow bounds mismatch: expected [{expected_min}, ~{expected_max_approx}] \
                     in {vc_description}"
                )
            }
            CrossCheckWarning::DivZeroMissingDivisorCheck { function } => {
                format!(
                    "division-by-zero VC for `{function}` does not contain `divisor == 0` check"
                )
            }
            CrossCheckWarning::SortMismatch { context, lhs_sort, rhs_sort } => {
                format!("sort mismatch in {context}: LHS is {lhs_sort:?}, RHS is {rhs_sort:?}")
            }
            CrossCheckWarning::DegenerateConnective { connective, child_count } => {
                format!("{connective} has {child_count} children (expected >= 2)")
            }
            CrossCheckWarning::TrivialFormula { function, value } => {
                format!(
                    "VC for `{function}` is trivially {value} — \
                     likely a placeholder or auto-proved stub"
                )
            }
        }
    }
}

/// Coarse sort classification for cross-checking.
///
/// We do not need the full Sort here — just enough to detect mismatches
/// between Int-domain and BitVec-domain terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortClass {
    Bool,
    Int,
    BitVec(u32),
    Unknown,
}

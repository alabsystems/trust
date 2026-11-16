// trust_vcgen/coverage.rs: MIR handling coverage matrix
//
// Systematic gap analysis for verifier handling. Enumerates all Rvalue,
// Terminator, BinOp, and UnOp variants from trust-types and records their
// direct-VC, explicit fail-closed, value-formula, or CFG handling.
//
// This module does NOT modify VC generation -- it only analyzes what exists.
//
// Part of #468: MIR handling coverage matrix.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

/// Coverage status for a single variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoverageStatus {
    /// Explicit VC handling exists for this variant. This includes both
    /// semantic safety VCs and fail-closed `UnsupportedMir` rows; neither may
    /// be silently omitted from the report.
    Covered {
        /// Principal implementation paths establishing this classification.
        /// Auxiliary dataflow consumers are intentionally not exhaustive.
        /// The historical field name is retained for public API compatibility;
        /// entries may be validation or fail-closed paths as well as modules.
        modules: Vec<&'static str>,
        /// Principal verification effects: direct VC kinds, explicit
        /// fail-closed rows, or conditional value/guard semantics paired with
        /// those rows. This is a classification witness, not an exhaustive list
        /// of every downstream consumer.
        /// The historical field name is retained for public API compatibility;
        /// entries may include non-VC effects.
        vc_kinds: Vec<&'static str>,
    },
    /// The variant is modeled without a direct safety VC. Depending on the MIR
    /// category, that handling is a value formula or explicit CFG semantics.
    FormulaOnly {
        /// Implementation path that handles the value or CFG semantics.
        module: &'static str,
        /// Why no direct safety VC is needed.
        reason: &'static str,
    },
    /// No direct VC, fail-closed row, value model, or CFG semantics. A gap.
    NotCovered {
        /// Why this is a gap and what would be needed.
        gap_description: &'static str,
        /// Priority: "high" = safety-critical, "medium" = correctness,
        /// "low" = nice-to-have.
        priority: &'static str,
    },
}

impl CoverageStatus {
    /// Returns true if this variant has any VC generation.
    #[must_use]
    pub fn has_vc_generation(&self) -> bool {
        matches!(self, CoverageStatus::Covered { .. })
    }

    /// Returns true if this variant is handled either semantically or through
    /// an explicit fail-closed VC.
    #[must_use]
    pub fn is_handled(&self) -> bool {
        matches!(self, CoverageStatus::Covered { .. } | CoverageStatus::FormulaOnly { .. })
    }

    /// Legacy spelling for [`Self::is_handled`]. The name predates CFG-only
    /// rows such as `Resume`; it reports explicit handling, not necessarily a
    /// literal formula.
    #[must_use]
    pub fn has_formula(&self) -> bool {
        self.is_handled()
    }

    /// Returns true if this is a gap (no coverage at all).
    #[must_use]
    pub fn is_gap(&self) -> bool {
        matches!(self, CoverageStatus::NotCovered { .. })
    }
}

/// Coverage entry for one enum variant.
#[derive(Debug, Clone)]
pub struct VariantCoverage {
    /// Name of the variant (e.g., "BinaryOp", "Goto").
    pub variant_name: &'static str,
    /// Coverage status.
    pub status: CoverageStatus,
}

/// Complete coverage report across all MIR constructs.
#[derive(Debug, Clone)]
pub struct CoverageReport {
    /// Coverage for each Rvalue variant.
    pub rvalue_coverage: Vec<VariantCoverage>,
    /// Coverage for each Terminator variant.
    pub terminator_coverage: Vec<VariantCoverage>,
    /// Coverage for each BinOp variant (overflow/safety checking).
    pub binop_coverage: Vec<VariantCoverage>,
    /// Coverage for each UnOp variant.
    pub unop_coverage: Vec<VariantCoverage>,
}

impl CoverageReport {
    /// Count of Rvalue variants with VC generation.
    #[must_use]
    pub fn rvalue_covered_count(&self) -> usize {
        self.rvalue_coverage.iter().filter(|v| v.status.has_vc_generation()).count()
    }

    /// Count of Rvalue variants with explicit handling.
    #[must_use]
    pub fn rvalue_handled_count(&self) -> usize {
        self.rvalue_coverage.iter().filter(|v| v.status.is_handled()).count()
    }

    /// Legacy spelling for [`Self::rvalue_handled_count`].
    #[must_use]
    pub fn rvalue_formula_count(&self) -> usize {
        self.rvalue_handled_count()
    }

    /// Count of Rvalue variants that are gaps.
    #[must_use]
    pub fn rvalue_gap_count(&self) -> usize {
        self.rvalue_coverage.iter().filter(|v| v.status.is_gap()).count()
    }

    /// Count of Terminator variants with VC generation.
    #[must_use]
    pub fn terminator_covered_count(&self) -> usize {
        self.terminator_coverage.iter().filter(|v| v.status.has_vc_generation()).count()
    }

    /// Count of Terminator variants that are gaps.
    #[must_use]
    pub fn terminator_gap_count(&self) -> usize {
        self.terminator_coverage.iter().filter(|v| v.status.is_gap()).count()
    }

    /// Count of BinOp variants with overflow/safety checking.
    #[must_use]
    pub fn binop_covered_count(&self) -> usize {
        self.binop_coverage.iter().filter(|v| v.status.has_vc_generation()).count()
    }

    /// Count of BinOp variants that are gaps.
    #[must_use]
    pub fn binop_gap_count(&self) -> usize {
        self.binop_coverage.iter().filter(|v| v.status.is_gap()).count()
    }

    /// Count of UnOp variants with explicit VC handling.
    #[must_use]
    pub fn unop_covered_count(&self) -> usize {
        self.unop_coverage.iter().filter(|v| v.status.has_vc_generation()).count()
    }

    /// Count of UnOp variants that are gaps.
    #[must_use]
    pub fn unop_gap_count(&self) -> usize {
        self.unop_coverage.iter().filter(|v| v.status.is_gap()).count()
    }

    /// All identified gaps across all categories.
    #[must_use]
    pub fn all_gaps(&self) -> Vec<&VariantCoverage> {
        self.rvalue_coverage
            .iter()
            .chain(self.terminator_coverage.iter())
            .chain(self.binop_coverage.iter())
            .chain(self.unop_coverage.iter())
            .filter(|v| v.status.is_gap())
            .collect()
    }

    /// Total variant count across all categories.
    #[must_use]
    pub fn total_variant_count(&self) -> usize {
        self.rvalue_coverage.len()
            + self.terminator_coverage.len()
            + self.binop_coverage.len()
            + self.unop_coverage.len()
    }

    /// Total count of variants with explicit handling.
    #[must_use]
    pub fn total_handled_count(&self) -> usize {
        self.rvalue_coverage
            .iter()
            .chain(self.terminator_coverage.iter())
            .chain(self.binop_coverage.iter())
            .chain(self.unop_coverage.iter())
            .filter(|v| v.status.is_handled())
            .count()
    }

    /// Legacy spelling for [`Self::total_handled_count`].
    #[must_use]
    pub fn total_formula_count(&self) -> usize {
        self.total_handled_count()
    }

    /// Total count of gaps across all categories.
    #[must_use]
    pub fn total_gap_count(&self) -> usize {
        self.rvalue_gap_count()
            + self.terminator_gap_count()
            + self.binop_gap_count()
            + self.unop_gap_count()
    }
}

impl fmt::Display for CoverageReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== MIR Handling Coverage Report ===")?;
        writeln!(f)?;

        writeln!(
            f,
            "Rvalue:     {}/{} covered, {}/{} handled, {} gaps",
            self.rvalue_covered_count(),
            self.rvalue_coverage.len(),
            self.rvalue_handled_count(),
            self.rvalue_coverage.len(),
            self.rvalue_gap_count(),
        )?;
        writeln!(
            f,
            "Terminator: {}/{} covered, {} gaps",
            self.terminator_covered_count(),
            self.terminator_coverage.len(),
            self.terminator_gap_count(),
        )?;
        writeln!(
            f,
            "BinOp:      {}/{} covered, {} gaps",
            self.binop_covered_count(),
            self.binop_coverage.len(),
            self.binop_gap_count(),
        )?;
        writeln!(
            f,
            "UnOp:       {}/{} covered, {} gaps",
            self.unop_covered_count(),
            self.unop_coverage.len(),
            self.unop_gap_count(),
        )?;
        writeln!(f)?;

        let gaps = self.all_gaps();
        if gaps.is_empty() {
            writeln!(f, "No gaps identified.")?;
        } else {
            writeln!(f, "Gaps ({}):", gaps.len())?;
            for gap in &gaps {
                if let CoverageStatus::NotCovered { gap_description, priority } = &gap.status {
                    writeln!(f, "  [{priority}] {}: {gap_description}", gap.variant_name)?;
                }
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Coverage analysis functions
// ---------------------------------------------------------------------------

/// Analyze Rvalue variant coverage in the VC generation pipeline.
///
/// Each Rvalue variant is checked against the current `trust_vcgen` handling
/// paths: `generate::safety`, `generate::unsupported`, `rvalue_safety`,
/// `sep_engine`, `guards`, and `chc` (formula translation).
#[must_use]
fn analyze_rvalue_coverage() -> Vec<VariantCoverage> {
    vec![
        VariantCoverage {
            variant_name: "Rvalue::Use",
            status: CoverageStatus::Covered {
                modules: vec!["chc", "rvalue_safety"],
                vc_kinds: vec![
                    "Value copy/move formula",
                    "IndexOutOfBounds for projection-bearing operands",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::BinaryOp",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::overflow_vc"],
                vc_kinds: vec![
                    "ArithmeticOverflow (Add/Sub/Mul)",
                    "DivisionByZero",
                    "RemainderByZero",
                    "ArithmeticOverflow (signed Div/Rem INT_MIN/-1)",
                    "ShiftOverflow (Shl/Shr)",
                    "FloatOverflowToInfinity (float Add/Sub/Mul/Div)",
                    "UnsupportedMir for unmodeled opaque arithmetic operands",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::CheckedBinaryOp",
            status: CoverageStatus::Covered {
                modules: vec!["validate_function", "generate::safety", "generate::checked_vcs"],
                vc_kinds: vec![
                    "ArithmeticOverflow (Add/Sub/Mul WithOverflow carriers)",
                    "MalformedTrustIr for non-Add/Sub/Mul checked carriers \
                     (shift obligations arise only from the plain BinaryOp spelling)",
                    "UnsupportedMir for unmodeled checked carriers or opaque operands",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::UncheckedBinaryOp",
            status: CoverageStatus::Covered {
                modules: vec![
                    "validate_function",
                    "generate::safety",
                    "generate::unsupported",
                    "generate::slice_conversion",
                ],
                vc_kinds: vec![
                    "MalformedTrustIr for non-Add/Sub/Mul/Shl/Shr or invalid integer carriers",
                    "UncheckedArithmeticOverflow (unchecked Add/Sub/Mul; UB on overflow, no runtime guard)",
                    "UnsupportedMir for unchecked Shl/Shr (UB outside 0..BITS; no UB-class shift kind yet)",
                    "UnsupportedMir for an explicit unsupported operand",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::UnaryOp",
            status: CoverageStatus::Covered {
                modules: vec![
                    "chc",
                    "generate::safety",
                    "generate::checked_vcs",
                    "generate::unsupported",
                    "generate::slice_conversion",
                    "guards",
                ],
                vc_kinds: vec![
                    "Not value formula",
                    "NegationOverflow (Neg on signed INT_MIN)",
                    "PtrMetadata slice/str/array length model or fail-closed UnsupportedMir",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Ref",
            status: CoverageStatus::Covered {
                modules: vec!["chc", "rvalue_safety"],
                vc_kinds: vec![
                    "Reference value model",
                    "IndexOutOfBounds for projection-bearing referents",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Cast",
            status: CoverageStatus::Covered {
                modules: vec![
                    "chc",
                    "guards",
                    "generate::checked_vcs",
                    "generate::unsupported",
                    "generate::slice_conversion",
                ],
                vc_kinds: vec![
                    "Defined Rust cast value/range model",
                    "UnsupportedMir for unmodeled carrier or provenance semantics",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Aggregate",
            status: CoverageStatus::Covered {
                modules: vec!["rvalue_safety"],
                vc_kinds: vec!["AggregateArrayLengthMismatch"],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Discriminant",
            status: CoverageStatus::Covered {
                modules: vec!["rvalue_safety"],
                vc_kinds: vec!["InvalidDiscriminant"],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Len",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Len produces a non-negative integer; \
                         no safety violation possible from the read itself",
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Repeat",
            status: CoverageStatus::FormulaOnly {
                module: "guards",
                reason: "Array repetition [val; N] is modeled by guards' conditional \
                         Store-chain seed for eligible array-theory locals (free base \
                         otherwise -- sound, false-FAIL only); the chc scalar bridge \
                         fails closed pending destination-aware array Store semantics",
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::AddressOf",
            status: CoverageStatus::Covered {
                modules: vec!["rvalue_safety", "sep_engine"],
                vc_kinds: vec![
                    "IndexOutOfBounds for projection-bearing sources",
                    "SeparationLogic(AddressOfSourceLiveness)",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::CopyForDeref",
            status: CoverageStatus::Covered {
                modules: vec!["chc", "rvalue_safety"],
                vc_kinds: vec![
                    "Compiler-inserted dereference copy model",
                    "IndexOutOfBounds for projection-bearing places",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::PtrOffset",
            status: CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "generate::slice_conversion"],
                vc_kinds: vec!["UnsupportedMir (pointer-offset bounds unresolved; fail-closed)"],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Unsupported",
            status: CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "generate::slice_conversion", "chc"],
                vc_kinds: vec![
                    "UnsupportedMir (preserved kind/detail/operands; sealed ThreadLocalRef thin-address exception)",
                ],
            },
        },
    ]
}

/// Analyze Terminator variant coverage in the VC generation pipeline.
#[must_use]
fn analyze_terminator_coverage() -> Vec<VariantCoverage> {
    vec![
        VariantCoverage {
            variant_name: "Terminator::Goto",
            status: CoverageStatus::FormulaOnly {
                module: "generate::path_defs",
                reason: "Unconditional CFG edge with no direct safety assertion",
            },
        },
        VariantCoverage {
            variant_name: "Terminator::SwitchInt",
            status: CoverageStatus::FormulaOnly {
                module: "trust_types::model::discovered_clauses / guards / generate::path_defs",
                reason: "SwitchIntMatch/SwitchIntOtherwise are explicit CFG path conditions, not standalone VCs",
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Return",
            status: CoverageStatus::Covered {
                modules: vec!["generate::contract_vcs"],
                vc_kinds: vec!["Postcondition (from #[ensures])"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Call",
            status: CoverageStatus::Covered {
                modules: vec![
                    "generate::callsite",
                    "generate::path_defs",
                    "generate::semantic_guard",
                    "interprocedural",
                ],
                vc_kinds: vec!["Precondition (callee's #[requires])"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::TailCall",
            status: CoverageStatus::Covered {
                modules: vec![
                    "trust_types::model::with_tail_calls_expanded",
                    "generate::callsite",
                    "generate::contract_vcs",
                    "termination",
                    "interprocedural",
                ],
                vc_kinds: vec![
                    "Precondition (callee's #[requires])",
                    "Postcondition (call result returned to caller)",
                    "Direct-self recursion decreases",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Assert",
            status: CoverageStatus::Covered {
                modules: vec![
                    "generate::safety",
                    "generate::checked_vcs",
                    "generate::unsupported",
                    "guards",
                ],
                vc_kinds: vec![
                    "DivisionByZero / RemainderByZero",
                    "ArithmeticOverflow / ShiftOverflow / NegationOverflow",
                    "IndexOutOfBounds (BoundsCheck)",
                    "Assertion (Custom message)",
                    "UnsupportedMir (unmodeled safety assert or operand)",
                    "AssertHolds/AssertFails CFG guard extraction",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Drop",
            status: CoverageStatus::FormulaOnly {
                module: "generate::path_defs",
                reason: "Drop is an explicit normal/unwind CFG effect; compiler-side drop-glue panic obligations are checked separately",
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Opaque",
            status: CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "unsafe_verify::detection"],
                vc_kinds: vec!["UnsupportedMir with preserved CFG successors"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Unreachable",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::overflow_vc"],
                vc_kinds: vec!["Unreachable (reachability check via path conditions)"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Resume",
            status: CoverageStatus::FormulaOnly {
                module: "generate::path_defs",
                reason: "UnwindResume is a terminal re-raise with no in-CFG successor or direct safety assertion; cleanup Drop sites are handled separately",
            },
        },
    ]
}

/// Analyze BinOp variant coverage for overflow and safety checking.
///
/// This specifically checks which operations have *safety* VCs generated
/// (not just formula translation, which all BinOps have via chc.rs).
#[must_use]
fn analyze_binop_coverage() -> Vec<VariantCoverage> {
    vec![
        VariantCoverage {
            variant_name: "BinOp::Add",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["ArithmeticOverflow", "FloatOverflowToInfinity"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Sub",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["ArithmeticOverflow", "FloatOverflowToInfinity"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Mul",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["ArithmeticOverflow", "FloatOverflowToInfinity"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Div",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec![
                    "DivisionByZero",
                    "ArithmeticOverflow (signed INT_MIN / -1)",
                    "FloatOverflowToInfinity (float division magnitude)",
                ],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Rem",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec![
                    "RemainderByZero (integer remainder)",
                    "ArithmeticOverflow (signed INT_MIN % -1)",
                ],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Eq",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Ne",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Lt",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Le",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Gt",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Ge",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Comparison -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::BitAnd",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Bitwise AND -- cannot overflow or trap; \
                         translated to BvAnd formula",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::BitOr",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Bitwise OR -- cannot overflow or trap; \
                         translated to BvOr formula",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::BitXor",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Bitwise XOR -- cannot overflow or trap; \
                         translated to BvXor formula",
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Shl",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["ShiftOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Shr",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["ShiftOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Cmp",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Three-way comparison -- returns -1/0/1, cannot overflow; \
                         translated to ITE formula",
            },
        },
    ]
}

/// Analyze UnOp variant coverage for safety checking.
#[must_use]
fn analyze_unop_coverage() -> Vec<VariantCoverage> {
    vec![
        VariantCoverage {
            variant_name: "UnOp::Not",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Bitwise/logical NOT -- cannot overflow or trap",
            },
        },
        VariantCoverage {
            variant_name: "UnOp::Neg",
            status: CoverageStatus::Covered {
                modules: vec!["generate::safety", "generate::checked_vcs"],
                vc_kinds: vec!["NegationOverflow (signed INT_MIN)"],
            },
        },
        VariantCoverage {
            variant_name: "UnOp::PtrMetadata",
            status: CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "generate::slice_conversion", "guards"],
                vc_kinds: vec![
                    "slice/str/array length via slice_len_formula",
                    "UnsupportedMir for unmodelable raw-pointer or dynamic metadata provenance",
                ],
            },
        },
    ]
}

/// Generate the complete coverage report.
///
/// This is the main entry point for the coverage analysis. It enumerates
/// all MIR construct variants and checks them against the existing VC
/// generation pipeline.
#[must_use]
pub fn coverage_report() -> CoverageReport {
    CoverageReport {
        rvalue_coverage: analyze_rvalue_coverage(),
        terminator_coverage: analyze_terminator_coverage(),
        binop_coverage: analyze_binop_coverage(),
        unop_coverage: analyze_unop_coverage(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exactly_one<'a>(rows: &'a [VariantCoverage], name: &str) -> &'a VariantCoverage {
        let matches = rows.iter().filter(|entry| entry.variant_name == name).collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "{name} must have exactly one coverage row");
        matches[0]
    }

    #[test]
    fn test_coverage_report_generation() {
        let report = coverage_report();

        // These counts come from wildcard-free matches in trust-types, the
        // source crate that owns the enums. A newly added variant fails that
        // crate's build until its source census is updated, then fails this
        // report until it gains a handling row.
        assert_eq!(
            report.rvalue_coverage.len(),
            trust_types::RVALUE_VARIANT_NAMES.len(),
            "Rvalue report must match the source-owned exhaustive census"
        );
        assert_eq!(
            report.terminator_coverage.len(),
            trust_types::TERMINATOR_VARIANT_NAMES.len(),
            "Terminator report must match the source-owned exhaustive census"
        );
        assert_eq!(
            report.binop_coverage.len(),
            trust_types::BINOP_VARIANT_NAMES.len(),
            "BinOp report must match the source-owned exhaustive census"
        );
        assert_eq!(
            report.unop_coverage.len(),
            trust_types::UNOP_VARIANT_NAMES.len(),
            "UnOp report must match the source-owned exhaustive census"
        );
    }

    #[test]
    fn test_variant_name_inventory_is_exact() {
        let report = coverage_report();
        let names = |rows: &[VariantCoverage]| {
            rows.iter().map(|entry| entry.variant_name).collect::<Vec<_>>()
        };

        assert_eq!(names(&report.rvalue_coverage), trust_types::RVALUE_VARIANT_NAMES,);
        assert_eq!(names(&report.terminator_coverage), trust_types::TERMINATOR_VARIANT_NAMES,);
        assert_eq!(names(&report.binop_coverage), trust_types::BINOP_VARIANT_NAMES,);
        assert_eq!(names(&report.unop_coverage), trust_types::UNOP_VARIANT_NAMES,);
    }

    #[test]
    fn test_rvalue_coverage_counts() {
        let report = coverage_report();

        // Explicit/direct or fail-closed VC vc_kinds: every variant except Len
        // and Repeat = 13. PtrOffset and Unsupported are deliberately
        // fail-closed; Use/Ref/CopyForDeref emit projection-safety rows when
        // their places carry projections.
        assert_eq!(report.rvalue_covered_count(), 13, "13 Rvalue variants should have VC handling");

        // Modeled without any direct VC path: Len and Repeat = 2.
        let modeled_no_direct_vc = report.rvalue_handled_count() - report.rvalue_covered_count();
        assert_eq!(
            modeled_no_direct_vc, 2,
            "2 Rvalue variants should be modeled without a direct VC"
        );

        assert_eq!(report.rvalue_gap_count(), 0, "no Rvalue variants should be gaps");
    }

    #[test]
    fn test_terminator_coverage_counts() {
        let report = coverage_report();

        // Direct/fail-closed VC paths: Return, Call, TailCall, Assert, Opaque,
        // Unreachable = 6. Goto, SwitchInt, Drop, and Resume have explicit CFG
        // semantics without a direct VC.
        assert_eq!(
            report.terminator_covered_count(),
            6,
            "6 Terminator variants should have VC generation"
        );

        // No gaps: every remaining terminator has explicit CFG semantics.
        assert_eq!(report.terminator_gap_count(), 0, "no Terminator gaps");
    }

    #[test]
    fn test_terminator_tail_call_is_exactly_covered() {
        let report = coverage_report();
        let tail_call = exactly_one(&report.terminator_coverage, "Terminator::TailCall");
        assert_eq!(
            &tail_call.status,
            &CoverageStatus::Covered {
                modules: vec![
                    "trust_types::model::with_tail_calls_expanded",
                    "generate::callsite",
                    "generate::contract_vcs",
                    "termination",
                    "interprocedural",
                ],
                vc_kinds: vec![
                    "Precondition (callee's #[requires])",
                    "Postcondition (call result returned to caller)",
                    "Direct-self recursion decreases",
                ],
            },
            "TailCall coverage must retain the exact handling-path and direct-VC inventory"
        );
    }

    #[test]
    fn test_newly_enumerated_variant_rows_are_exact() {
        let report = coverage_report();

        assert_eq!(
            &exactly_one(&report.rvalue_coverage, "Rvalue::UncheckedBinaryOp").status,
            &CoverageStatus::Covered {
                modules: vec![
                    "validate_function",
                    "generate::safety",
                    "generate::unsupported",
                    "generate::slice_conversion",
                ],
                vc_kinds: vec![
                    "MalformedTrustIr for non-Add/Sub/Mul/Shl/Shr or invalid integer carriers",
                    "UncheckedArithmeticOverflow (unchecked Add/Sub/Mul; UB on overflow, no runtime guard)",
                    "UnsupportedMir for unchecked Shl/Shr (UB outside 0..BITS; no UB-class shift kind yet)",
                    "UnsupportedMir for an explicit unsupported operand",
                ],
            }
        );
        assert_eq!(
            &exactly_one(&report.rvalue_coverage, "Rvalue::PtrOffset").status,
            &CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "generate::slice_conversion"],
                vc_kinds: vec!["UnsupportedMir (pointer-offset bounds unresolved; fail-closed)",],
            }
        );
        assert_eq!(
            &exactly_one(&report.rvalue_coverage, "Rvalue::Unsupported").status,
            &CoverageStatus::Covered {
                modules: vec!["generate::unsupported", "generate::slice_conversion", "chc"],
                vc_kinds: vec![
                    "UnsupportedMir (preserved kind/detail/operands; sealed ThreadLocalRef thin-address exception)",
                ],
            }
        );
        assert_eq!(
            &exactly_one(&report.terminator_coverage, "Terminator::Resume").status,
            &CoverageStatus::FormulaOnly {
                module: "generate::path_defs",
                reason: "UnwindResume is a terminal re-raise with no in-CFG successor or direct safety assertion; cleanup Drop sites are handled separately",
            }
        );
    }

    #[test]
    fn test_binop_coverage_counts() {
        let report = coverage_report();

        // Covered (have overflow/safety VCs): Add, Sub, Mul, Div, Rem, Shl, Shr = 7
        assert_eq!(report.binop_covered_count(), 7, "7 BinOp variants should have safety VCs");

        // No gaps -- comparisons and bitwise ops have value semantics without direct VCs.
        assert_eq!(
            report.binop_gap_count(),
            0,
            "no BinOp gaps (comparisons and bitwise are inherently safe)"
        );
    }

    #[test]
    fn test_all_gaps_identified() {
        let report = coverage_report();
        let gaps = report.all_gaps();

        assert!(gaps.is_empty(), "coverage report should not contain gaps: {gaps:?}");
    }

    #[test]
    fn test_coverage_status_predicates() {
        let covered = CoverageStatus::Covered {
            modules: vec!["generate::safety"],
            vc_kinds: vec!["ArithmeticOverflow"],
        };
        assert!(covered.has_vc_generation());
        assert!(covered.is_handled());
        assert!(!covered.is_gap());

        let modeled = CoverageStatus::FormulaOnly { module: "chc", reason: "safe" };
        assert!(!modeled.has_vc_generation());
        assert!(modeled.is_handled());
        assert!(!modeled.is_gap());

        let not_covered =
            CoverageStatus::NotCovered { gap_description: "needs work", priority: "high" };
        assert!(!not_covered.has_vc_generation());
        assert!(!not_covered.is_handled());
        assert!(not_covered.is_gap());
    }

    #[test]
    fn test_total_counts() {
        let report = coverage_report();

        // Total = 15 + 10 + 17 + 3 = 45
        assert_eq!(report.total_variant_count(), 45);

        assert_eq!(report.total_gap_count(), 0);

        // Every variant except gaps must have semantic or explicit fail-closed handling.
        assert_eq!(
            report.total_handled_count(),
            report.total_variant_count() - report.total_gap_count(),
            "all non-gap variants should have explicit handling"
        );
    }

    #[test]
    fn test_display_format() {
        let report = coverage_report();
        let display = format!("{report}");

        assert!(display.contains("MIR Handling Coverage Report"), "display should have header");
        assert!(display.contains("Rvalue:"), "display should list Rvalue stats");
        assert!(display.contains("UnOp:"), "display should list UnOp stats");
        assert!(display.contains("No gaps identified."), "display should show gap-free coverage");
    }

    // -----------------------------------------------------------------------
    // Variant-by-variant verification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_rvalue_use_has_projection_safety_coverage() {
        let report = coverage_report();
        let entry = report
            .rvalue_coverage
            .iter()
            .find(|v| v.variant_name == "Rvalue::Use")
            .expect("Rvalue::Use should be in report");
        let CoverageStatus::Covered { modules, vc_kinds } = &entry.status else {
            panic!("Rvalue::Use must retain projection-safety handling")
        };
        assert!(modules.contains(&"rvalue_safety"));
        assert!(vc_kinds.iter().any(|effect| effect.contains("IndexOutOfBounds")));
    }

    #[test]
    fn test_rvalue_binaryop_is_covered() {
        let report = coverage_report();
        let entry = report
            .rvalue_coverage
            .iter()
            .find(|v| v.variant_name == "Rvalue::BinaryOp")
            .expect("Rvalue::BinaryOp should be in report");
        assert!(entry.status.has_vc_generation(), "Rvalue::BinaryOp should have VC generation");
    }

    #[test]
    fn test_rvalue_cast_is_covered() {
        let report = coverage_report();
        let entry = report
            .rvalue_coverage
            .iter()
            .find(|v| v.variant_name == "Rvalue::Cast")
            .expect("Rvalue::Cast should be in report");
        assert!(
            entry.status.has_vc_generation(),
            "Rvalue::Cast must explicitly fail closed when its representation is unmodeled"
        );
        let CoverageStatus::Covered { vc_kinds, .. } = &entry.status else {
            unreachable!("the preceding assertion establishes Covered")
        };
        assert!(
            vc_kinds.iter().all(|kind| !kind.contains("CastOverflow")),
            "defined Rust casts must not be mislabeled as CastOverflow"
        );
        assert!(
            vc_kinds.iter().any(|kind| kind.contains("UnsupportedMir")),
            "unmodeled cast representation/provenance must remain fail-closed"
        );
    }

    #[test]
    fn test_rvalue_addressof_is_covered() {
        let report = coverage_report();
        let entry = report
            .rvalue_coverage
            .iter()
            .find(|v| v.variant_name == "Rvalue::AddressOf")
            .expect("Rvalue::AddressOf should be in report");
        assert!(entry.status.has_vc_generation(), "Rvalue::AddressOf should have VC generation");
    }

    #[test]
    fn test_ptr_metadata_records_modeled_and_fail_closed_paths() {
        let report = coverage_report();
        let entry = report
            .unop_coverage
            .iter()
            .find(|v| v.variant_name == "UnOp::PtrMetadata")
            .expect("UnOp::PtrMetadata should be in report");
        let CoverageStatus::Covered { modules, vc_kinds } = &entry.status else {
            panic!("PtrMetadata must record both modeled and fail-closed handling")
        };
        assert!(modules.contains(&"generate::unsupported"));
        assert!(vc_kinds.iter().any(|kind| kind.contains("slice_len_formula")));
        assert!(vc_kinds.iter().any(|kind| kind.contains("UnsupportedMir")));
    }

    #[test]
    fn test_terminator_assert_is_covered() {
        let report = coverage_report();
        let entry = report
            .terminator_coverage
            .iter()
            .find(|v| v.variant_name == "Terminator::Assert")
            .expect("Terminator::Assert should be in report");
        assert!(entry.status.has_vc_generation(), "Terminator::Assert should have VC generation");
    }

    #[test]
    fn test_terminator_unreachable_is_covered() {
        let report = coverage_report();
        let entry = report
            .terminator_coverage
            .iter()
            .find(|v| v.variant_name == "Terminator::Unreachable")
            .expect("Terminator::Unreachable should be in report");
        assert!(
            entry.status.has_vc_generation(),
            "Terminator::Unreachable should have VC generation"
        );
    }

    #[test]
    fn test_binop_add_sub_mul_covered() {
        let report = coverage_report();
        for name in ["BinOp::Add", "BinOp::Sub", "BinOp::Mul"] {
            let entry = report
                .binop_coverage
                .iter()
                .find(|v| v.variant_name == name)
                .unwrap_or_else(|| panic!("{name} should be in report"));
            assert!(entry.status.has_vc_generation(), "{name} should have overflow VC generation");
        }
    }

    #[test]
    fn test_binop_comparisons_are_modeled_without_direct_vc() {
        let report = coverage_report();
        for name in ["BinOp::Eq", "BinOp::Ne", "BinOp::Lt", "BinOp::Le", "BinOp::Gt", "BinOp::Ge"] {
            let entry = report
                .binop_coverage
                .iter()
                .find(|v| v.variant_name == name)
                .unwrap_or_else(|| panic!("{name} should be in report"));
            assert!(
                matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
                "{name} should be modeled without a direct VC (comparisons are safe)"
            );
        }
    }

    #[test]
    fn test_binop_bitwise_are_modeled_without_direct_vc() {
        let report = coverage_report();
        for name in ["BinOp::BitAnd", "BinOp::BitOr", "BinOp::BitXor"] {
            let entry = report
                .binop_coverage
                .iter()
                .find(|v| v.variant_name == name)
                .unwrap_or_else(|| panic!("{name} should be in report"));
            assert!(
                matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
                "{name} should be modeled without a direct VC (bitwise ops are safe)"
            );
        }
    }

    #[test]
    fn test_binop_cmp_is_modeled_without_direct_vc() {
        let report = coverage_report();
        let entry = report
            .binop_coverage
            .iter()
            .find(|v| v.variant_name == "BinOp::Cmp")
            .expect("BinOp::Cmp should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "BinOp::Cmp should be modeled without a direct VC (three-way comparison is safe)"
        );
    }

    #[test]
    fn test_unop_neg_is_covered() {
        let report = coverage_report();
        let entry = report
            .unop_coverage
            .iter()
            .find(|v| v.variant_name == "UnOp::Neg")
            .expect("UnOp::Neg should be in report");
        assert!(
            entry.status.has_vc_generation(),
            "UnOp::Neg should have VC generation (negation overflow)"
        );
    }

    #[test]
    fn test_unop_not_is_modeled_without_direct_vc() {
        let report = coverage_report();
        let entry = report
            .unop_coverage
            .iter()
            .find(|v| v.variant_name == "UnOp::Not")
            .expect("UnOp::Not should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "UnOp::Not should be modeled without a direct VC"
        );
    }
}

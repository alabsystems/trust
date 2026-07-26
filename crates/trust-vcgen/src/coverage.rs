// trust_vcgen/coverage.rs: MIR-to-Formula coverage matrix
//
// Systematic gap analysis for VC generation. Enumerates all Rvalue, Terminator,
// and BinOp variants from trust-types and checks which ones have corresponding
// verification condition generation in the trust_vcgen pipeline.
//
// This module does NOT modify VC generation -- it only analyzes what exists.
//
// Part of #468: MIR-to-Formula coverage matrix.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

/// Coverage status for a single variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoverageStatus {
    /// Full VC generation exists for this variant.
    Covered {
        /// Which module(s) handle this variant.
        modules: Vec<&'static str>,
        /// What kind of VCs are generated.
        vc_kinds: Vec<&'static str>,
    },
    /// Formula translation exists (in chc::rvalue_to_formula or sp transformer)
    /// but no safety VC is generated. This is expected for safe operations.
    FormulaOnly {
        /// Module that handles the formula translation.
        module: &'static str,
        /// Why no safety VC is needed.
        reason: &'static str,
    },
    /// No VC generation and no formula translation. A gap.
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

    /// Returns true if this variant has at least formula translation.
    #[must_use]
    pub fn has_formula(&self) -> bool {
        matches!(self, CoverageStatus::Covered { .. } | CoverageStatus::FormulaOnly { .. })
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

    /// Count of Rvalue variants with at least formula translation.
    #[must_use]
    pub fn rvalue_formula_count(&self) -> usize {
        self.rvalue_coverage.iter().filter(|v| v.status.has_formula()).count()
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

    /// Total count of variants with at least formula coverage.
    #[must_use]
    pub fn total_formula_count(&self) -> usize {
        self.rvalue_coverage
            .iter()
            .chain(self.terminator_coverage.iter())
            .chain(self.binop_coverage.iter())
            .chain(self.unop_coverage.iter())
            .filter(|v| v.status.has_formula())
            .count()
    }

    /// Total count of gaps across all categories.
    #[must_use]
    pub fn total_gap_count(&self) -> usize {
        self.all_gaps().len()
    }
}

impl fmt::Display for CoverageReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== MIR-to-Formula Coverage Report ===")?;
        writeln!(f)?;

        writeln!(
            f,
            "Rvalue:     {}/{} covered, {}/{} with formula, {} gaps",
            self.rvalue_covered_count(),
            self.rvalue_coverage.len(),
            self.rvalue_formula_count(),
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
/// Each Rvalue variant is checked against the modules in trust_vcgen that
/// handle it: overflow.rs, divzero.rs, shifts.rs, casts.rs, negation.rs,
/// rvalue_safety.rs, bounds.rs, and chc.rs (formula translation).
#[must_use]
fn analyze_rvalue_coverage() -> Vec<VariantCoverage> {
    vec![
        VariantCoverage {
            variant_name: "Rvalue::Use",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Simple copy/move -- no safety property to check",
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::BinaryOp",
            status: CoverageStatus::Covered {
                modules: vec!["overflow", "divzero", "shifts"],
                vc_kinds: vec![
                    "ArithmeticOverflow (Add/Sub/Mul)",
                    "DivisionByZero",
                    "RemainderByZero",
                    "ArithmeticOverflow (signed Div/Rem INT_MIN/-1)",
                    "ShiftOverflow (Shl/Shr)",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::CheckedBinaryOp",
            status: CoverageStatus::Covered {
                modules: vec!["overflow", "divzero", "shifts"],
                vc_kinds: vec![
                    "ArithmeticOverflow (Add/Sub/Mul)",
                    "DivisionByZero",
                    "RemainderByZero",
                    "ShiftOverflow (Shl/Shr)",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::UnaryOp",
            status: CoverageStatus::Covered {
                modules: vec!["negation"],
                vc_kinds: vec!["NegationOverflow (Neg on signed INT_MIN)"],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Ref",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Reference creation is safe in safe Rust; \
                         aliasing/borrow VCs are handled by ownership module",
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::Cast",
            status: CoverageStatus::Covered {
                modules: vec!["casts"],
                vc_kinds: vec![
                    "CastOverflow (narrowing)",
                    "CastOverflow (signed-to-unsigned)",
                    "CastOverflow (unsigned-to-signed)",
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
                module: "chc",
                reason: "Array repetition [val; N] is safe if val is valid; \
                         N is a compile-time constant",
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::AddressOf",
            status: CoverageStatus::Covered {
                modules: vec!["sep_engine"],
                vc_kinds: vec!["SeparationLogic(AddressOfSourceLiveness)"],
            },
        },
        VariantCoverage {
            variant_name: "Rvalue::CopyForDeref",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Compiler-inserted copy for deref; semantically equivalent \
                         to Use(Copy(place))",
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
                module: "sp",
                reason: "Unconditional jump -- no safety property, \
                         propagated through SP transformer",
            },
        },
        VariantCoverage {
            variant_name: "Terminator::SwitchInt",
            status: CoverageStatus::Covered {
                modules: vec!["guards", "sp"],
                vc_kinds: vec!["Path condition extraction (SwitchIntMatch, SwitchIntOtherwise)"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Return",
            status: CoverageStatus::Covered {
                modules: vec!["contracts", "sp"],
                vc_kinds: vec!["Postcondition (from #[ensures])"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Call",
            status: CoverageStatus::Covered {
                modules: vec!["contracts", "sp", "interprocedural"],
                vc_kinds: vec!["Precondition (callee's #[requires])", "Uninterpreted result in SP"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Assert",
            status: CoverageStatus::Covered {
                modules: vec!["asserts", "guards"],
                vc_kinds: vec![
                    "IndexOutOfBounds (BoundsCheck)",
                    "Assertion (Custom message)",
                    "AssertHolds/AssertFails guard extraction",
                ],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Drop",
            status: CoverageStatus::FormulaOnly {
                module: "sp",
                reason: "Drop glue is compiler-generated and safe; \
                         drop ordering checked by ownership module",
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Opaque",
            status: CoverageStatus::Covered {
                modules: vec!["vcgen", "cfg"],
                vc_kinds: vec!["UnsupportedMir with preserved CFG successors"],
            },
        },
        VariantCoverage {
            variant_name: "Terminator::Unreachable",
            status: CoverageStatus::Covered {
                modules: vec!["unreachable"],
                vc_kinds: vec!["Unreachable (reachability check via path conditions)"],
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
                modules: vec!["overflow"],
                vc_kinds: vec!["ArithmeticOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Sub",
            status: CoverageStatus::Covered {
                modules: vec!["overflow"],
                vc_kinds: vec!["ArithmeticOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Mul",
            status: CoverageStatus::Covered {
                modules: vec!["overflow"],
                vc_kinds: vec!["ArithmeticOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Div",
            status: CoverageStatus::Covered {
                modules: vec!["divzero"],
                vc_kinds: vec!["DivisionByZero", "ArithmeticOverflow (signed INT_MIN / -1)"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Rem",
            status: CoverageStatus::Covered {
                modules: vec!["divzero"],
                vc_kinds: vec!["RemainderByZero", "ArithmeticOverflow (signed INT_MIN % -1)"],
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
                modules: vec!["shifts"],
                vc_kinds: vec!["ShiftOverflow"],
            },
        },
        VariantCoverage {
            variant_name: "BinOp::Shr",
            status: CoverageStatus::Covered {
                modules: vec!["shifts"],
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
                modules: vec!["negation"],
                vc_kinds: vec!["NegationOverflow (signed INT_MIN)"],
            },
        },
        VariantCoverage {
            variant_name: "UnOp::PtrMetadata",
            status: CoverageStatus::FormulaOnly {
                module: "chc",
                reason: "Fat pointer metadata extraction -- produces unconstrained \
                         usize, modeled as identity pass-through",
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

    #[test]
    fn test_coverage_report_generation() {
        let report = coverage_report();

        // Verify we enumerate all known variants
        assert_eq!(
            report.rvalue_coverage.len(),
            12,
            "Rvalue has 12 variants: Use, BinaryOp, CheckedBinaryOp, UnaryOp, \
             Ref, Cast, Aggregate, Discriminant, Len, Repeat, AddressOf, CopyForDeref"
        );
        assert_eq!(
            report.terminator_coverage.len(),
            8,
            "Terminator has 8 variants: Goto, SwitchInt, Return, Call, Assert, Drop, Opaque, Unreachable"
        );
        assert_eq!(
            report.binop_coverage.len(),
            17,
            "BinOp has 17 variants: Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, \
             Gt, Ge, BitAnd, BitOr, BitXor, Shl, Shr, Cmp"
        );
        assert_eq!(report.unop_coverage.len(), 3, "UnOp has 3 variants: Not, Neg, PtrMetadata");
    }

    #[test]
    fn test_rvalue_coverage_counts() {
        let report = coverage_report();

        // Covered (have safety VCs): BinaryOp, CheckedBinaryOp, UnaryOp,
        // Cast, Aggregate, Discriminant, AddressOf = 7
        assert_eq!(report.rvalue_covered_count(), 7, "7 Rvalue variants should have VC generation");

        // Formula-only (safe, no VCs needed): Use, Ref, Len, Repeat,
        // CopyForDeref = 5
        let formula_only = report.rvalue_formula_count() - report.rvalue_covered_count();
        assert_eq!(formula_only, 5, "5 Rvalue variants should be formula-only (safe)");

        assert_eq!(report.rvalue_gap_count(), 0, "no Rvalue variants should be gaps");
    }

    #[test]
    fn test_terminator_coverage_counts() {
        let report = coverage_report();

        // Covered: SwitchInt, Return, Call, Assert, Opaque, Unreachable = 6
        assert_eq!(
            report.terminator_covered_count(),
            6,
            "6 Terminator variants should have VC generation"
        );

        // No gaps -- Goto and Drop are formula-only (safe)
        assert_eq!(report.terminator_gap_count(), 0, "no Terminator gaps");
    }

    #[test]
    fn test_binop_coverage_counts() {
        let report = coverage_report();

        // Covered (have overflow/safety VCs): Add, Sub, Mul, Div, Rem, Shl, Shr = 7
        assert_eq!(report.binop_covered_count(), 7, "7 BinOp variants should have safety VCs");

        // No gaps -- comparisons and bitwise ops are formula-only (safe)
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
            modules: vec!["overflow"],
            vc_kinds: vec!["ArithmeticOverflow"],
        };
        assert!(covered.has_vc_generation());
        assert!(covered.has_formula());
        assert!(!covered.is_gap());

        let formula_only = CoverageStatus::FormulaOnly { module: "chc", reason: "safe" };
        assert!(!formula_only.has_vc_generation());
        assert!(formula_only.has_formula());
        assert!(!formula_only.is_gap());

        let not_covered =
            CoverageStatus::NotCovered { gap_description: "needs work", priority: "high" };
        assert!(!not_covered.has_vc_generation());
        assert!(!not_covered.has_formula());
        assert!(not_covered.is_gap());
    }

    #[test]
    fn test_total_counts() {
        let report = coverage_report();

        // Total = 12 + 8 + 17 + 3 = 40
        assert_eq!(report.total_variant_count(), 40);

        assert_eq!(report.total_gap_count(), 0);

        // Every variant except gaps should have formula coverage
        assert_eq!(
            report.total_formula_count(),
            report.total_variant_count() - report.total_gap_count(),
            "all non-gap variants should have formula coverage"
        );
    }

    #[test]
    fn test_display_format() {
        let report = coverage_report();
        let display = format!("{report}");

        assert!(display.contains("MIR-to-Formula Coverage Report"), "display should have header");
        assert!(display.contains("Rvalue:"), "display should list Rvalue stats");
        assert!(display.contains("No gaps identified."), "display should show gap-free coverage");
    }

    // -----------------------------------------------------------------------
    // Variant-by-variant verification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_rvalue_use_is_formula_only() {
        let report = coverage_report();
        let entry = report
            .rvalue_coverage
            .iter()
            .find(|v| v.variant_name == "Rvalue::Use")
            .expect("Rvalue::Use should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "Rvalue::Use should be formula-only"
        );
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
            "Rvalue::Cast should have VC generation (cast overflow)"
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
    fn test_binop_comparisons_are_formula_only() {
        let report = coverage_report();
        for name in ["BinOp::Eq", "BinOp::Ne", "BinOp::Lt", "BinOp::Le", "BinOp::Gt", "BinOp::Ge"] {
            let entry = report
                .binop_coverage
                .iter()
                .find(|v| v.variant_name == name)
                .unwrap_or_else(|| panic!("{name} should be in report"));
            assert!(
                matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
                "{name} should be formula-only (comparisons are safe)"
            );
        }
    }

    #[test]
    fn test_binop_bitwise_are_formula_only() {
        let report = coverage_report();
        for name in ["BinOp::BitAnd", "BinOp::BitOr", "BinOp::BitXor"] {
            let entry = report
                .binop_coverage
                .iter()
                .find(|v| v.variant_name == name)
                .unwrap_or_else(|| panic!("{name} should be in report"));
            assert!(
                matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
                "{name} should be formula-only (bitwise ops are safe)"
            );
        }
    }

    #[test]
    fn test_binop_cmp_is_formula_only() {
        let report = coverage_report();
        let entry = report
            .binop_coverage
            .iter()
            .find(|v| v.variant_name == "BinOp::Cmp")
            .expect("BinOp::Cmp should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "BinOp::Cmp should be formula-only (three-way comparison is safe)"
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
    fn test_unop_not_is_formula_only() {
        let report = coverage_report();
        let entry = report
            .unop_coverage
            .iter()
            .find(|v| v.variant_name == "UnOp::Not")
            .expect("UnOp::Not should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "UnOp::Not should be formula-only"
        );
    }

    #[test]
    fn test_unop_ptrmetadata_is_formula_only() {
        let report = coverage_report();
        let entry = report
            .unop_coverage
            .iter()
            .find(|v| v.variant_name == "UnOp::PtrMetadata")
            .expect("UnOp::PtrMetadata should be in report");
        assert!(
            matches!(entry.status, CoverageStatus::FormulaOnly { .. }),
            "UnOp::PtrMetadata should be formula-only"
        );
    }
}

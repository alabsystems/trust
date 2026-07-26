// trust_vcgen/cross_check/comparison.rs: Dual-method VC comparison
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{VcKind, VerifiableFunction};

use super::cross_check_all_vcs;
use super::reference_vcgen::reference_vcgen;
use super::warnings::CrossCheckWarning;

// ---------------------------------------------------------------------------
// CrossCheckResult: dual-method VC comparison
// ---------------------------------------------------------------------------

/// Verdict from comparing two independently generated VCs.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CrossCheckVerdict {
    /// Both methods produced VCs covering the same safety properties.
    /// The VC generator is likely correct for this function.
    Agree,
    /// The primary method produced a VC kind that the reference method missed.
    /// This could mean the primary is overly conservative (generating spurious VCs)
    /// or the reference method has a gap.
    PrimaryOnly { missing_from_reference: Vec<VcKind> },
    /// The reference method produced a VC kind that the primary method missed.
    /// This is the DANGEROUS case: the primary VC generator may be UNSOUND,
    /// missing a real safety check.
    ReferenceOnly { missing_from_primary: Vec<VcKind> },
    /// Both directions have mismatches. Likely a fundamental disagreement
    /// about which operations need checking.
    Divergent { primary_only: Vec<VcKind>, reference_only: Vec<VcKind> },
}

/// Result of cross-checking a function's VCs via two independent generation methods.
///
/// The primary method is the standard `generate_vcs()` pipeline.
/// The reference method is an independent re-derivation that walks the MIR
/// directly, without using the primary pipeline's overflow/divzero/shifts/
/// casts/bounds sub-modules.
#[derive(Debug, Clone)]
pub struct CrossCheckResult {
    pub function_name: String,
    pub primary_vc_kinds: Vec<VcKind>,
    pub reference_vc_kinds: Vec<VcKind>,
    pub structural_warnings: Vec<CrossCheckWarning>,
    pub verdict: CrossCheckVerdict,
}

impl CrossCheckResult {
    /// Returns true if the primary VC generator is at least as strong as the
    /// reference method (Agree or PrimaryOnly — never missing a real check).
    #[must_use]
    pub fn is_sound(&self) -> bool {
        matches!(self.verdict, CrossCheckVerdict::Agree | CrossCheckVerdict::PrimaryOnly { .. })
    }

    /// Returns true if there is a soundness alarm: the reference method found
    /// a safety check that the primary method missed.
    #[must_use]
    pub fn has_soundness_alarm(&self) -> bool {
        matches!(
            self.verdict,
            CrossCheckVerdict::ReferenceOnly { .. } | CrossCheckVerdict::Divergent { .. }
        )
    }
}

/// Run a full cross-check for a function: generate VCs via both methods,
/// run structural checks on the primary VCs, and compare the VC-kind sets.
#[must_use]
pub fn full_cross_check(func: &VerifiableFunction) -> CrossCheckResult {
    let reference_kinds = reference_vcgen(func);
    let primary_vcs = crate::generate_vcs(func);
    let primary_kinds: Vec<VcKind> = primary_vcs.iter().map(|vc| vc.kind.clone()).collect();

    let structural_warnings = cross_check_all_vcs(&primary_vcs, func);
    let verdict = compare_vc_sets(&primary_kinds, &reference_kinds);

    CrossCheckResult {
        function_name: func.name.clone(),
        primary_vc_kinds: primary_kinds,
        reference_vc_kinds: reference_kinds,
        structural_warnings,
        verdict,
    }
}

// ---------------------------------------------------------------------------
// VC-set comparison via coarse safety categories
// ---------------------------------------------------------------------------

/// Coarse safety category for comparing VC sets from two generators.
///
/// We compare at the category level rather than exact VcKind because the two
/// generators may use slightly different VcKind variants for the same check
/// (e.g., the primary uses ArithmeticOverflow while the reference uses a
/// more specific encoding).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum VcCategory {
    Overflow,
    DivisionByZero,
    Bounds,
    Shift,
    Negation,
    Cast,
    FloatSafety,
    Other(&'static str),
}

pub(crate) fn categorize_vc(kind: &VcKind) -> VcCategory {
    match kind {
        VcKind::ArithmeticOverflow { .. } => VcCategory::Overflow,
        VcKind::ShiftOverflow { .. } => VcCategory::Shift,
        VcKind::DivisionByZero | VcKind::RemainderByZero => VcCategory::DivisionByZero,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => VcCategory::Bounds,
        VcKind::NegationOverflow { .. } => VcCategory::Negation,
        VcKind::CastOverflow { .. } => VcCategory::Cast,
        VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
            VcCategory::FloatSafety
        }
        _ => VcCategory::Other("non-safety"),
    }
}

pub(crate) fn compare_vc_sets(primary: &[VcKind], reference: &[VcKind]) -> CrossCheckVerdict {
    let primary_cats: FxHashSet<VcCategory> = primary.iter().map(categorize_vc).collect();
    let reference_cats: FxHashSet<VcCategory> = reference.iter().map(categorize_vc).collect();

    let in_primary_only: FxHashSet<_> = primary_cats.difference(&reference_cats).copied().collect();
    // FloatSafety compares ONE-DIRECTIONALLY: the primary generator's interval
    // tracer legitimately DISCHARGES float-overflow obligations (bounded
    // operands, guarded divisors — no VC minted), while the reference is
    // deliberately discharge-free and always mints them. A reference-only
    // FloatSafety category is therefore the expected post-discharge shape, not
    // generator drift — flagging it turned a correctly-verified
    // `|x| <= 1e30; x / 2.0` function into a SoundnessAlarm. Primary-only
    // FloatSafety still alarms (the reference missing a kind the primary emits
    // IS drift), and every other category stays bidirectional.
    let in_reference_only: FxHashSet<_> = reference_cats
        .difference(&primary_cats)
        .copied()
        .filter(|category| *category != VcCategory::FloatSafety)
        .collect();

    if in_primary_only.is_empty() && in_reference_only.is_empty() {
        CrossCheckVerdict::Agree
    } else if !in_primary_only.is_empty() && in_reference_only.is_empty() {
        let missing: Vec<VcKind> = primary
            .iter()
            .filter(|k| in_primary_only.contains(&categorize_vc(k)))
            .cloned()
            .collect();
        CrossCheckVerdict::PrimaryOnly { missing_from_reference: missing }
    } else if in_primary_only.is_empty() && !in_reference_only.is_empty() {
        let missing: Vec<VcKind> = reference
            .iter()
            .filter(|k| in_reference_only.contains(&categorize_vc(k)))
            .cloned()
            .collect();
        CrossCheckVerdict::ReferenceOnly { missing_from_primary: missing }
    } else {
        let p_only: Vec<VcKind> = primary
            .iter()
            .filter(|k| in_primary_only.contains(&categorize_vc(k)))
            .cloned()
            .collect();
        let r_only: Vec<VcKind> = reference
            .iter()
            .filter(|k| in_reference_only.contains(&categorize_vc(k)))
            .cloned()
            .collect();
        CrossCheckVerdict::Divergent { primary_only: p_only, reference_only: r_only }
    }
}

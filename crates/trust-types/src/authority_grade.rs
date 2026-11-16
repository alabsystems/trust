// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The three-axis grade of a passing obligation (proven-core plan VF1;
//! soundness-by-construction plan R7, M0.3).
//!
//! A passing row's `TrustStatus`/`TrustProofStrength` says how far a checker
//! went; it does not say WHAT the checked formula was a translation of, nor
//! what else the verdict leans on. R7 states the grade on three axes, never
//! summed into one:
//!
//! * [`GradeEncoding`]: where the checked proposition came from. Only a VC
//!   calculus proved sound in the kernel ([`GradeEncoding::ProvenCalculus`])
//!   makes a kernel check a claim about the program; every encoder in the tree
//!   today is unvalidated, and the E6 rows rest on the E6 reflector's reading
//!   of the body ([`GradeEncoding::E6Reflector`]), not on calculus credit.
//! * [`GradeDischarge`]: who decided it: the Clean kernel over a reconstructed
//!   term, a solver whose proof a strict checker replayed, a solver's own
//!   say-so, a compiler composition of other rows, or nobody (an assumption).
//! * [`GradePremise`]: the named premise classes the row rests on beyond the
//!   shared base (`docs/TCB.md`, "Also in the base, on every path").
//!
//! The compiler states one [`ObligationGrade`] per `ResultProofAuthority`
//! variant (`trust_grade_for_authority`, `trust_verify.rs`), and `docs/TCB.md`'s
//! authority table carries the same triple; `tcb_document_exhaustiveness`
//! holds the two to each other. The grade is disclosure: it is never proof
//! authority, and no gate, cache or codegen decision reads it.

use serde::{Deserialize, Serialize};

/// Where the checked proposition came from (R7 axis 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum GradeEncoding {
    /// A VC calculus proved sound in the Clean kernel over the shipped
    /// generator (VF5): F1's `vc` over SemR, with `vc_sound_F1` and
    /// `compose_F1` admitted through the reference entry with closures ⊆ Ax0.
    /// One authority states it (`CalculusRowProved`), and only with the
    /// reference-entry discharge; its rows count as "proved (calculus)" and,
    /// until the owner's E4.7 ruling ([`E4_7_CALCULUS_ROWS_CERTIFIED`]), never
    /// toward `Certified` totals.
    ProvenCalculus,
    /// A Rust encoder nothing has proved faithful to the program: trust-vcgen
    /// and trust-mir-extract's violation formulas, trust-vc's MIR-memory
    /// engine, the CHC/PDR source-to-native translation.
    UnvalidatedEncoder,
    /// The E6 reflector's reading of the function body (the imported defining
    /// equation an E9 citation is graded against). Trusted Rust, like an
    /// encoder, and never calculus credit.
    E6Reflector,
    /// Nothing was encoded: the row records an assumption.
    NotEncoded,
}

/// Who decided the row (R7 axis 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum GradeDischarge {
    /// The Clean kernel type-checked a reconstructed proof term, AND Clean's
    /// fenced reference entry (`clean_kernel::ReferenceKernel`, theory
    /// `LeanReferenceV1`: Lean 4's kernel theory, `CleanMode::Constructive`,
    /// over a base whose every constant passed the full kernel check) accepted
    /// the same closed judgment and issued its `ReferenceAccepted` token (the
    /// KR0 switch). The only discharge a `Certified` authority states.
    KernelReferenceChecked,
    /// The Clean kernel type-checked a reconstructed proof term (not through
    /// the reference entry).
    KernelReconstructed,
    /// A solver's fresh proof, replayed by a strict proof checker (trusted
    /// code, not a kernel).
    SolverSelfChecked,
    /// A solver's verdict, reported by trusted code that does not replay the
    /// artifact the compiler receives (R7's "solver-said").
    SolverAsserted,
    /// The compiler composed the verdict from other rows' verdicts or a
    /// registry; the composition itself is not checked.
    CompilerComposed,
    /// Nothing was discharged: an assumption, recorded.
    Assumed,
}

/// A named premise class a row rests on beyond the shared base (R7 axis 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum GradePremise {
    /// The E6 parameter view: a frozen shared pointee's field values at entry
    /// are what the function reads (R1).
    ParameterView,
    /// The requires-to-hypothesis link of a conditional citation (OR-A1).
    RequiresLink,
    /// A language premise about the body's reference arguments (`noalias`,
    /// a valid `Box` read through a reference).
    ArgumentPremise,
    /// The crate's type-invariant certificate (TINV).
    TypeInvariantCertificate,
    /// R1's closed-world claim: every caller was enumerated.
    ClosedWorldCallers,
    /// The registry of unconditionally panic-free callees.
    PanicFreeCalleeRegistry,
    /// The sibling rows of the same body, read by their verdict.
    SiblingRows,
    /// The complete exact body-proof group of a source clause.
    BodyProofGroup,
    /// A definition-site `requires`, assumed at entry.
    RequiresAssumedAtEntry,
    /// A callee the user marked `#[trust::assume_total]`.
    UserAssumeTotal,
    /// A sibling row this one rests on is itself conditional (not an all-input
    /// proof: an R1, `assume_total`, argument-premise or type-invariant
    /// premise); that row's own grade names the premise.
    SiblingPremises,
    /// A coroutine resume body's executor-protocol premise: the executor
    /// resumes the body only in the states the resume-state contract names.
    ExecutorProtocol,
    /// VF5: the translation the calculus reads the program through. The
    /// kernel's theorem is about the compiler's trust-ir artifact as SemR's
    /// decoder reads it; that this is what the function does rests on SemR's
    /// faithfulness to the reader and interpreter (trust-ir's differential, not
    /// a proof), on the artifact being the program (RM5's `prod_equiv`, owed),
    /// and on the binary being compiled from it (the F1 lane).
    SemrTranslation,
    /// VF5: κ, the target SemR's theorem is stated for: 64-bit little-endian,
    /// 8-byte pointers, read from the artifact's target record. A row proved at
    /// κ says nothing about another target.
    TargetKappa,
    /// VF5: the closed-world entry premise. The kernel decides that the
    /// module's roots carry no precondition and that every annotated function
    /// is reachable from one (`entriesOK`); that no caller OUTSIDE the module
    /// enters an annotated function is not in the artifact (every Rust
    /// function there has external linkage) and is assumed.
    ClosedWorldEntry,
}

/// One row's grade: the three R7 axes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObligationGrade {
    /// Where the checked proposition came from.
    pub encoding: GradeEncoding,
    /// Who decided it.
    pub discharge: GradeDischarge,
    /// The premise classes it rests on beyond the shared base, in declaration
    /// order; empty when it rests on the shared base alone.
    pub premises: Vec<GradePremise>,
}

/// The owner's E4.7 ruling: whether a "proved (calculus)" row (the VF5
/// authority, `CalculusRowProved`) counts toward `Certified` totals. Not
/// taken: `false`, so the compiler reports such a row `Trusted`
/// (`calculus_row_disposition` in `trust_verify.rs`), every `Certified`
/// summary leaves it out, and it licenses no check elision. Flipping this is
/// decision E4.7 of the proven-core plan; the compiler's
/// `calculus_row_exclusion` tests show what the flip would change.
pub const E4_7_CALCULUS_ROWS_CERTIFIED: bool = false;

/// The premises the VF5 calculus authority states, in declaration order:
/// SemR's reading of the artifact, the target κ, and the closed-world entry.
pub const CALCULUS_ROW_PREMISES: [GradePremise; 3] =
    [GradePremise::SemrTranslation, GradePremise::TargetKappa, GradePremise::ClosedWorldEntry];

/// The (encoding, discharge) pairs a compiler states today: exactly the pairs
/// `trust_grade_for_authority` (`trust_verify.rs`) spells, which
/// `tcb_document_exhaustiveness` holds to this list both ways. A record whose
/// grade names any other pair (a forged or stale one, or calculus credit by
/// any discharge but the reference entry's) is refused by
/// [`ObligationGrade::admitted`].
pub const ADMITTED_AXES: [(GradeEncoding, GradeDischarge); 9] = [
    (GradeEncoding::ProvenCalculus, GradeDischarge::KernelReferenceChecked),
    (GradeEncoding::UnvalidatedEncoder, GradeDischarge::KernelReferenceChecked),
    (GradeEncoding::E6Reflector, GradeDischarge::KernelReferenceChecked),
    (GradeEncoding::UnvalidatedEncoder, GradeDischarge::KernelReconstructed),
    (GradeEncoding::UnvalidatedEncoder, GradeDischarge::SolverSelfChecked),
    (GradeEncoding::UnvalidatedEncoder, GradeDischarge::SolverAsserted),
    (GradeEncoding::UnvalidatedEncoder, GradeDischarge::CompilerComposed),
    (GradeEncoding::E6Reflector, GradeDischarge::KernelReconstructed),
    (GradeEncoding::NotEncoded, GradeDischarge::Assumed),
];

impl ObligationGrade {
    /// The grade with these axes.
    #[must_use]
    pub fn new(
        encoding: GradeEncoding,
        discharge: GradeDischarge,
        premises: &[GradePremise],
    ) -> Self {
        Self { encoding, discharge, premises: premises.to_vec() }
    }

    /// This grade with `premise` added, keeping the premises in declaration
    /// order and each at most once.
    #[must_use]
    pub fn with_premise(mut self, premise: GradePremise) -> Self {
        if let Err(at) = self.premises.binary_search(&premise) {
            self.premises.insert(at, premise);
        }
        self
    }

    /// Whether a record may state this grade: its (encoding, discharge) pair is
    /// one of [`ADMITTED_AXES`] (so calculus credit only as the VF5 authority
    /// states it, and no incoherent pair such as an E6 reading that was merely assumed), and its
    /// premises are in declaration order with none repeated, and a
    /// `proven-calculus` grade states every [`CALCULUS_ROW_PREMISES`].
    ///
    /// # Errors
    /// Why the grade is not admitted.
    pub fn admitted(&self) -> Result<(), String> {
        if !ADMITTED_AXES.contains(&(self.encoding, self.discharge)) {
            return Err(format!(
                "no proof authority states encoding `{}` with discharge `{}`",
                self.encoding.as_str(),
                self.discharge.as_str()
            ));
        }
        // VF5: calculus credit is disclosed with what it rests on. A
        // `proven-calculus` grade that drops SemR's translation, κ or the
        // closed-world entry is not one the authority states.
        if self.encoding == GradeEncoding::ProvenCalculus
            && !CALCULUS_ROW_PREMISES.iter().all(|premise| self.premises.contains(premise))
        {
            return Err(format!(
                "a `proven-calculus` grade states the premises {:?}, got {:?}",
                CALCULUS_ROW_PREMISES.iter().map(|premise| premise.as_str()).collect::<Vec<_>>(),
                self.premises.iter().map(|premise| premise.as_str()).collect::<Vec<_>>()
            ));
        }
        if !self.premises.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(format!(
                "grade premises {:?} are not in declaration order without repeats",
                self.premises.iter().map(|premise| premise.as_str()).collect::<Vec<_>>()
            ));
        }
        Ok(())
    }

    /// Whether the row's credit is calculus credit: a proven encoding,
    /// discharged by the kernel. This is the "proved (calculus)" count.
    #[must_use]
    pub fn is_calculus_proved(&self) -> bool {
        self.encoding == GradeEncoding::ProvenCalculus
            && matches!(
                self.discharge,
                GradeDischarge::KernelReferenceChecked | GradeDischarge::KernelReconstructed
            )
    }
}

impl GradeEncoding {
    /// The serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ProvenCalculus => "proven-calculus",
            Self::UnvalidatedEncoder => "unvalidated-encoder",
            Self::E6Reflector => "e6-reflector",
            Self::NotEncoded => "not-encoded",
        }
    }

    /// Every value, in declaration order.
    pub const ALL: [Self; 4] =
        [Self::ProvenCalculus, Self::UnvalidatedEncoder, Self::E6Reflector, Self::NotEncoded];

    /// The value spelled `text`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|value| value.as_str() == text)
    }
}

impl GradeDischarge {
    /// The serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::KernelReferenceChecked => "kernel-reference-checked",
            Self::KernelReconstructed => "kernel-reconstructed",
            Self::SolverSelfChecked => "solver-self-checked",
            Self::SolverAsserted => "solver-asserted",
            Self::CompilerComposed => "compiler-composed",
            Self::Assumed => "assumed",
        }
    }

    /// Every value, in declaration order.
    pub const ALL: [Self; 6] = [
        Self::KernelReferenceChecked,
        Self::KernelReconstructed,
        Self::SolverSelfChecked,
        Self::SolverAsserted,
        Self::CompilerComposed,
        Self::Assumed,
    ];

    /// The value spelled `text`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|value| value.as_str() == text)
    }
}

impl GradePremise {
    /// The serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ParameterView => "parameter-view",
            Self::RequiresLink => "requires-link",
            Self::ArgumentPremise => "argument-premise",
            Self::TypeInvariantCertificate => "type-invariant-certificate",
            Self::ClosedWorldCallers => "closed-world-callers",
            Self::PanicFreeCalleeRegistry => "panic-free-callee-registry",
            Self::SiblingRows => "sibling-rows",
            Self::BodyProofGroup => "body-proof-group",
            Self::RequiresAssumedAtEntry => "requires-assumed-at-entry",
            Self::UserAssumeTotal => "user-assume-total",
            Self::SiblingPremises => "sibling-premises",
            Self::ExecutorProtocol => "executor-protocol",
            Self::SemrTranslation => "semr-translation",
            Self::TargetKappa => "target-kappa",
            Self::ClosedWorldEntry => "closed-world-entry",
        }
    }

    /// Every value, in declaration order.
    pub const ALL: [Self; 15] = [
        Self::ParameterView,
        Self::RequiresLink,
        Self::ArgumentPremise,
        Self::TypeInvariantCertificate,
        Self::ClosedWorldCallers,
        Self::PanicFreeCalleeRegistry,
        Self::SiblingRows,
        Self::BodyProofGroup,
        Self::RequiresAssumedAtEntry,
        Self::UserAssumeTotal,
        Self::SiblingPremises,
        Self::ExecutorProtocol,
        Self::SemrTranslation,
        Self::TargetKappa,
        Self::ClosedWorldEntry,
    ];

    /// The value spelled `text`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|value| value.as_str() == text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `as_str` spellings are the serde spellings, so a record written by
    /// one and read by the other agrees.
    #[test]
    fn spellings_are_the_serde_spellings() {
        for value in GradeEncoding::ALL {
            assert_eq!(serde_json::to_value(value).unwrap(), value.as_str());
            assert_eq!(GradeEncoding::parse(value.as_str()), Some(value));
        }
        for value in GradeDischarge::ALL {
            assert_eq!(serde_json::to_value(value).unwrap(), value.as_str());
            assert_eq!(GradeDischarge::parse(value.as_str()), Some(value));
        }
        for value in GradePremise::ALL {
            assert_eq!(serde_json::to_value(value).unwrap(), value.as_str());
            assert_eq!(GradePremise::parse(value.as_str()), Some(value));
        }
        assert_eq!(GradeEncoding::parse("certified"), None);
    }

    /// `ALL` lists every variant once, in declaration order: each index is the
    /// variant's ordinal from a wildcard-free match, so a variant dropped from
    /// `ALL` (with the length adjusted) or a new variant left out fails here or
    /// does not compile.
    #[test]
    fn every_all_list_is_exhaustive_and_in_declaration_order() {
        fn encoding(value: GradeEncoding) -> usize {
            match value {
                GradeEncoding::ProvenCalculus => 0,
                GradeEncoding::UnvalidatedEncoder => 1,
                GradeEncoding::E6Reflector => 2,
                GradeEncoding::NotEncoded => 3,
            }
        }
        fn discharge(value: GradeDischarge) -> usize {
            match value {
                GradeDischarge::KernelReferenceChecked => 0,
                GradeDischarge::KernelReconstructed => 1,
                GradeDischarge::SolverSelfChecked => 2,
                GradeDischarge::SolverAsserted => 3,
                GradeDischarge::CompilerComposed => 4,
                GradeDischarge::Assumed => 5,
            }
        }
        fn premise(value: GradePremise) -> usize {
            match value {
                GradePremise::ParameterView => 0,
                GradePremise::RequiresLink => 1,
                GradePremise::ArgumentPremise => 2,
                GradePremise::TypeInvariantCertificate => 3,
                GradePremise::ClosedWorldCallers => 4,
                GradePremise::PanicFreeCalleeRegistry => 5,
                GradePremise::SiblingRows => 6,
                GradePremise::BodyProofGroup => 7,
                GradePremise::RequiresAssumedAtEntry => 8,
                GradePremise::UserAssumeTotal => 9,
                GradePremise::SiblingPremises => 10,
                GradePremise::ExecutorProtocol => 11,
                GradePremise::SemrTranslation => 12,
                GradePremise::TargetKappa => 13,
                GradePremise::ClosedWorldEntry => 14,
            }
        }
        let ordinals = |ordinals: Vec<usize>| {
            assert_eq!(ordinals, (0..ordinals.len()).collect::<Vec<_>>());
        };
        ordinals(GradeEncoding::ALL.into_iter().map(encoding).collect());
        assert_eq!(GradeEncoding::ALL.len(), encoding(GradeEncoding::NotEncoded) + 1);
        ordinals(GradeDischarge::ALL.into_iter().map(discharge).collect());
        assert_eq!(GradeDischarge::ALL.len(), discharge(GradeDischarge::Assumed) + 1);
        ordinals(GradePremise::ALL.into_iter().map(premise).collect());
        assert_eq!(GradePremise::ALL.len(), premise(GradePremise::ClosedWorldEntry) + 1);
        // And the `Ord` the premise ordering rule reads is declaration order.
        assert!(GradePremise::ALL.windows(2).all(|pair| pair[0] < pair[1]));
    }

    /// A grade is admitted only on a pair a compiler states, with ordered,
    /// distinct premises; calculus credit only through the reference entry
    /// (VF5's one authority), never through any other discharge.
    #[test]
    fn admitted_refuses_calculus_incoherent_pairs_and_unordered_premises() {
        for (encoding, discharge) in ADMITTED_AXES {
            let premises: &[GradePremise] = if encoding == GradeEncoding::ProvenCalculus {
                &CALCULUS_ROW_PREMISES
            } else {
                &[]
            };
            assert_eq!(ObligationGrade::new(encoding, discharge, premises).admitted(), Ok(()));
        }
        let refused = |grade: ObligationGrade| assert!(grade.admitted().is_err(), "{grade:?}");
        refused(ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReconstructed,
            &CALCULUS_ROW_PREMISES,
        ));
        // The VF5 pair with a premise dropped: credit without its disclosure.
        refused(ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &[GradePremise::SemrTranslation, GradePremise::TargetKappa],
        ));
        refused(ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &[],
        ));
        for discharge in [
            GradeDischarge::SolverSelfChecked,
            GradeDischarge::SolverAsserted,
            GradeDischarge::CompilerComposed,
            GradeDischarge::Assumed,
        ] {
            refused(ObligationGrade::new(GradeEncoding::ProvenCalculus, discharge, &[]));
        }
        // The VF5 authority's grade is admitted, and is calculus credit.
        let calculus = ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &CALCULUS_ROW_PREMISES,
        );
        assert_eq!(calculus.admitted(), Ok(()));
        assert!(calculus.is_calculus_proved());
        // Its premises out of declaration order are not.
        refused(ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &[GradePremise::ClosedWorldEntry, GradePremise::SemrTranslation],
        ));
        refused(ObligationGrade::new(GradeEncoding::E6Reflector, GradeDischarge::Assumed, &[]));
        refused(ObligationGrade::new(
            GradeEncoding::NotEncoded,
            GradeDischarge::KernelReconstructed,
            &[],
        ));
        let pair = (GradeEncoding::UnvalidatedEncoder, GradeDischarge::CompilerComposed);
        refused(ObligationGrade::new(
            pair.0,
            pair.1,
            &[GradePremise::SiblingRows, GradePremise::PanicFreeCalleeRegistry],
        ));
        refused(ObligationGrade::new(
            pair.0,
            pair.1,
            &[GradePremise::ParameterView, GradePremise::ParameterView],
        ));
        // Control: the same premises in declaration order are admitted.
        assert_eq!(
            ObligationGrade::new(
                pair.0,
                pair.1,
                &[GradePremise::PanicFreeCalleeRegistry, GradePremise::SiblingRows],
            )
            .admitted(),
            Ok(())
        );
    }

    /// `with_premise` keeps declaration order and adds a premise once.
    #[test]
    fn with_premise_keeps_order_and_is_idempotent() {
        let grade = ObligationGrade::new(
            GradeEncoding::UnvalidatedEncoder,
            GradeDischarge::KernelReconstructed,
            &[GradePremise::ExecutorProtocol],
        )
        .with_premise(GradePremise::SiblingRows)
        .with_premise(GradePremise::SiblingRows);
        assert_eq!(grade.premises, [GradePremise::SiblingRows, GradePremise::ExecutorProtocol]);
        assert_eq!(grade.admitted(), Ok(()));
    }

    /// E4.7 is not taken: calculus rows stay out of
    /// `Certified` totals. (The compiler's `calculus_row_exclusion` tests show
    /// the flip's effect on the totals; this pins the shipped value.)
    #[test]
    #[expect(clippy::assertions_on_constants, reason = "pins the shipped value of the ruling")]
    fn e4_7_is_not_taken() {
        assert!(!E4_7_CALCULUS_ROWS_CERTIFIED);
        assert!(CALCULUS_ROW_PREMISES.windows(2).all(|pair| pair[0] < pair[1]));
    }

    /// A grade with a field outside the three axes does not deserialize.
    #[test]
    fn a_grade_with_an_unknown_field_is_refused() {
        let extra = r#"{"encoding":"e6-reflector","discharge":"kernel-reconstructed","premises":[],"credit":"calculus"}"#;
        assert!(serde_json::from_str::<ObligationGrade>(extra).is_err());
    }

    /// Only a proven encoding discharged by the kernel is calculus credit; a
    /// kernel check of an unvalidated encoding is not.
    #[test]
    fn calculus_credit_needs_both_axes() {
        let kernel_over_encoder = ObligationGrade::new(
            GradeEncoding::UnvalidatedEncoder,
            GradeDischarge::KernelReconstructed,
            &[],
        );
        assert!(!kernel_over_encoder.is_calculus_proved());
        let solver_over_calculus = ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::SolverSelfChecked,
            &[],
        );
        assert!(!solver_over_calculus.is_calculus_proved());
        let calculus = ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReconstructed,
            &[],
        );
        assert!(calculus.is_calculus_proved());
        // KR0 switch review (T4): the reference-checked kernel discharge is a
        // kernel discharge too; over an unvalidated encoder it is still not.
        let reference_checked = ObligationGrade::new(
            GradeEncoding::ProvenCalculus,
            GradeDischarge::KernelReferenceChecked,
            &[],
        );
        assert!(reference_checked.is_calculus_proved());
        let reference_over_encoder = ObligationGrade::new(
            GradeEncoding::UnvalidatedEncoder,
            GradeDischarge::KernelReferenceChecked,
            &[],
        );
        assert!(!reference_over_encoder.is_calculus_proved());
    }

    /// A grade missing an axis does not deserialize.
    #[test]
    fn a_grade_without_an_axis_is_refused() {
        let full =
            r#"{"encoding":"e6-reflector","discharge":"kernel-reconstructed","premises":[]}"#;
        assert!(serde_json::from_str::<ObligationGrade>(full).is_ok());
        for partial in [
            r#"{"discharge":"kernel-reconstructed","premises":[]}"#,
            r#"{"encoding":"e6-reflector","premises":[]}"#,
            r#"{"encoding":"e6-reflector","discharge":"kernel-reconstructed"}"#,
        ] {
            assert!(serde_json::from_str::<ObligationGrade>(partial).is_err(), "{partial}");
        }
    }
}

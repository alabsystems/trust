// SPDX-License-Identifier: Apache-2.0
//! Single source of truth for the compiler's Level-0 REFUTATION
//! reclassifications: the non-proved rows the compiler counts as `failed`
//! although no solver returned `Failed` for them.
//!
//! # Why this module exists
//!
//! Three kinds of non-proved Level-0 row are refutations, not coverage gaps:
//!
//!   * a known-panicking unmodeled call (`Option`/`Result` `unwrap`/`expect`
//!     and the rest of the `panic-freedom-unverified` catalogue), and the
//!     SOLVABLE twin of the unwrap-family row (`Call::<m>::panic-freedom`) when
//!     no engine proved it (2026-10-03);
//!   * a strict-L0 SAFETY obligation (overflow, bounds, memory) whose VC kind is
//!     the `UnsupportedMir { kind: "FullVerification::<SafetyKind>" }` the native
//!     round trip mints when the native typed lane returned `Unsupported` for it.
//!     The class is decided by that KIND, so ANY non-proved result on such a VC
//!     — `unknown`, a solver `timeout`, `runtime_checked` — is counted `failed`
//!     (the summary always counted it so); the row's reason keeps which it was;
//!   * the FATAL absent-callee row for an OPEN, uncontracted, unresolved generic
//!     trait dispatch, whose universal panic-freedom claim is constructively
//!     false (a downstream `impl` that panics is the witness).
//!
//! The compiler's per-function Level-0 summary line ("Level 0 summary: N
//! failed, …") and its strict abort counted these rows `failed`. The transport
//! row the same compiler published for the same obligation kept the solver's
//! outcome — `runtime_checked`, `unknown` or `timeout` — and targo's exit-code
//! gate, `report.json` and every saved report count the transport row. So one
//! obligation was "failed" on the compiler's diagnostic and "runtime-checked"
//! in the gate (MEASURED on stage-1 `b0b9258cc9`, 2026-10-02:
//! `impl<T: Clone> Clone for Wrap<T>` printed "Level 0 summary: 1 failed" while
//! its row said `runtime_checked`; under `--allow-l0-gaps` the gate would have
//! conditional-passed it). The two readers re-derived the decision from
//! different data, which is the drift [`crate::tolerance`] exists to prevent
//! for contract panics.
//!
//! Both readers now ask [`L0RefutationClass::of_kind`], and the compiler stamps
//! the answer onto the published row through [`reclassify_published_row`], so
//! the line, the row, the JSON counts and the gate say the same thing. The
//! STRICTER label wins: a refutation is never published as a runtime check.
//!
//! Soundness discipline: this module only ever turns a non-proved, non-failed,
//! non-skipped row into `failed`. It never grants proof credit, never touches a
//! `proved` row, and never turns a `failed` row into anything else.

use crate::{Outcome, TransportObligationResult, VcKind};

/// The marker substring `trust-vcgen` stamps into the `VcKind::UnsupportedMir`
/// kind string it emits for a normally-returning call to a known panicking std
/// method whose internal panic path is unmodeled
/// (`Call::<m>::panic-freedom-unverified`). The full-verifier round trip keeps
/// the original kind inside `detail`, so both fields are read.
pub const KNOWN_PANICKING_CALL_UNSUPPORTED_MARKER: &str = "panic-freedom-unverified";

/// The exact `VcKind::Assertion` messages `trust-vcgen` mints for the SOLVABLE
/// panic-freedom obligation of a std `Option`/`Result` unwrap-family call — the
/// obligation "the receiver's discriminant is not the panicking variant" that
/// replaces the `panic-freedom-unverified` row whenever the receiver's tag is
/// pinned to a term the engine can reason about (a construction, a discriminant
/// read, a std probe, a parameter's entry tag, …). Both are the SAME claim about
/// the SAME call; only the second can be discharged. Minted through
/// [`unwrap_family_panic_freedom_message`], so the classifier below and the mint
/// cannot drift.
pub const UNWRAP_FAMILY_PANIC_FREEDOM_MESSAGES: &[(&str, &str)] = &[
    ("unwrap", "Call::unwrap::panic-freedom"),
    ("expect", "Call::expect::panic-freedom"),
    ("unwrap_err", "Call::unwrap_err::panic-freedom"),
    ("expect_err", "Call::expect_err::panic-freedom"),
];

/// The assertion message for the solvable panic-freedom obligation of the std
/// unwrap-family METHOD (`unwrap`, `expect`, `unwrap_err`, `expect_err`), or
/// `None` for any other method name.
#[must_use]
pub fn unwrap_family_panic_freedom_message(method: &str) -> Option<&'static str> {
    UNWRAP_FAMILY_PANIC_FREEDOM_MESSAGES.iter().find(|(m, _)| *m == method).map(|(_, msg)| *msg)
}

/// Whether a VC is the solvable unwrap-family panic-freedom obligation
/// ([`UNWRAP_FAMILY_PANIC_FREEDOM_MESSAGES`], exact match).
#[must_use]
pub fn is_unwrap_family_panic_freedom_assertion(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::Assertion { message }
            if UNWRAP_FAMILY_PANIC_FREEDOM_MESSAGES.iter().any(|(_, m)| m == message)
    )
}

/// The FATAL absent-callee row's obligation text prefix, up to the callee name.
/// Kept in lockstep with trust-ir-bridge's absent-callee row mint.
pub const ABSENT_CALLEE_ASSUMPTION_CALLEE_PREFIX: &str =
    "[trust-absent-callee-assumption] call to absent callee `";

/// Trust (OD-1, 2026-10-04, open shapes): the FATAL absent-callee spelling of a
/// `Fn`/`FnMut`/`FnOnce::call*` whose receiver the bridge cannot type (a closure
/// type parameter, a `dyn Fn*`), up to the callee name. Kept in lockstep with
/// trust-ir-bridge's untypeable-callable-receiver arm, which mints the same fatal
/// marker under this wording. Its expected-absent and assumed-total twins carry
/// other prefixes and never match.
pub const ABSENT_CALLEE_INDIRECT_CALL_PREFIX: &str =
    "[trust-absent-callee-assumption] indirect call `";

/// The `FullVerification::<kind>` prefixes the native round trip stamps onto an
/// `UnsupportedMir` VC for a STRICT-L0 SAFETY obligation.
pub const NATIVE_UNSUPPORTED_SAFETY_KIND_PREFIXES: &[&str] = &[
    "FullVerification::ArithmeticSafety",
    "FullVerification::BoundsCheck",
    "FullVerification::MemorySafety",
];

/// Why a non-proved Level-0 row is a refutation rather than a coverage gap.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum L0RefutationClass {
    /// A known-panicking call (`unwrap`/`expect`/…) whose panic-freedom no
    /// engine proved: an unmodeled one, or a modeled unwrap-family obligation
    /// left unproved. Assigned by kind; it does NOT assert the panic path is
    /// reachable (only a counterexample on the row does).
    KnownPanickingCall,
    /// A strict-L0 safety obligation the native typed lane could not model.
    NativeUnsupportedSafety,
    /// The fatal absent-callee row of an open, uncontracted dispatch: generic,
    /// virtual on a caller-supplied trait object, or propagated (OD-1 item 14).
    AdversarialOpenDispatch,
}

impl L0RefutationClass {
    /// Classify a VC kind. `is_adversarial_callee` answers whether a callee
    /// NAME (as the absent-callee row spells it) is in the compiler's
    /// adversarial-instantiation witness set for this body; pass `|_| false`
    /// where that set is unknown, which can only withhold the third class.
    ///
    /// The arms are tried in the order the compiler's summary always tried
    /// them, so a kind matching two arms gets the same class it always got.
    #[must_use]
    pub fn of_kind(kind: &VcKind, is_adversarial_callee: impl Fn(&str) -> bool) -> Option<Self> {
        if is_known_panicking_call_unsupported_mir(kind) {
            return Some(Self::KnownPanickingCall);
        }
        // Trust (2026-10-03, unwrap-from-facts): the SOLVABLE twin of the row
        // above. When the engine leaves it unproved — the receiver's tag is free
        // (an unguarded `o.unwrap()`), or the native lane demoted a refutation to
        // `unknown` — the call can still panic, exactly as when the shape was
        // unmodeled. Before, a modeled-but-unproved unwrap published
        // `runtime_checked` while an unmodeled one published `failed`: modelling a
        // shape made its unproved unwraps MORE permissive under
        // `--allow-l0-gaps`. A `Proved` result never reaches this classifier.
        if is_unwrap_family_panic_freedom_assertion(kind) {
            return Some(Self::KnownPanickingCall);
        }
        if is_native_unsupported_strict_l0_safety_mir(kind) {
            return Some(Self::NativeUnsupportedSafety);
        }
        if absent_callee_name(kind).is_some_and(is_adversarial_callee) {
            return Some(Self::AdversarialOpenDispatch);
        }
        None
    }

    /// The reason text a reclassified published row carries.
    #[must_use]
    pub const fn reason(self) -> &'static str {
        match self {
            Self::KnownPanickingCall => {
                // Trust (2026-10-12, known-panicking wording; UF-1(b),
                // JSON-UNWRAP-1, KP-WORDING-1): the class is assigned by KIND to
                // every unproved unwrap-family panic-freedom obligation, including
                // one whose `Err`/`None` comes only from a havoced absent callee
                // (serde_json `json!`'s `to_value(..).unwrap()`), where no engine
                // found a witness. The old "the panic path is reachable" claimed a
                // fact nobody established. Reachability is confirmed only when the
                // row carries a counterexample, which keeps its solver label and
                // reads `refuted`; without one the label is fail-closed and the row
                // reads `unproved_fail_closed`. Outcome and class are unchanged.
                "Level-0 refutation: a known-panicking call whose panic-freedom no engine \
                 established (compiler reclassification by obligation kind: no engine proved \
                 the panic path unreachable; it is confirmed reachable only when this row \
                 carries a counterexample)"
            }
            Self::NativeUnsupportedSafety => {
                "Level-0 refutation: a Level-0 safety obligation the native typed lane could not \
                 model, left unproved by every engine (compiler reclassification by obligation \
                 kind, whatever the final outcome, a timeout included; an unproved \
                 overflow/bounds/memory obligation is not a coverage gap)"
            }
            Self::AdversarialOpenDispatch => {
                // Trust (2026-10-05, rg concrete-misclassified): "trait dispatch",
                // not "generic trait dispatch": since OD-1 item 14 the class also
                // covers a virtual call on a caller-supplied trait object and a
                // still-generic call carrying its callee's refutation, and the old
                // wording made a `dyn`-decided row read as a misclassified call.
                "Level-0 refutation: open, uncontracted trait dispatch (an unresolved generic \
                 call, a virtual call on a caller-supplied trait object, or a call carrying \
                 its callee's such refutation) — panic-freedom over all instantiations is \
                 constructively false (a downstream impl may panic; compiler reclassification)"
            }
        }
    }
}

/// Whether a VC is the `UnsupportedMir` obligation Trust emits for a known
/// panicking unmodeled call.
#[must_use]
pub fn is_known_panicking_call_unsupported_mir(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind.contains(KNOWN_PANICKING_CALL_UNSUPPORTED_MARKER)
                || detail.contains(KNOWN_PANICKING_CALL_UNSUPPORTED_MARKER)
    )
}

/// Whether a VC is an `UnsupportedMir` obligation for a strict-L0 SAFETY
/// property the native typed lane could not model.
#[must_use]
pub fn is_native_unsupported_strict_l0_safety_mir(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::UnsupportedMir { kind, .. }
            if NATIVE_UNSUPPORTED_SAFETY_KIND_PREFIXES
                .iter()
                .any(|prefix| kind.starts_with(prefix))
    )
}

/// The callee a FATAL absent-callee row names, if `kind` is one: the direct
/// spelling ([`ABSENT_CALLEE_ASSUMPTION_CALLEE_PREFIX`]) or, since 2026-10-04, the
/// untypeable-callable-receiver spelling ([`ABSENT_CALLEE_INDIRECT_CALL_PREFIX`]).
/// Before, a non-admitted `<F as FnMut<..>>::call_mut` on a closure type parameter
/// (an open dispatch exactly like `<T as Tr>::m`) carried the second spelling, so
/// the witness set held its name but this reader never found it and the row
/// published `runtime_checked` instead of class (c) `failed`. A name is only ever
/// a witness through the caller's set, so reading a second spelling widens nothing
/// by itself.
#[must_use]
pub fn absent_callee_name(kind: &VcKind) -> Option<&str> {
    let text = match kind {
        VcKind::Assertion { message } => message.as_str(),
        VcKind::UnsupportedMir { detail, .. } => detail.as_str(),
        _ => return None,
    };
    let rest = text
        .split(ABSENT_CALLEE_ASSUMPTION_CALLEE_PREFIX)
        .nth(1)
        .or_else(|| text.split(ABSENT_CALLEE_INDIRECT_CALL_PREFIX).nth(1))?;
    rest.split('`').next()
}

/// Stamp a Level-0 refutation onto a published transport row.
///
/// Only a row the solver left undecided — `runtime_checked`, `unknown`,
/// `timeout`, `unsupported`, `canceled` or `rejected` — is rewritten, to
/// `failed`; a `proved`, `failed` or `skipped` row is returned unchanged
/// (`false`). A skipped row is a recorded assumption whose own ledger entry
/// already carries it; the compiler's summary counts it on that axis, never as
/// a refutation. (The compiler stamps the raw rows, before any assumption
/// rewrite, so it never hands this a skipped row today; the exclusion keeps
/// the function safe for any other caller.) The prior outcome and reason are kept in the new reason, the
/// gap-class attestation (a statement about a completeness GAP) is dropped,
/// and no counterexample or proof evidence is invented.
///
/// The solver label says WHY the row fails (2026-10-03, l0-failure-basis): a row
/// with no counterexample (neither text nor model) is re-labelled
/// [`l0_refutation_solver_label`] (`level0-refutation-fail-closed-over-<prior
/// outcome>:<solver>`), which [`crate::FailureBasis::for_failed_row`] reads as
/// `unproved_fail_closed`. Keeping the verifier's bare label (e.g.
/// `trust-full-verifier`) made every reader call the row `refuted` — a found
/// violation — although no engine refuted it and no witness exists. A row that
/// does carry a counterexample keeps its solver and stays `refuted`. The label is
/// description only: outcome, counts, verdicts and exit codes do not read it.
pub fn reclassify_published_row(
    row: &mut TransportObligationResult,
    class: L0RefutationClass,
) -> bool {
    match row.outcome {
        Outcome::Proved | Outcome::Failed | Outcome::Skipped => return false,
        _ => {}
    }
    let prior = row.outcome;
    let reason = match row.reason.take() {
        Some(previous) if !previous.is_empty() => format!(
            "{}; the verifier's own outcome was `{}`: {previous}",
            class.reason(),
            prior.as_str()
        ),
        _ => format!("{}; the verifier's own outcome was `{}`", class.reason(), prior.as_str()),
    };
    if row.counterexample.is_none() && row.counterexample_model.is_none() {
        row.solver = l0_refutation_solver_label(prior, &row.solver);
    }
    row.outcome = Outcome::Failed;
    row.reason = Some(reason);
    row.gap_class = None;
    row.proof_evidence = None;
    true
}

/// The solver label a Level-0 refutation row without a counterexample is
/// published under: `<`[`crate::L0_REFUTATION_FAIL_CLOSED_SOLVER`]`>-over-<prior
/// outcome>:<prior solver>`, the same `<label>-over-<reason>:<solver>` shape as
/// the unsafe-demand family, so the engine that ran stays in the label (and every
/// substring reader of the solver — e.g. targo's full-verifier recognizer — sees
/// what it saw before).
#[must_use]
pub fn l0_refutation_solver_label(prior: Outcome, solver: &str) -> String {
    format!("{}-over-{}:{solver}", crate::L0_REFUTATION_FAIL_CLOSED_SOLVER, prior.as_str())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn absent_callee_assert(callee: &str) -> VcKind {
        VcKind::Assertion {
            message: format!(
                "{ABSENT_CALLEE_ASSUMPTION_CALLEE_PREFIX}{callee}` (body not in the lowered \
                 bundle) may panic"
            ),
        }
    }

    fn row(outcome: Outcome, kind: VcKind) -> TransportObligationResult {
        TransportObligationResult {
            assumes: Vec::new(),
            obligation_id: Some("vc:f:assertion:0".to_string()),
            claim_digest_sha256: None,
            kind: "assert".to_string(),
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind)),
            description: "assertion".to_string(),
            location: None,
            outcome,
            solver: "trust-full-verifier".to_string(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("native full verifier evidence status: Unsupported".to_string()),
            design_mandate: false,
            gap_class: Some(crate::TransportGapClass::StdPrintDispatch),
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        }
    }

    #[test]
    fn adversarial_open_dispatch_needs_the_witness_set() {
        let kind = absent_callee_assert("<T as core::clone::Clone>::clone");
        assert_eq!(absent_callee_name(&kind), Some("<T as core::clone::Clone>::clone"));
        assert_eq!(
            L0RefutationClass::of_kind(&kind, |name| name == "<T as core::clone::Clone>::clone"),
            Some(L0RefutationClass::AdversarialOpenDispatch)
        );
        // Not in the set (resolved, sealed, contracted): a gap, not a refutation.
        assert_eq!(L0RefutationClass::of_kind(&kind, |_| false), None);
    }

    /// rg concrete-misclassified (2026-10-05): class (c) covers generic, virtual
    /// (`dyn`, OD-1 item 14) and propagated open dispatch, so its reason must not
    /// call every such row "generic" — preview 2 read fold rows decided on a `dyn`
    /// site, whose text names a concrete representative, as concrete callees
    /// misclassified as generic dispatch. The prefix readers grep stays.
    #[test]
    fn adversarial_open_dispatch_reason_names_every_shape_it_covers() {
        let reason = L0RefutationClass::AdversarialOpenDispatch.reason();
        assert!(reason.starts_with("Level-0 refutation: open, uncontracted"), "{reason}");
        assert!(!reason.contains("generic trait dispatch"), "{reason}");
        for shape in ["generic", "virtual call on a caller-supplied trait object", "callee"] {
            assert!(reason.contains(shape), "{shape}: {reason}");
        }
    }

    /// OD-1 open shapes (2026-10-04): the untypeable-callable-receiver spelling of
    /// the fatal marker names its callee too, and is a refutation only through the
    /// witness set; the expected-absent and assumed-total spellings never are.
    #[test]
    fn indirect_call_spelling_names_its_callee() {
        let callee = "<F as core::ops::function::FnMut<(&mut u32,)>>::call_mut";
        let fatal = VcKind::Assertion {
            message: format!(
                "{ABSENT_CALLEE_INDIRECT_CALL_PREFIX}{callee}` through an untypeable callable \
                 receiver (dyn/erased Fn*; callee unknown) may panic"
            ),
        };
        assert_eq!(absent_callee_name(&fatal), Some(callee));
        assert_eq!(
            L0RefutationClass::of_kind(&fatal, |name| name == callee),
            Some(L0RefutationClass::AdversarialOpenDispatch)
        );
        assert_eq!(L0RefutationClass::of_kind(&fatal, |_| false), None);
        for prefix in [
            crate::assumption::EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX,
            crate::assumption::ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX,
        ] {
            let demoted = VcKind::Assertion {
                message: format!(
                    "{prefix}indirect call `{callee}` through an untypeable callable receiver \
                     (dyn/erased Fn*; callee unknown) may panic"
                ),
            };
            assert_eq!(absent_callee_name(&demoted), None);
            assert_eq!(L0RefutationClass::of_kind(&demoted, |_| true), None);
        }
    }

    /// OD-1 phase 1 (2026-10-04): the classifier is unchanged and never classifies an
    /// instance-hypothesis row, in any field and whatever the witness set says. An
    /// admitted site's row is a recorded premise, not a refutation; the class (c)
    /// refutation stays on non-admitted sites only.
    #[test]
    fn instance_hypothesis_rows_are_never_refutations() {
        let callee = "<T as c::Tr>::m";
        let text = format!(
            "{}call `{callee}` at c.rs:3: panic-freedom of this open generic dispatch is assumed \
             for every instance",
            crate::assumption::INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX
        );
        for kind in [
            VcKind::Assertion { message: text.clone() },
            VcKind::UnsupportedMir {
                kind: "assumption:instance-hypothesis".to_string(),
                detail: text.clone(),
            },
        ] {
            assert_eq!(absent_callee_name(&kind), None);
            assert_eq!(L0RefutationClass::of_kind(&kind, |_| true), None);
        }
    }

    #[test]
    fn known_panicking_and_native_unsupported_safety_classify() {
        let unwrap = VcKind::UnsupportedMir {
            kind: "Call::unwrap::panic-freedom-unverified".to_string(),
            detail: String::new(),
        };
        assert_eq!(
            L0RefutationClass::of_kind(&unwrap, |_| true),
            Some(L0RefutationClass::KnownPanickingCall)
        );
        let round_tripped = VcKind::UnsupportedMir {
            kind: "FullVerification::trust.vc::unsupported_mir".to_string(),
            detail: "unsupported MIR `Call::expect::panic-freedom-unverified`".to_string(),
        };
        assert_eq!(
            L0RefutationClass::of_kind(&round_tripped, |_| false),
            Some(L0RefutationClass::KnownPanickingCall)
        );
        let pow = VcKind::UnsupportedMir {
            kind: "FullVerification::ArithmeticSafety".to_string(),
            detail: "u32::pow".to_string(),
        };
        assert_eq!(
            L0RefutationClass::of_kind(&pow, |_| false),
            Some(L0RefutationClass::NativeUnsupportedSafety)
        );
        // An ordinary unmodeled construct and an ordinary assertion are gaps.
        let println = VcKind::UnsupportedMir {
            kind: "Call::std::io::_print".to_string(),
            detail: String::new(),
        };
        assert_eq!(L0RefutationClass::of_kind(&println, |_| true), None);
        let plain = VcKind::Assertion { message: "panic call: core::panicking::panic_fmt".into() };
        assert_eq!(L0RefutationClass::of_kind(&plain, |_| true), None);
    }

    /// 2026-10-03 (unwrap-from-facts): the SOLVABLE unwrap-family obligation is
    /// the same claim as the `panic-freedom-unverified` row, so an unproved one is
    /// the same refutation. Exact messages only: a near miss (another method, a
    /// suffix, a user assertion that merely mentions it) is not classified.
    #[test]
    fn solvable_unwrap_family_obligation_classifies_exactly() {
        for (method, message) in UNWRAP_FAMILY_PANIC_FREEDOM_MESSAGES {
            assert_eq!(unwrap_family_panic_freedom_message(method), Some(*message));
            let kind = VcKind::Assertion { message: (*message).to_string() };
            assert!(is_unwrap_family_panic_freedom_assertion(&kind), "{message}");
            assert_eq!(
                L0RefutationClass::of_kind(&kind, |_| false),
                Some(L0RefutationClass::KnownPanickingCall),
                "{message}"
            );
        }
        for method in ["unwrap_or", "unwrap_unchecked", "abs", "Unwrap", ""] {
            assert_eq!(unwrap_family_panic_freedom_message(method), None, "{method}");
        }
        for message in [
            "Call::unwrap_or::panic-freedom",
            "Call::abs::panic-freedom",
            "Call::unwrap::panic-freedom ",
            "assertion: Call::unwrap::panic-freedom",
            "Call::unwrap::panic-freedom::extra",
        ] {
            let kind = VcKind::Assertion { message: message.to_string() };
            assert!(!is_unwrap_family_panic_freedom_assertion(&kind), "{message}");
            assert_eq!(L0RefutationClass::of_kind(&kind, |_| false), None, "{message}");
        }
        // Only the Assertion kind carries it; the same text elsewhere is not it.
        let other = VcKind::UnsupportedMir {
            kind: "Call::unwrap::panic-freedom".to_string(),
            detail: String::new(),
        };
        assert!(!is_unwrap_family_panic_freedom_assertion(&other));

        // An unproved solvable row is published `failed`, unproved, no witness.
        let mut r = row(
            Outcome::RuntimeChecked,
            VcKind::Assertion { message: "Call::expect::panic-freedom".into() },
        );
        assert!(reclassify_published_row(&mut r, L0RefutationClass::KnownPanickingCall));
        assert_eq!(r.outcome, Outcome::Failed);
        assert_eq!(basis_of(&r), crate::FailureBasis::UnprovedFailClosed);
        // A proved row is never touched.
        let mut p = row(
            Outcome::Proved,
            VcKind::Assertion { message: "Call::unwrap::panic-freedom".into() },
        );
        assert!(!reclassify_published_row(&mut p, L0RefutationClass::KnownPanickingCall));
        assert_eq!(p.outcome, Outcome::Proved);
    }

    #[test]
    fn undecided_rows_become_failed_and_keep_their_history() {
        let class = L0RefutationClass::AdversarialOpenDispatch;
        for outcome in [
            Outcome::RuntimeChecked,
            Outcome::Unknown,
            Outcome::Timeout,
            Outcome::Unsupported,
            Outcome::Canceled,
            Outcome::Rejected,
        ] {
            let mut r = row(outcome, absent_callee_assert("<T as D>::m"));
            assert!(reclassify_published_row(&mut r, class), "{outcome:?}");
            assert_eq!(r.outcome, Outcome::Failed);
            assert_eq!(r.gap_class, None, "a refutation is not a completeness gap");
            assert!(r.counterexample.is_none(), "no counterexample is invented");
            let reason = r.reason.as_deref().unwrap();
            assert!(reason.starts_with(class.reason()), "{reason}");
            assert!(reason.contains(&format!("`{}`", outcome.as_str())), "{reason}");
            assert!(reason.contains("native full verifier evidence status"), "{reason}");
            assert_eq!(
                r.solver,
                format!(
                    "{}-over-{}:trust-full-verifier",
                    crate::L0_REFUTATION_FAIL_CLOSED_SOLVER,
                    outcome.as_str()
                ),
                "the engine that ran stays in the label"
            );
        }
    }

    fn unwrap_kind() -> VcKind {
        VcKind::UnsupportedMir {
            kind: "Call::unwrap::panic-freedom-unverified".to_string(),
            detail: String::new(),
        }
    }

    fn native_unsupported_overflow_kind() -> VcKind {
        VcKind::UnsupportedMir {
            kind: "FullVerification::ArithmeticSafety".to_string(),
            detail: "arithmetic overflow (Mul)".to_string(),
        }
    }

    /// The basis a reader derives from a published row, exactly as targo reads it
    /// (solver label + whether a counterexample exists).
    fn basis_of(r: &TransportObligationResult) -> crate::FailureBasis {
        assert_eq!(r.outcome, Outcome::Failed);
        crate::FailureBasis::for_failed_row(
            &r.solver,
            r.counterexample.is_some() || r.counterexample_model.is_some(),
        )
    }

    /// 2026-10-03 (l0-failure-basis): every Level-0 refutation class, published
    /// WITHOUT a counterexample, reads `unproved_fail_closed` — no engine refuted
    /// it and no witness exists. Before, the row kept `trust-full-verifier` and
    /// every reader called it `refuted`.
    #[test]
    fn every_class_without_a_counterexample_reads_unproved_fail_closed() {
        use crate::FailureBasis::UnprovedFailClosed;
        let cases = [
            (L0RefutationClass::KnownPanickingCall, unwrap_kind()),
            (L0RefutationClass::NativeUnsupportedSafety, native_unsupported_overflow_kind()),
            (
                L0RefutationClass::AdversarialOpenDispatch,
                absent_callee_assert("<T as core::clone::Clone>::clone"),
            ),
        ];
        for (class, kind) in cases {
            assert_eq!(
                L0RefutationClass::of_kind(&kind, |name| name.starts_with("<T as")),
                Some(class)
            );
            for outcome in [Outcome::RuntimeChecked, Outcome::Unknown, Outcome::Timeout] {
                let mut r = row(outcome, kind.clone());
                assert!(reclassify_published_row(&mut r, class), "{class:?} {outcome:?}");
                assert_eq!(basis_of(&r), UnprovedFailClosed, "{class:?} {outcome:?}");
                assert!(
                    crate::ObligationOutcome::failed_from_backend(&r.solver, None)
                        .is_unproved_fail_closed(),
                    "{class:?} {outcome:?}: report.json reads it unproved too"
                );
                assert!(crate::is_fail_closed_solver_label(&r.solver), "{}", r.solver);
            }
        }
    }

    /// REFUTED CONTROL: a row that carries a counterexample (text or model) keeps
    /// its solver and stays `refuted`, and a row an engine itself returned
    /// `failed` is never touched, so it stays `refuted` too.
    #[test]
    fn a_row_with_a_counterexample_or_a_solver_failure_stays_refuted() {
        use crate::FailureBasis::Refuted;
        let class = L0RefutationClass::NativeUnsupportedSafety;

        let mut with_model = row(Outcome::Unknown, native_unsupported_overflow_kind());
        with_model.counterexample_model = Some(crate::Counterexample::new(vec![(
            "x".into(),
            crate::CounterexampleValue::Uint(65_536),
        )]));
        assert!(reclassify_published_row(&mut with_model, class));
        assert_eq!(with_model.solver, "trust-full-verifier", "a witnessed row keeps its solver");
        assert_eq!(basis_of(&with_model), Refuted);

        let mut with_text = row(Outcome::Unknown, native_unsupported_overflow_kind());
        with_text.counterexample = Some("x = 65536".to_string());
        assert!(reclassify_published_row(&mut with_text, class));
        assert_eq!(with_text.solver, "trust-full-verifier");
        assert_eq!(basis_of(&with_text), Refuted);
        // Even read without the text (a reader that only sees the model), the
        // untouched label still says refuted.
        assert_eq!(crate::FailureBasis::for_failed_row(&with_text.solver, false), Refuted);

        let mut solver_failed = row(Outcome::Failed, native_unsupported_overflow_kind());
        assert!(!reclassify_published_row(&mut solver_failed, class));
        assert_eq!(solver_failed.solver, "trust-full-verifier");
        assert_eq!(basis_of(&solver_failed), Refuted);
    }

    #[test]
    fn native_unsupported_safety_is_decided_by_kind_so_a_timeout_is_published_failed() {
        let pow = VcKind::UnsupportedMir {
            kind: "FullVerification::ArithmeticSafety".to_string(),
            detail: "arithmetic overflow (Mul)".to_string(),
        };
        let class = L0RefutationClass::of_kind(&pow, |_| false).unwrap();
        assert_eq!(class, L0RefutationClass::NativeUnsupportedSafety);
        let mut r = row(Outcome::Timeout, pow);
        assert!(reclassify_published_row(&mut r, class));
        assert_eq!(r.outcome, Outcome::Failed);
        let reason = r.reason.as_deref().unwrap();
        assert!(reason.contains("a timeout included"), "{reason}");
        assert!(reason.contains("own outcome was `timeout`"), "{reason}");
    }

    /// 2026-10-12 (KP-WORDING-1): the `KnownPanickingCall` reason states only
    /// what is known. The class is assigned by kind to an unproved unwrap-family
    /// row even when the `Err`/`None` comes only from a havoced absent callee
    /// (no witness), so the reason must not claim reachability; a row that does
    /// carry a counterexample keeps that distinction visible (solver kept,
    /// `refuted`), while the outcome stays `failed` either way.
    #[test]
    fn known_panicking_reason_claims_no_reachability_without_a_counterexample() {
        use crate::FailureBasis::{Refuted, UnprovedFailClosed};
        let class = L0RefutationClass::KnownPanickingCall;
        let text = class.reason();
        assert!(!text.contains("the panic path is reachable"), "{text}");
        assert!(text.contains("no engine proved the panic path unreachable"), "{text}");
        assert!(text.contains("only when this row carries a counterexample"), "{text}");
        assert!(text.starts_with("Level-0 refutation: a known-panicking call"), "{text}");

        // Witness-free (the json! shape): failed, unproved_fail_closed.
        assert_eq!(L0RefutationClass::of_kind(&unwrap_kind(), |_| false), Some(class));
        let mut plain = row(Outcome::RuntimeChecked, unwrap_kind());
        assert!(reclassify_published_row(&mut plain, class));
        assert_eq!(plain.outcome, Outcome::Failed);
        assert_eq!(basis_of(&plain), UnprovedFailClosed);
        assert!(plain.reason.as_deref().unwrap().starts_with(text));

        // Witnessed: still failed, and the basis says refuted.
        let mut witnessed = row(Outcome::Unknown, unwrap_kind());
        witnessed.counterexample = Some("o = None".to_string());
        assert!(reclassify_published_row(&mut witnessed, class));
        assert_eq!(witnessed.outcome, Outcome::Failed);
        assert_eq!(witnessed.solver, "trust-full-verifier");
        assert_eq!(basis_of(&witnessed), Refuted);
    }

    #[test]
    fn decided_and_assumption_rows_are_never_rewritten() {
        for outcome in [Outcome::Proved, Outcome::Failed, Outcome::Skipped] {
            let mut r = row(outcome, absent_callee_assert("<T as D>::m"));
            let before = r.clone();
            assert!(!reclassify_published_row(&mut r, L0RefutationClass::KnownPanickingCall));
            assert_eq!(r, before, "{outcome:?}");
        }
    }
}

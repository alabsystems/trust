// SPDX-License-Identifier: Apache-2.0
//! Single source of truth for classifying whether a non-proved Trust obligation
//! is a DECLARED, tolerable panic versus a genuine refutation.
//!
//! # Why this module exists
//!
//! The question *"is this failed/unproved obligation a deliberately-declared
//! `#[trust::contract_panic]` panic?"* was historically re-derived at
//! four independent sites, each spelling the marker constants
//! ([`crate::assumption`]) inline against a DIFFERENT data shape:
//!
//!   * the compiler's strict-L0 abort gate (over `(VC, VerificationResult)`),
//!   * the compiler's full-verification abort gate + memory-safe UB counter
//!     (over `trust_verifier_api::TrustObligation`),
//!   * the compiler's transport-row reclassification (over
//!     `TransportObligationResult`),
//!   * targo's exit-code partition (over the transport row kind).
//!
//! `trust-types` owned the marker constants but not the classification that
//! reads them, so the constants' anti-drift doctrine did not extend to the
//! predicate. Colocating classification here makes marker interpretation
//! consistent: every gate projects its own data into [`ContractPanicView`] and
//! asks this module. Policy remains deliberately separate: only advisory
//! Survey mode may admit a declared panic as visible conditional evidence;
//! strict mode fails it, and memory-safe mode excludes it from safe-panic
//! demotion.
//!
//! Soundness discipline: an UNUSED annotation (matched no panic) is classified
//! [`ContractPanicClass::Unused`] and is NEVER declared — it stays a refutation
//! (anti-abuse: an annotation may not sit dormant waiting to mask a future
//! panic). A declared panic is never a proof. It is conditional evidence only
//! in advisory survey mode; strict and memory-safe modes reject it.

use crate::assumption;

/// How a non-proved obligation relates to the `#[trust::contract_panic]`
/// declared-panic mechanism. Exhaustive over the contract-panic axis; every
/// other reason an obligation is non-proved (a genuine refutation, an assumption
/// gap, a coverage gap) is [`ContractPanicClass::None`] here and classified on
/// its own axis by the caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractPanicClass {
    /// Not a contract panic. Classify by the other axes, or it is a genuine
    /// refutation / coverage gap that fails closed.
    None,
    /// A reachable panic CALL whose enclosing function's
    /// `#[trust::contract_panic(message_contains = "…")]` payload matched a
    /// const-str operand of THAT panic call — a DELIBERATELY declared panic.
    Matched,
    /// The whole-function panic-freedom AGGREGATE, established to be covered
    /// entirely by declared contract panics (every reachable panic is matched,
    /// no undeclared panic remains). A declared panic at the function level.
    AggregateCovered,
    /// A `#[trust::contract_panic]` annotation whose `message_contains` payload
    /// matched NO panic call in the function. An annotation on panic-free code
    /// is an ERROR — this is a REFUTATION, never a tolerable declared panic.
    Unused,
}

impl ContractPanicClass {
    /// True for a genuinely DECLARED panic (a matched call or an aggregate
    /// covered by matched calls). A declared panic is eligible for a visible
    /// CONDITIONAL pass only in advisory survey mode, never a proof, and is
    /// inadmissible in strict and memory-safe modes. `None` and `Unused` are not
    /// declared.
    #[must_use]
    pub fn is_declared(self) -> bool {
        matches!(self, ContractPanicClass::Matched | ContractPanicClass::AggregateCovered)
    }

    /// The row `kind` string a rewritten transport row carries for this class,
    /// or `None` when the class does not rewrite a row (`None` variant). The one
    /// place the class → row-kind mapping is spelled, so the compiler's rewrite
    /// and targo's partition cannot disagree on the wire kind.
    #[must_use]
    pub fn transport_row_kind(self) -> Option<&'static str> {
        match self {
            ContractPanicClass::None => None,
            ContractPanicClass::Matched => Some(assumption::CONTRACT_PANIC_MATCHED_ROW_KIND),
            ContractPanicClass::AggregateCovered => {
                Some(assumption::CONTRACT_PANIC_AGGREGATE_ROW_KIND)
            }
            ContractPanicClass::Unused => Some(assumption::CONTRACT_PANIC_UNUSED_ROW_KIND),
        }
    }
}

/// A call-site's cheap projection of one obligation onto the contract-panic
/// axis. Every gate builds this from its own data shape — a `VcKind::Assertion`
/// message, a `TrustObligation.description`, or a `TransportObligationResult`'s
/// `description` + `kind` — and asks [`classify_contract_panic`].
pub struct ContractPanicView<'a> {
    /// The obligation's descriptive text into which trust-vcgen stamps the
    /// contract-panic markers: a VC Assertion message, a TrustObligation
    /// description, or a transport-row description.
    pub text: &'a str,
    /// The transport/targo row `kind`, when the site operates on a row that may
    /// already carry a rewritten `contract-panic:` kind. `None` for raw
    /// VC/obligation sites (the markers live in `text` there).
    pub row_kind: Option<&'a str>,
}

/// Classify a NON-PROVED obligation on the contract-panic axis from its
/// projected view. The caller is responsible for only asking about non-proved
/// obligations (a proved obligation is not a tolerance question).
///
/// Order is load-bearing and fail-closed:
///   1. the UNUSED marker wins first — an unused annotation must never be
///      mistaken for a declared panic (it is a refutation);
///   2. then the MATCHED call marker in the text;
///   3. then a rewritten row kind (aggregate-covered, or any `contract-panic:`
///      prefix → matched);
///   4. otherwise it is not a contract panic.
#[must_use]
pub fn classify_contract_panic(view: &ContractPanicView<'_>) -> ContractPanicClass {
    // (1) Anti-abuse: an annotation that matched no panic is an ERROR. Checked
    // FIRST so it can never be laundered into a declared panic by a later arm.
    if view.text.contains(assumption::CONTRACT_PANIC_UNUSED_VC_MARKER)
        || view.row_kind == Some(assumption::CONTRACT_PANIC_UNUSED_ROW_KIND)
    {
        return ContractPanicClass::Unused;
    }
    // (2) A declared, message-matched reachable panic CALL (marker in the text).
    if view.text.contains(assumption::CONTRACT_PANIC_VC_MARKER) {
        return ContractPanicClass::Matched;
    }
    // (3) An already-rewritten transport row carries its class in the kind.
    if let Some(kind) = view.row_kind {
        if kind == assumption::CONTRACT_PANIC_AGGREGATE_ROW_KIND {
            return ContractPanicClass::AggregateCovered;
        }
        // Any other `contract-panic:` prefix is a matched call. NB: the UNUSED
        // row kind is `contract-panic-unused` (dash, not colon) so it does NOT
        // match this prefix and was already caught in (1).
        if kind.starts_with(assumption::CONTRACT_PANIC_ROW_KIND_PREFIX) {
            return ContractPanicClass::Matched;
        }
    }
    ContractPanicClass::None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn view(text: &str) -> ContractPanicView<'_> {
        ContractPanicView { text, row_kind: None }
    }
    fn row<'a>(text: &'a str, kind: &'a str) -> ContractPanicView<'a> {
        ContractPanicView { text, row_kind: Some(kind) }
    }

    #[test]
    fn matched_marker_in_text_is_declared() {
        let msg = format!(
            "{}panic call: core::panicking::panic_fmt",
            assumption::CONTRACT_PANIC_VC_MARKER
        );
        let c = classify_contract_panic(&view(&msg));
        assert_eq!(c, ContractPanicClass::Matched);
        assert!(c.is_declared());
    }

    #[test]
    fn unused_marker_is_a_refutation_not_declared() {
        let msg =
            format!("{}annotation matched no panic", assumption::CONTRACT_PANIC_UNUSED_VC_MARKER);
        let c = classify_contract_panic(&view(&msg));
        assert_eq!(c, ContractPanicClass::Unused);
        assert!(!c.is_declared(), "unused annotation must never be a declared panic");
    }

    #[test]
    fn unused_wins_even_if_matched_marker_also_present() {
        // Defensive: if both markers ever co-occur, the anti-abuse UNUSED wins.
        let msg = format!(
            "{}{}both",
            assumption::CONTRACT_PANIC_UNUSED_VC_MARKER,
            assumption::CONTRACT_PANIC_VC_MARKER
        );
        assert_eq!(classify_contract_panic(&view(&msg)), ContractPanicClass::Unused);
    }

    #[test]
    fn plain_refutation_is_none() {
        let c = classify_contract_panic(&view("assertion: index out of bounds"));
        assert_eq!(c, ContractPanicClass::None);
        assert!(!c.is_declared());
    }

    #[test]
    fn aggregate_row_kind_is_declared() {
        let c = classify_contract_panic(&row(
            "panic freedom: no assertion, `unreachable!`, or panic is reachable",
            assumption::CONTRACT_PANIC_AGGREGATE_ROW_KIND,
        ));
        assert_eq!(c, ContractPanicClass::AggregateCovered);
        assert!(c.is_declared());
    }

    #[test]
    fn matched_row_kind_is_declared() {
        let c =
            classify_contract_panic(&row("whatever", assumption::CONTRACT_PANIC_MATCHED_ROW_KIND));
        assert_eq!(c, ContractPanicClass::Matched);
        assert!(c.is_declared());
    }

    #[test]
    fn unused_row_kind_is_a_refutation() {
        // `contract-panic-unused` (dash) must NOT be swept up by the
        // `contract-panic:` (colon) prefix into a declared panic.
        let c =
            classify_contract_panic(&row("whatever", assumption::CONTRACT_PANIC_UNUSED_ROW_KIND));
        assert_eq!(c, ContractPanicClass::Unused);
        assert!(!c.is_declared());
    }

    #[test]
    fn row_kind_to_class_roundtrips() {
        assert_eq!(
            ContractPanicClass::Matched.transport_row_kind(),
            Some(assumption::CONTRACT_PANIC_MATCHED_ROW_KIND)
        );
        assert_eq!(
            ContractPanicClass::AggregateCovered.transport_row_kind(),
            Some(assumption::CONTRACT_PANIC_AGGREGATE_ROW_KIND)
        );
        assert_eq!(
            ContractPanicClass::Unused.transport_row_kind(),
            Some(assumption::CONTRACT_PANIC_UNUSED_ROW_KIND)
        );
        assert_eq!(ContractPanicClass::None.transport_row_kind(), None);
    }
}

//! The single per-obligation outcome taxonomy.
//!
//! Trust decides one thing about every verification obligation, and it decides
//! it once. Before this module the same decision was spelled independently on
//! each side of every boundary — a `String` on the compiler→targo transport, a
//! private enum in the report DTOs, another in the engine boundary, another in
//! targo's own pipeline — so the two ends of Trust's own protocol could disagree
//! by a typo and the disagreement would surface as a silent misclassification
//! rather than a build failure. [`Outcome`] is the vocabulary all of them share.
//!
//! # Why these variants and not fewer
//!
//! An outcome is proof-relevant: downstream gates, publication floors, and the
//! `unknown`/`skipped`/`timed_out` accounting all branch on it. Two spellings
//! may only be merged when they mean the same thing to every one of those
//! consumers. Each variant below survives because at least one consumer would
//! lose information if it were folded into a neighbour:
//!
//! * [`Outcome::Proved`] — discharged with live verifier authority. The only
//!   favorable outcome; assurance (solver-backed vs kernel-certified) is a
//!   separate axis carried by `ProofStrength`, never by this enum.
//! * [`Outcome::Failed`] — refuted. A counterexample exists.
//! * [`Outcome::Unknown`] — attempted, undecided. The obligation was encoded
//!   and handed to a decision procedure that came back without an answer.
//! * [`Outcome::Timeout`] — attempted, abandoned on the time budget. Distinct
//!   from `Unknown`: the same claim under a larger budget may still decide, so a
//!   scheduler that raises limits and retries needs to tell the two apart.
//! * [`Outcome::RuntimeChecked`] — not statically discharged; a runtime check
//!   monitors the property instead. This is execution evidence, never proof
//!   credit, and it must not be laundered into either `Proved` or `Unknown`.
//! * [`Outcome::Skipped`] — deliberately not attempted, on a recorded
//!   assumption (definition-entry and assumed-total-callee rows). Distinct from
//!   `Unknown`: no decision procedure ran, so the residual risk is an admitted
//!   assumption rather than solver incompleteness, and the assumption ledger
//!   keys on exactly this.
//! * [`Outcome::Unsupported`] — outside the backend's encodable fragment. No
//!   solver budget can help, because nothing was ever encoded; a capability gap
//!   is reported and fixed differently from an incomplete solver.
//! * [`Outcome::Canceled`] — stopped from outside (cancellation request).
//!   Distinct from `Timeout`: no resource limit was reached, so an unchanged
//!   retry can succeed.
//! * [`Outcome::Rejected`] — a backend produced evidence and validation refused
//!   it. Distinct from `Unsupported`: the backend claimed capability it did not
//!   have, which is a defect signal rather than a coverage signal.
//!
//! # Reading old spellings
//!
//! Serialization is canonical and single-valued: an `Outcome` is only ever
//! written as [`Outcome::as_str`]. Deserialization is deliberately more
//! forgiving, because saved reports predate this type and spell the same
//! outcomes as `timed_out`, `timedout`, `TIMED-OUT`, `cancelled`, `skip`, and so
//! on. [`Outcome::parse`] normalizes case and `-`/`_` separators and accepts
//! every historical spelling, so stored evidence keeps deserializing without
//! being rewritten. An outcome this type does not recognize is an error, not a
//! guess — the transport consumer's parse-failure path already fails closed, so
//! surfacing protocol drift is strictly safer than picking a bucket for it.

use std::fmt;
use std::str::FromStr;

use serde::de::{Error as DeError, Unexpected};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// What Trust concluded about one verification obligation.
///
/// See the [module documentation](self) for why each variant is distinct and
/// for the compatibility rules governing its serialized form.
// Deliberately not `Ord`: the variants have no severity order. Declaration
// order would supply one anyway, and a comparison that silently means
// "declared earlier" is how a gate ends up ranking a timeout above a
// refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Outcome {
    /// Discharged with live verifier authority.
    Proved,
    /// Refuted; a counterexample exists.
    Failed,
    /// Encoded and attempted, but no decision procedure decided it.
    Unknown,
    /// Attempted and abandoned on the time budget.
    Timeout,
    /// Not statically discharged; a runtime check monitors the property.
    RuntimeChecked,
    /// Deliberately not attempted, on a recorded assumption.
    Skipped,
    /// Outside the backend's encodable fragment; nothing was ever encoded.
    Unsupported,
    /// Stopped from outside before any limit was reached.
    Canceled,
    /// Evidence was produced and validation refused it.
    Rejected,
}

impl Outcome {
    /// The canonical serialized spelling. This is the only spelling Trust
    /// writes, on every wire and in every report.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Timeout => "timeout",
            Self::RuntimeChecked => "runtime_checked",
            Self::Skipped => "skipped",
            Self::Unsupported => "unsupported",
            Self::Canceled => "canceled",
            Self::Rejected => "rejected",
        }
    }

    /// Parse any spelling Trust has ever written for an outcome.
    ///
    /// Case and `-`/`_`/whitespace separators are normalized away first, so a
    /// report written by an older toolchain (`TIMED-OUT`, `timedOut`,
    /// `runtime-checked`, `cancelled`) reads back as the outcome it recorded.
    /// Anything else is refused rather than bucketed, so protocol drift cannot
    /// masquerade as a known outcome.
    #[must_use]
    pub fn parse(raw: &str) -> Option<Self> {
        let mut normalized = String::with_capacity(raw.len());
        for ch in raw.trim().chars() {
            if ch.is_ascii_alphanumeric() {
                normalized.push(ch.to_ascii_lowercase());
            } else if ch == '_' || ch == '-' || ch.is_ascii_whitespace() {
                // Separator spellings are equivalent: `timed_out`, `timed-out`,
                // and `timedout` are the same recorded outcome.
            } else {
                return None;
            }
        }
        // Only spellings Trust has actually written are accepted. A synonym no
        // producer emits (`proven`, `refuted`) would not add compatibility — it
        // would let a word from some *other* taxonomy be read as an obligation
        // outcome, which is the failure this type exists to prevent.
        Some(match normalized.as_str() {
            "proved" => Self::Proved,
            "failed" => Self::Failed,
            "unknown" => Self::Unknown,
            // `timed_out` is the summary-bucket name, written into rows by
            // producers that reused the bucket's spelling.
            "timeout" | "timedout" => Self::Timeout,
            "runtimechecked" => Self::RuntimeChecked,
            "skipped" => Self::Skipped,
            "unsupported" => Self::Unsupported,
            "canceled" | "cancelled" => Self::Canceled,
            "rejected" => Self::Rejected,
            _ => return None,
        })
    }

    /// The obligation was discharged. The single favorable outcome.
    #[must_use]
    pub const fn is_proved(self) -> bool {
        matches!(self, Self::Proved)
    }

    /// The obligation was refuted.
    #[must_use]
    pub const fn is_failed(self) -> bool {
        matches!(self, Self::Failed)
    }

    /// A runtime check stands in for a static proof.
    #[must_use]
    pub const fn is_runtime_checked(self) -> bool {
        matches!(self, Self::RuntimeChecked)
    }

    /// No decision procedure ran, because an assumption was admitted instead.
    #[must_use]
    pub const fn is_skipped(self) -> bool {
        matches!(self, Self::Skipped)
    }

    /// The obligation was abandoned on the time budget.
    #[must_use]
    pub const fn is_timeout(self) -> bool {
        matches!(self, Self::Timeout)
    }
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for Outcome {
    type Err = UnknownOutcome;

    fn from_str(raw: &str) -> Result<Self, Self::Err> {
        Self::parse(raw).ok_or_else(|| UnknownOutcome(raw.to_string()))
    }
}

/// A spelling that no released Trust toolchain has ever written for an outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownOutcome(pub String);

impl fmt::Display for UnknownOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unrecognized verification outcome `{}`", self.0)
    }
}

impl std::error::Error for UnknownOutcome {}

impl Serialize for Outcome {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for Outcome {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = String::deserialize(deserializer)?;
        Self::parse(&raw)
            .ok_or_else(|| DeError::invalid_value(Unexpected::Str(&raw), &"a verification outcome"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: &[Outcome] = &[
        Outcome::Proved,
        Outcome::Failed,
        Outcome::Unknown,
        Outcome::Timeout,
        Outcome::RuntimeChecked,
        Outcome::Skipped,
        Outcome::Unsupported,
        Outcome::Canceled,
        Outcome::Rejected,
    ];

    #[test]
    fn canonical_spelling_round_trips() {
        for &outcome in ALL {
            assert_eq!(Outcome::parse(outcome.as_str()), Some(outcome));
            let json = serde_json::to_string(&outcome).expect("serialize outcome");
            assert_eq!(json, format!("\"{}\"", outcome.as_str()));
            assert_eq!(
                serde_json::from_str::<Outcome>(&json).expect("deserialize outcome"),
                outcome
            );
        }
    }

    #[test]
    fn canonical_spellings_are_distinct() {
        let mut seen = std::collections::BTreeSet::new();
        for &outcome in ALL {
            assert!(seen.insert(outcome.as_str()), "duplicate spelling {outcome}");
        }
    }

    #[test]
    fn legacy_spellings_read_back_as_the_outcome_they_recorded() {
        for (raw, expected) in [
            ("timed_out", Outcome::Timeout),
            ("timedout", Outcome::Timeout),
            ("TIMED-OUT", Outcome::Timeout),
            ("Timeout", Outcome::Timeout),
            ("runtime-checked", Outcome::RuntimeChecked),
            ("RUNTIME_CHECKED", Outcome::RuntimeChecked),
            ("cancelled", Outcome::Canceled),
            ("PROVED", Outcome::Proved),
            (" failed ", Outcome::Failed),
        ] {
            assert_eq!(Outcome::parse(raw), Some(expected), "parsing {raw}");
            assert_eq!(
                serde_json::from_str::<Outcome>(&format!("\"{raw}\"")).expect("legacy spelling"),
                expected
            );
        }
    }

    #[test]
    fn legacy_spellings_are_never_written_back() {
        let restored: Outcome = serde_json::from_str("\"timed_out\"").expect("legacy spelling");
        assert_eq!(serde_json::to_string(&restored).expect("serialize"), "\"timeout\"");
    }

    #[test]
    fn an_unrecognized_spelling_is_refused_not_bucketed() {
        assert_eq!(Outcome::parse("almost_proved"), None);
        assert_eq!(Outcome::parse(""), None);
        assert_eq!(Outcome::parse("proved!"), None);
        assert!(serde_json::from_str::<Outcome>("\"almost_proved\"").is_err());
    }

    /// Words that name a conclusion in some *other* Trust taxonomy — binary
    /// verification statuses, scorecard columns — are not obligation outcomes.
    /// Accepting them would import a foreign vocabulary's meaning under this
    /// type's name.
    #[test]
    fn a_neighbouring_taxonomys_word_is_not_an_outcome() {
        for foreign in ["proven", "refuted", "fail", "pass", "ok", "excepted", "planned"] {
            assert_eq!(Outcome::parse(foreign), None, "`{foreign}` is not an outcome");
        }
    }

    /// Exactly one outcome is favorable. Every predicate that gates proof
    /// credit reads `is_proved`, so a second variant answering `true` here
    /// would grant credit everywhere at once.
    #[test]
    fn exactly_one_outcome_is_favorable() {
        assert_eq!(ALL.iter().filter(|outcome| outcome.is_proved()).count(), 1);
        for &outcome in ALL {
            let predicates = [
                outcome.is_proved(),
                outcome.is_failed(),
                outcome.is_runtime_checked(),
                outcome.is_skipped(),
                outcome.is_timeout(),
            ];
            assert!(
                predicates.iter().filter(|held| **held).count() <= 1,
                "{outcome} answers more than one classification predicate"
            );
        }
    }
}

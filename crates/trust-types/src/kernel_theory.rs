// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The kernel theory and environment a `Certified` row was checked in (the
//! KR0 switch, proven-core plan increment 2).
//!
//! A `Certified` row's evidence names the theory the Clean kernel checked it
//! in and the environment it checked it against, as the Clean reference
//! entry's token (`clean_kernel::ReferenceAccepted`) states them. The values
//! here are wire MIRRORS of `clean_kernel::TheoryId` and
//! `clean_kernel::EnvDigest`: trust-types is a leaf crate that the Clean
//! workspace itself depends on, so it cannot name Clean's types. The only
//! producer of a populated value is `trust-certify`, which reads it off a
//! `ReferenceAccepted` token (`trust_certify::reference_mint`); nothing parses
//! a theory out of a solver string.
//!
//! Fail closed by construction: [`crate::ProofEvidence`] carries both as
//! `#[serde(default)]` options, so a row written before the switch reads both
//! as `None`, and `ProofEvidence::is_certified` is false for it.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The reduction theory a `Certified` row's kernel check ran in. Mirrors
/// `clean_kernel::TheoryId`; the spelling is the serialized form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum KernelTheoryId {
    /// Lean 4's kernel theory as the Clean reference entry fixes it
    /// (`clean_kernel::TheoryId::LeanReferenceV1`): the fourteen `Nat` literal
    /// extensions and the string-literal expansion, in `CleanMode::Constructive`.
    LeanReferenceV1,
}

impl KernelTheoryId {
    /// The serialized spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LeanReferenceV1 => "lean-reference-v1",
        }
    }
}

/// The environment a `Certified` row's kernel check ran against: the Clean
/// reference entry's environment digest (`clean_kernel::EnvDigest`), carried
/// as 64 lowercase hex digits on the wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KernelEnvDigest(pub [u8; 32]);

impl KernelEnvDigest {
    /// The lowercase hex spelling.
    #[must_use]
    pub fn to_hex(&self) -> String {
        crate::digest::lowercase_hex(&self.0)
    }

    /// Parse exactly 64 lowercase hex digits.
    #[must_use]
    pub fn from_hex(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        if bytes.len() != 64 {
            return None;
        }
        let nibble = |b: u8| match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            _ => None,
        };
        let mut out = [0u8; 32];
        for (i, pair) in bytes.chunks_exact(2).enumerate() {
            out[i] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
        }
        Some(Self(out))
    }
}

impl Serialize for KernelEnvDigest {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_hex())
    }
}

impl<'de> Deserialize<'de> for KernelEnvDigest {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let text = String::deserialize(deserializer)?;
        Self::from_hex(&text).ok_or_else(|| {
            serde::de::Error::custom("a kernel environment digest is 64 lowercase hex digits")
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theory_spelling_is_pinned() {
        assert_eq!(
            serde_json::to_string(&KernelTheoryId::LeanReferenceV1).unwrap(),
            "\"lean-reference-v1\""
        );
        assert_eq!(KernelTheoryId::LeanReferenceV1.as_str(), "lean-reference-v1");
    }

    /// Fail closed: a `Certified` evidence record written before the KR0
    /// switch has no theory and reads as not certified; stamping it (what only
    /// the reference mint does) is what makes it certified, and the stamp is
    /// visible on the wire. A stamp on a non-`Certified` assurance certifies
    /// nothing.
    #[test]
    fn an_old_row_reads_as_not_certified_and_the_stamp_is_on_the_wire() {
        use crate::{AssuranceLevel, ProofEvidence, ReasoningKind};
        let old: ProofEvidence =
            serde_json::from_str(r#"{"reasoning":"Constructive","assurance":"Certified"}"#)
                .expect("an old record still reads");
        assert_eq!(old.kernel_theory, None);
        assert_eq!(old.env_digest, None);
        assert!(!old.is_certified());
        let stamped = old
            .clone()
            .with_kernel_reference(KernelTheoryId::LeanReferenceV1, KernelEnvDigest([7; 32]));
        assert!(stamped.is_certified());
        assert_eq!(stamped.without_kernel_reference(), old);
        let wire = serde_json::to_value(&stamped).unwrap();
        assert_eq!(wire["kernel_theory"], "lean-reference-v1");
        assert_eq!(wire["env_digest"], "07".repeat(32));
        assert_eq!(serde_json::from_value::<ProofEvidence>(wire).unwrap(), stamped);
        // An unstamped record serializes exactly as before the switch.
        assert!(serde_json::to_value(&old).unwrap().get("kernel_theory").is_none());
        let trusted = ProofEvidence::new(ReasoningKind::Constructive, AssuranceLevel::Trusted)
            .with_kernel_reference(KernelTheoryId::LeanReferenceV1, KernelEnvDigest([7; 32]));
        assert!(!trusted.is_certified());
    }

    #[test]
    fn env_digest_round_trips_as_hex_and_refuses_other_spellings() {
        let digest = KernelEnvDigest([0xab; 32]);
        let wire = serde_json::to_string(&digest).unwrap();
        assert_eq!(wire, format!("\"{}\"", "ab".repeat(32)));
        assert_eq!(serde_json::from_str::<KernelEnvDigest>(&wire).unwrap(), digest);
        // Negative controls: upper case, short, and non-hex spellings refuse.
        for bad in ["AB".repeat(32), "ab".repeat(31), "zz".repeat(32)] {
            assert!(serde_json::from_str::<KernelEnvDigest>(&format!("\"{bad}\"")).is_err());
        }
    }
}

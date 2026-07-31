// trust-types/result.rs: Verification results
//
// What solvers return after checking a verification condition.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Component, Path};

use serde::de::{self, DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

use crate::formula::{ProofLevel, VcKind, VerificationCondition};
use crate::outcome::Outcome;
use crate::{SourceSpan, Symbol};

// ---------------------------------------------------------------------------
// SMT theory classification for TheoryLemma reasoning kind.
// ---------------------------------------------------------------------------

/// SMT theory classification for `ReasoningKind::TheoryLemma`.
///
/// Identifies which SMT theory solver produced a theory lemma in a proof.
/// Used to distinguish e.g. LIA arithmetic reasoning from bitvector blasting.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SmtTheory {
    /// Linear integer/real arithmetic (LIA/LRA).
    LinearArithmetic,
    /// Fixed-width bitvector theory.
    Bitvectors,
    /// Uninterpreted functions and equality.
    UninterpretedFunctions,
    /// Array theory (select/store).
    Arrays,
    /// Algebraic datatypes.
    Datatypes,
    /// Nonlinear integer/real arithmetic (NIA/NRA).
    NonlinearArithmetic,
    /// String theory.
    Strings,
}

// ---------------------------------------------------------------------------
// NativeProofEnvelope — zero-authority native proof-artifact carrier (S2).
// ---------------------------------------------------------------------------

/// Schema label for [`NativeProofEnvelope`]. Envelopes whose `schema` field
/// does not equal this exact string fail [`NativeProofEnvelope::accepted`]
/// and are treated as absent (strict versioned parse: unknown version ⇒
/// absent, never "best effort").
pub const NATIVE_PROOF_ENVELOPE_SCHEMA: &str = "trust.native-proof-envelope.v1";

/// Hard bound on the TOTAL variable-length payload an envelope may carry and
/// still pass [`NativeProofEnvelope::accepted`]: 16 MiB, counted over EVERY
/// variable-length field — artifact bytes AND every string in the envelope
/// (schema label, the full claim payload, both digest strings, the transport
/// identity strings, and per-artifact `kind`/`sha256` labels). Bounding only
/// artifact bytes would leave a multi-GiB `claim_payload` (or artifact label)
/// as a memory-inflation hole while the gate's own docs claimed a bound.
///
/// Rationale: the envelope rides inside [`VerificationResult::Proved`] rows
/// that are cloned, aggregated, and serialized into run reports. An unbounded
/// carrier would let a (by-construction untrusted) producer inflate
/// report/replay memory arbitrarily. Oversize envelopes are not an error —
/// consumers simply treat them as absent (fail-closed to the status quo), and
/// the lenient wire parse drops them at deserialization.
pub const NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES: u64 = 16 * 1024 * 1024;

/// Hard bound on how many artifacts an envelope may carry and still pass
/// [`NativeProofEnvelope::accepted`]. The byte bound does not count
/// per-artifact fixed overhead, so without this cap a producer could ship
/// millions of zero-byte artifacts under the byte budget. 64 is generous for
/// the real shape (invariant model + transcript + bundle + a few extras).
pub const NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS: usize = 64;

/// The kind of native proof evidence an envelope carries.
///
/// This enum is deliberately CLOSED (no `#[non_exhaustive]`, no catch-all
/// string variant): "kind is known" is enforced by construction — a serialized
/// envelope bearing any other kind string fails deserialization outright, so
/// no downstream code ever needs to reason about an unknown kind.
///
/// `Bmc` / `FiniteAcyclicBmc` are DELIBERATELY UNREPRESENTABLE here: a bounded
/// model-checking run explores finitely many steps of an (in general)
/// unbounded verification condition. A bounded run that finds no
/// counterexample is evidence of absence up to the bound — it is NOT a proof
/// of the unbounded VC, and no replay of it can ever mint proof authority.
/// Bounded stays bounded; a future honest exhaustive-finite lane requires a
/// machine-checkable acyclicity witness and its own kind (blueprint S6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NativeProofEnvelopeKind {
    /// An SMT UNSAT proof bundle (e.g. an ay `SerializableProofBundle`).
    SmtUnsatBundle,
    /// A CHC inductive invariant model (ay-chc).
    ChcInductiveInvariant,
    /// A PDR/IC3 inductive invariant model (ay-chc PDR engine).
    PdrInductiveInvariant,
    /// A Clean-kernel refutation term: `bincode`-serialized CIC proof of
    /// `False` from the negation of the obligation.
    ///
    /// Unlike every other kind here, this one is replayable to a *decision*
    /// rather than merely inspectable — but ONLY by a replayer that rebuilds
    /// the local context from the verification condition itself and checks the
    /// carried term against that rebuilt context. The carried context artifact
    /// is audit material and MUST NOT be used as the checking context: a term
    /// checked against an attacker-chosen context that happens to contain
    /// `h : False` kernel-checks perfectly and proves nothing about the
    /// obligation. See `trust_router::ay_certify::replay_certified_envelope`,
    /// which is the only supported replayer and derives its context solely
    /// from the VC in hand.
    CleanKernelRefutation,
}

/// Mirror of the compiler-side `NativeTransportIdentity` (the transport tuple
/// that identifies which native request/proof a row came from).
///
/// This is a correlation datum ONLY: it lets an auditor or replay gate find
/// the matching request-side objects. Like every other envelope field it is
/// attacker-writable and grants nothing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeProofTransportIdentity {
    /// Native suite name (e.g. the trust-mc harness suite).
    pub suite: String,
    /// Request id within the suite.
    pub request_id: u32,
    /// Proof id within the request.
    pub proof_id: u32,
    /// Native backend row identity string.
    pub native_id: String,
}

/// One content-addressed artifact carried by a [`NativeProofEnvelope`]
/// (e.g. invariant-model bytes, a solver transcript, a proof bundle).
///
/// `sha256` is the hex digest of `bytes` as *claimed by the producer* — a
/// replay gate recomputes it and uses any mismatch as a reject-only
/// pre-filter. Neither field carries authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeProofArtifact {
    /// Artifact kind label (free-form, e.g. `"pdr-invariant-model"`).
    pub kind: String,
    /// Producer-claimed hex SHA-256 of `bytes` (correlation/pre-filter only).
    pub sha256: String,
    /// The exact held bytes.
    pub bytes: Vec<u8>,
}

/// Zero-authority carrier for native (solver-produced) proof artifacts.
///
/// # ZERO AUTHORITY BY CONSTRUCTION — read this before consuming it
///
/// This envelope is **REPLAY INPUT and offline-audit material, nothing more**.
/// It is serializable, which means every field is forgeable by design: anyone
/// who can write a report file can write any envelope whatsoever. Therefore:
///
/// - **No field of this struct may ever be consulted as a checker verdict.**
///   Digests, transport identities, and claim payloads are reject-only
///   pre-filters at best (a mismatch may demote; a match grants nothing).
/// - Proof authority flows exclusively from the compiler gate's OWN
///   re-derivation of the problem from compiler-held request-side objects
///   plus the gate's OWN check verdict (blueprint constitution U1/U6). The
///   private receipt types that record such a gate check live in
///   `trust_verify.rs`, have no serde, and die with the invocation — this
///   public envelope is merely what the gate may choose to replay *from*.
/// - Carrying an envelope does not change any verdict anywhere: a `Proved`
///   row with a forged envelope is exactly as (un)trusted as a `Proved` row
///   with none.
///
/// Consumers MUST treat any envelope for which [`Self::accepted`] returns
/// `false` as absent.
///
/// Schema: [`NATIVE_PROOF_ENVELOPE_SCHEMA`] (`trust.native-proof-envelope.v1`).
///
/// There is intentionally NO `Default` impl: an "empty envelope" is not a
/// meaningful value, and a defaultable envelope invites constructor sites
/// that fill fields lazily.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NativeProofEnvelope {
    /// Schema label; must equal [`NATIVE_PROOF_ENVELOPE_SCHEMA`] to be
    /// [`Self::accepted`]. Unknown versions are treated as absent.
    pub schema: String,
    /// What kind of native evidence the artifacts claim to be. Closed enum —
    /// see [`NativeProofEnvelopeKind`] for why bounded kinds cannot exist.
    pub kind: NativeProofEnvelopeKind,
    /// The FULL canonical exact-VC claim payload string
    /// (`trustc.transport-exact-vc-claim.v2`) for the obligation this
    /// envelope claims to discharge. Carried in full — not just a digest —
    /// so a replay gate can bind by structural payload equality (U7), and an
    /// offline auditor can read the claim without the producing compiler.
    pub claim_payload: String,
    /// Hex SHA-256 of `claim_payload`. **Correlation only — grants nothing.**
    /// A gate that cares recomputes the digest from `claim_payload` (or,
    /// better, compares the payload itself); an attacker who can write this
    /// field can equally write a matching digest, so agreement proves only
    /// internal consistency of the (untrusted) envelope.
    pub claim_digest_sha256: String,
    /// Hex SHA-256 of the normalized solver input (e.g. ay's normalized CHC
    /// input). Reject-only pre-filter for the gate's triple cross-check;
    /// grants nothing.
    pub normalized_input_sha256: String,
    /// Which native request/proof this envelope claims to originate from.
    pub transport_identity: NativeProofTransportIdentity,
    /// Content-addressed artifacts (invariant models, transcripts, bundles).
    pub artifacts: Vec<NativeProofArtifact>,
}

impl NativeProofEnvelope {
    /// Total bytes across EVERY variable-length field the envelope carries:
    /// artifact bytes plus every string (schema, claim payload, digests,
    /// transport identity strings, artifact `kind`/`sha256` labels).
    /// Saturating; a saturated sum is far beyond the acceptance bound anyway.
    #[must_use]
    pub fn total_carried_bytes(&self) -> u64 {
        let base = [
            self.schema.len(),
            self.claim_payload.len(),
            self.claim_digest_sha256.len(),
            self.normalized_input_sha256.len(),
            self.transport_identity.suite.len(),
            self.transport_identity.native_id.len(),
        ]
        .into_iter()
        .fold(0u64, |acc, l| acc.saturating_add(l as u64));
        self.artifacts.iter().fold(base, |acc, a| {
            acc.saturating_add(a.kind.len() as u64)
                .saturating_add(a.sha256.len() as u64)
                .saturating_add(a.bytes.len() as u64)
        })
    }

    /// Strict structural acceptance gate. Consumers MUST treat a non-accepted
    /// envelope exactly as if the field were `None` (the lenient wire parse
    /// on `Proved.native_proof_envelope` already enforces this for
    /// deserialized envelopes; this method is the same predicate for
    /// in-memory-constructed values).
    ///
    /// Accepted means, and only means:
    /// - the schema label is exactly [`NATIVE_PROOF_ENVELOPE_SCHEMA`]
    ///   (unknown/future versions ⇒ absent, never best-effort);
    /// - the kind is known — enforced by the closed
    ///   [`NativeProofEnvelopeKind`] enum, so any in-memory value passes
    ///   this arm by construction (a bogus kind string already failed the
    ///   strict envelope parse and landed absent on the wire);
    /// - `claim_payload` is non-empty (an envelope that does not say what it
    ///   claims to prove is not audit material);
    /// - `artifacts` is non-empty (an envelope with no evidence bytes at all
    ///   is not replay input) and has at most
    ///   [`NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS`] entries;
    /// - total carried bytes (ALL strings + artifact bytes) ≤
    ///   [`NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES`].
    ///
    /// Acceptance is NOT authority: an accepted envelope is merely
    /// well-formed replay input. See the type-level docs.
    #[must_use]
    pub fn accepted(&self) -> bool {
        self.schema == NATIVE_PROOF_ENVELOPE_SCHEMA
            && !self.claim_payload.is_empty()
            && !self.artifacts.is_empty()
            && self.artifacts.len() <= NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS
            && self.total_carried_bytes() <= NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES
    }
}

/// Shared allocation budget for the streaming envelope decoder below.
///
/// This is deliberately separate from [`NativeProofEnvelope::accepted`]: the
/// latter validates values constructed in memory, while this budget prevents
/// an untrusted wire value from first allocating an oversized intermediate
/// representation and only then being rejected.
struct NativeProofEnvelopeParseBudget {
    remaining: usize,
    invalid: bool,
}

impl NativeProofEnvelopeParseBudget {
    fn new() -> Self {
        Self { remaining: NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize, invalid: false }
    }

    fn invalidate(&mut self) {
        self.invalid = true;
    }

    /// Reserve payload bytes before allocating them in the decoded carrier.
    fn reserve(&mut self, bytes: usize) -> bool {
        if self.invalid || bytes > self.remaining {
            self.invalid = true;
            return false;
        }
        self.remaining -= bytes;
        true
    }
}

fn discard_native_proof_sequence<'de, A>(sequence: &mut A) -> Result<(), A::Error>
where
    A: SeqAccess<'de>,
{
    while sequence.next_element::<IgnoredAny>()?.is_some() {}
    Ok(())
}

fn discard_native_proof_map<'de, A>(map: &mut A) -> Result<(), A::Error>
where
    A: MapAccess<'de>,
{
    while map.next_entry::<IgnoredAny, IgnoredAny>()?.is_some() {}
    Ok(())
}

// Each streaming visitor below accepts one JSON shape and must consume every
// other syntactically valid shape without turning an optional bad envelope
// into a failure for its containing result. These macros keep that identical
// fail-closed behavior visible without repeating hundreds of method lines.
macro_rules! reject_native_proof_value_visit {
    ($method:ident, $value_type:ty) => {
        fn $method<E>(self, _value: $value_type) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            self.budget.invalidate();
            Ok(None)
        }
    };
}

macro_rules! reject_native_proof_empty_visit {
    ($method:ident) => {
        fn $method<E>(self) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            self.budget.invalidate();
            Ok(None)
        }
    };
}

macro_rules! reject_native_proof_sequence_visit {
    ($de:lifetime) => {
        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<$de>,
        {
            self.budget.invalidate();
            discard_native_proof_sequence(&mut sequence)?;
            Ok(None)
        }
    };
}

macro_rules! reject_native_proof_map_visit {
    ($de:lifetime) => {
        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<$de>,
        {
            self.budget.invalidate();
            discard_native_proof_map(&mut map)?;
            Ok(None)
        }
    };
}

#[derive(Clone, Copy)]
enum NativeProofEnvelopeField {
    Schema,
    Kind,
    ClaimPayload,
    ClaimDigestSha256,
    NormalizedInputSha256,
    TransportIdentity,
    Artifacts,
    Suite,
    RequestId,
    ProofId,
    NativeId,
    Sha256,
    Bytes,
    Unknown,
}

impl<'de> Deserialize<'de> for NativeProofEnvelopeField {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct FieldVisitor;

        impl Visitor<'_> for FieldVisitor {
            type Value = NativeProofEnvelopeField;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a native-proof-envelope field name")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(match value {
                    "schema" => NativeProofEnvelopeField::Schema,
                    "kind" => NativeProofEnvelopeField::Kind,
                    "claim_payload" => NativeProofEnvelopeField::ClaimPayload,
                    "claim_digest_sha256" => NativeProofEnvelopeField::ClaimDigestSha256,
                    "normalized_input_sha256" => NativeProofEnvelopeField::NormalizedInputSha256,
                    "transport_identity" => NativeProofEnvelopeField::TransportIdentity,
                    "artifacts" => NativeProofEnvelopeField::Artifacts,
                    "suite" => NativeProofEnvelopeField::Suite,
                    "request_id" => NativeProofEnvelopeField::RequestId,
                    "proof_id" => NativeProofEnvelopeField::ProofId,
                    "native_id" => NativeProofEnvelopeField::NativeId,
                    "sha256" => NativeProofEnvelopeField::Sha256,
                    "bytes" => NativeProofEnvelopeField::Bytes,
                    _ => NativeProofEnvelopeField::Unknown,
                })
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                self.visit_str(&value)
            }
        }

        // `deserialize_identifier` lets serde_json borrow ordinary field names
        // directly from the input instead of allocating a `String` for every
        // map key. Unknown keys are never retained.
        deserializer.deserialize_identifier(FieldVisitor)
    }
}

struct BoundedNativeProofStringSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for BoundedNativeProofStringSeed<'_> {
    type Value = Option<String>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct StringVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for StringVisitor<'_> {
            type Value = Option<String>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a bounded native-proof-envelope string")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                // Check before creating the owned carrier string. For plain
                // JSON strings serde_json supplies a borrowed slice; escaped
                // strings may use serde_json's reusable parser scratch space,
                // but are still never copied into the carrier before this
                // check succeeds.
                Ok(self.budget.reserve(value.len()).then(|| value.to_owned()))
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(self.budget.reserve(value.len()).then_some(value))
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_sequence_visit!('de);
            reject_native_proof_map_visit!('de);
        }

        // `deserialize_any` is intentional: a field with the wrong JSON type
        // is consumed and makes the optional envelope absent instead of
        // poisoning the containing VerificationResult.
        deserializer.deserialize_any(StringVisitor { budget: self.budget })
    }
}

/// Decode the closed root `kind` enum without allocating or charging it as a
/// variable-length payload. `total_carried_bytes()` deliberately excludes
/// this fixed closed enum, so charging its wire spelling here would reject an
/// otherwise accepted envelope exactly at the inclusive 16 MiB boundary.
struct NativeProofKindSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for NativeProofKindSeed<'_> {
    type Value = Option<NativeProofEnvelopeKind>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct KindVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for KindVisitor<'_> {
            type Value = Option<NativeProofEnvelopeKind>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a known native-proof-envelope kind")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                let kind = match value {
                    "SmtUnsatBundle" => Some(NativeProofEnvelopeKind::SmtUnsatBundle),
                    "ChcInductiveInvariant" => Some(NativeProofEnvelopeKind::ChcInductiveInvariant),
                    "PdrInductiveInvariant" => Some(NativeProofEnvelopeKind::PdrInductiveInvariant),
                    "CleanKernelRefutation" => {
                        Some(NativeProofEnvelopeKind::CleanKernelRefutation)
                    }
                    _ => None,
                };
                if kind.is_none() {
                    self.budget.invalidate();
                }
                Ok(kind)
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                self.visit_str(&value)
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_sequence_visit!('de);
            reject_native_proof_map_visit!('de);
        }

        deserializer.deserialize_any(KindVisitor { budget: self.budget })
    }
}

struct NativeProofUnsignedSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
    maximum: u64,
}

impl<'de> DeserializeSeed<'de> for NativeProofUnsignedSeed<'_> {
    type Value = Option<u64>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct UnsignedVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
            maximum: u64,
        }

        impl<'de> Visitor<'de> for UnsignedVisitor<'_> {
            type Value = Option<u64>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "an unsigned integer no greater than {}", self.maximum)
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                if value <= self.maximum {
                    Ok(Some(value))
                } else {
                    self.budget.invalidate();
                    Ok(None)
                }
            }

            fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                match u64::try_from(value) {
                    Ok(value) if value <= self.maximum => Ok(Some(value)),
                    _ => {
                        self.budget.invalidate();
                        Ok(None)
                    }
                }
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_value_visit!(visit_str, &str);
            reject_native_proof_value_visit!(visit_string, String);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_sequence_visit!('de);
            reject_native_proof_map_visit!('de);
        }

        deserializer.deserialize_any(UnsignedVisitor { budget: self.budget, maximum: self.maximum })
    }
}

struct NativeProofBytesSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for NativeProofBytesSeed<'_> {
    type Value = Option<Vec<u8>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct BytesVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for BytesVisitor<'_> {
            type Value = Option<Vec<u8>>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a byte sequence within the remaining envelope budget")
            }

            fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                if self.budget.invalid
                    || sequence.size_hint().is_some_and(|hint| hint > self.budget.remaining)
                {
                    self.budget.invalidate();
                    discard_native_proof_sequence(&mut sequence)?;
                    return Ok(None);
                }

                let initial = sequence.size_hint().unwrap_or(0).min(self.budget.remaining);
                let mut bytes = Vec::with_capacity(initial);
                loop {
                    let Some(byte) = sequence.next_element_seed(NativeProofUnsignedSeed {
                        budget: self.budget,
                        maximum: u8::MAX.into(),
                    })?
                    else {
                        return Ok(Some(bytes));
                    };
                    let Some(byte) = byte else {
                        discard_native_proof_sequence(&mut sequence)?;
                        return Ok(None);
                    };
                    if !self.budget.reserve(1) {
                        discard_native_proof_sequence(&mut sequence)?;
                        return Ok(None);
                    }
                    bytes.push(byte as u8);
                }
            }

            fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(self.budget.reserve(value.len()).then(|| value.to_vec()))
            }

            fn visit_byte_buf<E>(self, value: Vec<u8>) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(self.budget.reserve(value.len()).then_some(value))
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_value_visit!(visit_str, &str);
            reject_native_proof_value_visit!(visit_string, String);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_map_visit!('de);
        }

        deserializer.deserialize_any(BytesVisitor { budget: self.budget })
    }
}

struct NativeProofTransportSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for NativeProofTransportSeed<'_> {
    type Value = Option<NativeProofTransportIdentity>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct TransportVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for TransportVisitor<'_> {
            type Value = Option<NativeProofTransportIdentity>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a native-proof transport identity object")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut suite = None;
                let mut request_id = None;
                let mut proof_id = None;
                let mut native_id = None;
                while let Some(field) = map.next_key::<NativeProofEnvelopeField>()? {
                    if self.budget.invalid {
                        map.next_value::<IgnoredAny>()?;
                        discard_native_proof_map(&mut map)?;
                        return Ok(None);
                    }
                    match field {
                        NativeProofEnvelopeField::Suite if suite.is_none() => {
                            suite = map.next_value_seed(BoundedNativeProofStringSeed {
                                budget: self.budget,
                            })?;
                        }
                        NativeProofEnvelopeField::RequestId if request_id.is_none() => {
                            request_id = map
                                .next_value_seed(NativeProofUnsignedSeed {
                                    budget: self.budget,
                                    maximum: u32::MAX.into(),
                                })?
                                .map(|value| value as u32);
                        }
                        NativeProofEnvelopeField::ProofId if proof_id.is_none() => {
                            proof_id = map
                                .next_value_seed(NativeProofUnsignedSeed {
                                    budget: self.budget,
                                    maximum: u32::MAX.into(),
                                })?
                                .map(|value| value as u32);
                        }
                        NativeProofEnvelopeField::NativeId if native_id.is_none() => {
                            native_id = map.next_value_seed(BoundedNativeProofStringSeed {
                                budget: self.budget,
                            })?;
                        }
                        _ => {
                            // Duplicate and unknown fields are invalid. In
                            // particular, this prevents ignored padding from
                            // bypassing the documented total-size bound.
                            self.budget.invalidate();
                            map.next_value::<IgnoredAny>()?;
                        }
                    }
                }
                if self.budget.invalid {
                    return Ok(None);
                }
                Ok(match (suite, request_id, proof_id, native_id) {
                    (Some(suite), Some(request_id), Some(proof_id), Some(native_id)) => {
                        Some(NativeProofTransportIdentity {
                            suite,
                            request_id,
                            proof_id,
                            native_id,
                        })
                    }
                    _ => None,
                })
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_value_visit!(visit_str, &str);
            reject_native_proof_value_visit!(visit_string, String);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_sequence_visit!('de);
        }

        deserializer.deserialize_any(TransportVisitor { budget: self.budget })
    }
}

struct NativeProofArtifactSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for NativeProofArtifactSeed<'_> {
    type Value = Option<NativeProofArtifact>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ArtifactVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for ArtifactVisitor<'_> {
            type Value = Option<NativeProofArtifact>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a bounded native-proof artifact object")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut kind = None;
                let mut sha256 = None;
                let mut bytes = None;
                while let Some(field) = map.next_key::<NativeProofEnvelopeField>()? {
                    if self.budget.invalid {
                        map.next_value::<IgnoredAny>()?;
                        discard_native_proof_map(&mut map)?;
                        return Ok(None);
                    }
                    match field {
                        NativeProofEnvelopeField::Kind if kind.is_none() => {
                            kind = map.next_value_seed(BoundedNativeProofStringSeed {
                                budget: self.budget,
                            })?;
                        }
                        NativeProofEnvelopeField::Sha256 if sha256.is_none() => {
                            sha256 = map.next_value_seed(BoundedNativeProofStringSeed {
                                budget: self.budget,
                            })?;
                        }
                        NativeProofEnvelopeField::Bytes if bytes.is_none() => {
                            bytes =
                                map.next_value_seed(NativeProofBytesSeed { budget: self.budget })?;
                        }
                        _ => {
                            self.budget.invalidate();
                            map.next_value::<IgnoredAny>()?;
                        }
                    }
                }
                if self.budget.invalid {
                    return Ok(None);
                }
                Ok(match (kind, sha256, bytes) {
                    (Some(kind), Some(sha256), Some(bytes)) => {
                        Some(NativeProofArtifact { kind, sha256, bytes })
                    }
                    _ => None,
                })
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_value_visit!(visit_str, &str);
            reject_native_proof_value_visit!(visit_string, String);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_sequence_visit!('de);
        }

        deserializer.deserialize_any(ArtifactVisitor { budget: self.budget })
    }
}

struct NativeProofArtifactsSeed<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> DeserializeSeed<'de> for NativeProofArtifactsSeed<'_> {
    type Value = Option<Vec<NativeProofArtifact>>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ArtifactsVisitor<'a> {
            budget: &'a mut NativeProofEnvelopeParseBudget,
        }

        impl<'de> Visitor<'de> for ArtifactsVisitor<'_> {
            type Value = Option<Vec<NativeProofArtifact>>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    formatter,
                    "at most {NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS} native-proof artifacts"
                )
            }

            fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                if self.budget.invalid
                    || sequence
                        .size_hint()
                        .is_some_and(|hint| hint > NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS)
                {
                    self.budget.invalidate();
                    discard_native_proof_sequence(&mut sequence)?;
                    return Ok(None);
                }
                let mut artifacts = Vec::with_capacity(
                    sequence.size_hint().unwrap_or(0).min(NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS),
                );
                while artifacts.len() < NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS {
                    match sequence
                        .next_element_seed(NativeProofArtifactSeed { budget: self.budget })?
                    {
                        None => return Ok(Some(artifacts)),
                        Some(Some(artifact)) => artifacts.push(artifact),
                        Some(None) => {
                            self.budget.invalidate();
                            discard_native_proof_sequence(&mut sequence)?;
                            return Ok(None);
                        }
                    }
                }
                if sequence.next_element::<IgnoredAny>()?.is_some() {
                    self.budget.invalidate();
                    discard_native_proof_sequence(&mut sequence)?;
                    return Ok(None);
                }
                Ok(Some(artifacts))
            }

            reject_native_proof_value_visit!(visit_bool, bool);
            reject_native_proof_value_visit!(visit_i64, i64);
            reject_native_proof_value_visit!(visit_u64, u64);
            reject_native_proof_value_visit!(visit_f64, f64);
            reject_native_proof_value_visit!(visit_str, &str);
            reject_native_proof_value_visit!(visit_string, String);
            reject_native_proof_empty_visit!(visit_none);
            reject_native_proof_empty_visit!(visit_unit);
            reject_native_proof_map_visit!('de);
        }

        deserializer.deserialize_any(ArtifactsVisitor { budget: self.budget })
    }
}

struct NativeProofEnvelopeVisitor<'a> {
    budget: &'a mut NativeProofEnvelopeParseBudget,
}

impl<'de> Visitor<'de> for NativeProofEnvelopeVisitor<'_> {
    type Value = Option<NativeProofEnvelope>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a bounded native-proof-envelope object")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut schema = None;
        let mut kind = None;
        let mut claim_payload = None;
        let mut claim_digest_sha256 = None;
        let mut normalized_input_sha256 = None;
        let mut transport_identity = None;
        let mut artifacts = None;
        while let Some(field) = map.next_key::<NativeProofEnvelopeField>()? {
            if self.budget.invalid {
                map.next_value::<IgnoredAny>()?;
                discard_native_proof_map(&mut map)?;
                return Ok(None);
            }
            match field {
                NativeProofEnvelopeField::Schema if schema.is_none() => {
                    schema =
                        map.next_value_seed(BoundedNativeProofStringSeed { budget: self.budget })?;
                }
                NativeProofEnvelopeField::Kind if kind.is_none() => {
                    kind = map.next_value_seed(NativeProofKindSeed { budget: self.budget })?;
                }
                NativeProofEnvelopeField::ClaimPayload if claim_payload.is_none() => {
                    claim_payload =
                        map.next_value_seed(BoundedNativeProofStringSeed { budget: self.budget })?;
                }
                NativeProofEnvelopeField::ClaimDigestSha256 if claim_digest_sha256.is_none() => {
                    claim_digest_sha256 =
                        map.next_value_seed(BoundedNativeProofStringSeed { budget: self.budget })?;
                }
                NativeProofEnvelopeField::NormalizedInputSha256
                    if normalized_input_sha256.is_none() =>
                {
                    normalized_input_sha256 =
                        map.next_value_seed(BoundedNativeProofStringSeed { budget: self.budget })?;
                }
                NativeProofEnvelopeField::TransportIdentity if transport_identity.is_none() => {
                    transport_identity =
                        map.next_value_seed(NativeProofTransportSeed { budget: self.budget })?;
                    if transport_identity.is_none() {
                        self.budget.invalidate();
                    }
                }
                NativeProofEnvelopeField::Artifacts if artifacts.is_none() => {
                    artifacts =
                        map.next_value_seed(NativeProofArtifactsSeed { budget: self.budget })?;
                    if artifacts.is_none() {
                        self.budget.invalidate();
                    }
                }
                _ => {
                    self.budget.invalidate();
                    map.next_value::<IgnoredAny>()?;
                }
            }
        }
        if self.budget.invalid {
            return Ok(None);
        }
        Ok(
            match (
                schema,
                kind,
                claim_payload,
                claim_digest_sha256,
                normalized_input_sha256,
                transport_identity,
                artifacts,
            ) {
                (
                    Some(schema),
                    Some(kind),
                    Some(claim_payload),
                    Some(claim_digest_sha256),
                    Some(normalized_input_sha256),
                    Some(transport_identity),
                    Some(artifacts),
                ) => Some(NativeProofEnvelope {
                    schema,
                    kind,
                    claim_payload,
                    claim_digest_sha256,
                    normalized_input_sha256,
                    transport_identity,
                    artifacts,
                }),
                _ => None,
            },
        )
    }

    reject_native_proof_value_visit!(visit_bool, bool);
    reject_native_proof_value_visit!(visit_i64, i64);
    reject_native_proof_value_visit!(visit_u64, u64);
    reject_native_proof_value_visit!(visit_f64, f64);
    reject_native_proof_value_visit!(visit_str, &str);
    reject_native_proof_value_visit!(visit_string, String);
    reject_native_proof_empty_visit!(visit_none);
    reject_native_proof_empty_visit!(visit_unit);
    reject_native_proof_sequence_visit!('de);
}

/// Decode one envelope through the shared streaming, allocation-bounded
/// visitor. Both the strict public `NativeProofEnvelope` deserializer and the
/// lenient optional `VerificationResult::Proved` field use this exact path;
/// parsing the envelope type directly must not bypass the wire budget.
fn deserialize_native_proof_envelope_bounded<'de, D>(
    deserializer: D,
) -> Result<Option<NativeProofEnvelope>, D::Error>
where
    D: Deserializer<'de>,
{
    let mut budget = NativeProofEnvelopeParseBudget::new();
    let envelope =
        deserializer.deserialize_any(NativeProofEnvelopeVisitor { budget: &mut budget })?;
    Ok(envelope.filter(NativeProofEnvelope::accepted))
}

impl<'de> Deserialize<'de> for NativeProofEnvelope {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserialize_native_proof_envelope_bounded(deserializer)?.ok_or_else(|| {
            de::Error::custom("invalid or oversized trust.native-proof-envelope.v1 value")
        })
    }
}

/// Field-level lenient deserializer for `Proved.native_proof_envelope`,
/// implementing the blueprint's strict-versioned-parse rule at the WIRE
/// boundary: a malformed/structurally incomplete, unknown-kind, unknown-version, or
/// otherwise non-[`NativeProofEnvelope::accepted`] envelope deserializes as
/// `None` instead of aborting the ENTIRE containing `VerificationResult`
/// document. Without this, one hostile or future-version envelope would be a
/// parse bomb poisoning every report/cache document embedding results — and a
/// future schema version adding a kind could never be introduced without
/// hard-breaking every deployed v1 parser at the whole-row level.
///
/// Fail-closed both ways: dropping an envelope only removes optional
/// zero-authority replay-input material (the row keeps its deserialized-Proved
/// treatment either way); it can never upgrade anything.
///
/// Parsing is streaming and allocation-bounded. Every retained string/byte is
/// charged against one shared budget before entering the carrier, artifact
/// count is checked before materializing an extra artifact, and unknown or
/// duplicate fields invalidate the envelope while their values are discarded
/// through [`IgnoredAny`]. There is no unbounded `serde_json::Value`
/// intermediate for hostile input to inflate.
fn deserialize_native_proof_envelope_lenient<'de, D>(
    deserializer: D,
) -> Result<Option<NativeProofEnvelope>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_native_proof_envelope_bounded(deserializer)
}

/// What a solver returns.
///
/// Each variant represents a possible outcome from a verification backend
/// (ay, trust-wp, ty, etc.).
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationResult, ProofStrength};
///
/// // A proved result from ay
/// let proved = VerificationResult::Proved {
///     solver: "ay".into(),
///     time_ms: 5,
///     strength: ProofStrength::smt_unsat(),
///     proof_certificate: None,
///     solver_warnings: None,
///     native_proof_envelope: None,
/// };
/// assert!(proved.is_proved());
/// assert_eq!(proved.solver_name(), "ay");
/// assert_eq!(proved.time_ms(), 5);
///
/// // A timeout result
/// let timeout = VerificationResult::Timeout {
///     solver: "ay".into(),
///     timeout_ms: 30000,
/// };
/// assert!(!timeout.is_proved());
/// assert_eq!(timeout.time_ms(), 30000);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationResult {
    Proved {
        // Interned solver name — small set repeated across all results.
        solver: Symbol,
        time_ms: u64,
        strength: ProofStrength,
        /// Raw proof certificate data from the solver (e.g., LRAT bytes from ay).
        /// Populated when the solver produces a proof certificate alongside an UNSAT result.
        /// `None` when no certificate is available (e.g., non-ay solvers, or older results).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        proof_certificate: Option<Vec<u8>>,
        /// Warnings captured from solver stderr during verification.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        solver_warnings: Option<Vec<String>>,
        /// Zero-authority native proof-artifact carrier (replay input /
        /// offline-audit material ONLY — see [`NativeProofEnvelope`] for the
        /// loud version). Carrying (or forging) an envelope changes no
        /// verdict anywhere; authority comes solely from the compiler gate's
        /// own re-derivation and re-check. Consumers treat a non-`accepted()`
        /// envelope as `None`.
        ///
        /// Wire compat: `#[serde(default)]` — `Proved` values serialized
        /// before this field existed deserialize with `None`;
        /// `skip_serializing_if` keeps envelope-less rows byte-identical on
        /// the wire. (`VerificationResult` uses serde's default external
        /// tagging, so adding an optional named field to a struct variant is
        /// a compatible schema extension.)
        ///
        /// Strict versioned parse, NOT a parse bomb: `deserialize_with` routes
        /// through [`deserialize_native_proof_envelope_lenient`], so a
        /// malformed / unknown-kind / unknown-version / oversize envelope
        /// lands as `None` (treated absent) instead of failing
        /// deserialization of the whole containing result document.
        #[serde(
            default,
            skip_serializing_if = "Option::is_none",
            deserialize_with = "deserialize_native_proof_envelope_lenient"
        )]
        native_proof_envelope: Option<NativeProofEnvelope>,
    },
    Failed {
        solver: Symbol,
        time_ms: u64,
        counterexample: Option<Counterexample>,
    },
    Unknown {
        solver: Symbol,
        time_ms: u64,
        reason: String,
    },
    Timeout {
        solver: Symbol,
        timeout_ms: u64,
    },
}

impl VerificationResult {
    /// This backend result as the shared outcome it denotes.
    ///
    /// A backend result carries the evidence (solver, timing, certificate,
    /// counterexample); the outcome is the conclusion drawn from it. Naming that
    /// conclusion once means a cache verdict, a report row, and a diagnostic
    /// cannot end up spelling the same conclusion three ways.
    ///
    /// Exhaustive on purpose: `VerificationResult` is `#[non_exhaustive]` only
    /// for its dependents, so a variant added here has to be given an outcome
    /// at the same time rather than falling into `Unknown` unnoticed.
    #[must_use]
    pub fn outcome(&self) -> Outcome {
        match self {
            VerificationResult::Proved { .. } => Outcome::Proved,
            VerificationResult::Failed { .. } => Outcome::Failed,
            VerificationResult::Unknown { .. } => Outcome::Unknown,
            VerificationResult::Timeout { .. } => Outcome::Timeout,
        }
    }

    pub fn is_proved(&self) -> bool {
        matches!(self, VerificationResult::Proved { .. })
    }

    pub fn is_failed(&self) -> bool {
        matches!(self, VerificationResult::Failed { .. })
    }

    /// The proof assurance of a `Proved` result; `None` for any other outcome.
    #[must_use]
    pub fn assurance(&self) -> Option<AssuranceLevel> {
        match self {
            VerificationResult::Proved { strength, .. } => Some(strength.assurance.clone()),
            _ => None,
        }
    }

    /// Un-forgeable-`Proved` gate. Keep a `Proved` result ONLY when its proof
    /// assurance is at least `min`; otherwise DOWNGRADE it to `Unknown`.
    ///
    /// This is the enforcement primitive behind "a wrong solver UNSAT can never
    /// be reported as proof": a backend that returns `Proved` with
    /// [`AssuranceLevel::Unchecked`] (a bare, unvalidated solver "unsat" — see
    /// [`ProofStrength::smt_unsat_unvalidated`]) cannot pass a boundary that
    /// requires `SmtBacked` or `Certified`. Apply it at the chokepoint where
    /// backend results become user-facing verdicts. Pass
    /// [`AssuranceLevel::Certified`] to demand kernel-checked *true proof* and
    /// downgrade everything weaker (including `Sound`/`SmtBacked`).
    ///
    /// `Failed`/`Unknown`/`Timeout` pass through unchanged — this gate only ever
    /// *weakens* a `Proved`, never strengthens any result, so it is sound by
    /// construction.
    #[must_use]
    pub fn require_assurance(self, min: AssuranceLevel) -> VerificationResult {
        self.require_assurance_inner(min)
    }

    /// R-U Phase B2: the NAMED reporting floor. Call sites name the policy
    /// ("this is the reported-proof floor") instead of hand-picking the enum
    /// variant; exactly ONE place — this method — defines what that floor is.
    /// Extensionally identical to `require_assurance(AssuranceLevel::SmtBacked)`
    /// (pinned by `named_reporting_floor_matches_the_variant_form`), and the
    /// same policy the grade record's `meets_reporting_floor` projects.
    #[must_use]
    pub fn require_reporting_floor(self) -> VerificationResult {
        self.require_assurance_inner(AssuranceLevel::SmtBacked)
    }

    fn require_assurance_inner(self, min: AssuranceLevel) -> VerificationResult {
        match &self {
            VerificationResult::Proved { strength, solver, time_ms, .. }
                if strength.assurance.strength_order() < min.strength_order() =>
            {
                VerificationResult::Unknown {
                    solver: *solver,
                    time_ms: *time_ms,
                    reason: format!(
                        "proof assurance {:?} below required {min:?}; downgraded to Unknown \
                         (un-forgeable-Proved gate)",
                        strength.assurance
                    ),
                }
            }
            _ => self,
        }
    }

    pub fn solver_name(&self) -> &str {
        match self {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => solver.as_str(),
        }
    }

    /// Get the solver Symbol (Copy, O(1) equality).
    #[must_use]
    pub fn solver_symbol(&self) -> Symbol {
        match self {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => *solver,
        }
    }

    pub fn time_ms(&self) -> u64 {
        match self {
            VerificationResult::Proved { time_ms, .. }
            | VerificationResult::Failed { time_ms, .. }
            | VerificationResult::Unknown { time_ms, .. } => *time_ms,
            VerificationResult::Timeout { timeout_ms, .. } => *timeout_ms,
        }
    }

    /// Returns true when the router skipped solver dispatch because the
    /// process memory guard had already reached its hard limit.
    #[must_use]
    pub fn is_memory_guard_solver_skip(&self) -> bool {
        match self {
            VerificationResult::Unknown { solver, reason, .. } => {
                solver.as_str() == "memory-guard"
                    && (reason.contains("memory limit exceeded")
                        || reason.contains("skipping solver dispatch"))
            }
            _ => false,
        }
    }

    /// Machine-stable wording for reports that need to keep memory-guard
    /// skips visible as release-blocking proof gaps.
    #[must_use]
    pub fn release_blocking_proof_gap_reason(&self) -> Option<String> {
        let VerificationResult::Unknown { reason, .. } = self else {
            return None;
        };
        if !self.is_memory_guard_solver_skip() {
            return None;
        }
        if reason.contains("release-blocking proof gap") {
            return Some(reason.clone());
        }
        Some(format!("release-blocking proof gap: memory guard skipped solver dispatch; {reason}"))
    }

    /// Derive `ProofEvidence` from this result.
    ///
    /// Returns `Some(ProofEvidence)` for `Proved` results (converting the legacy
    /// `ProofStrength` via `From`), and `None` for all other outcomes.
    #[must_use]
    pub fn evidence(&self) -> Option<ProofEvidence> {
        match self {
            VerificationResult::Proved { strength, .. } => Some(strength.clone().into()),
            _ => None,
        }
    }
}

/// How a proof was obtained (the reasoning technique used).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReasoningKind {
    /// SMT solver returned UNSAT (e.g., ay DPLL(T)).
    Smt,
    /// Bounded model checking explored states up to a given depth (e.g., trust_mc BMC, incomplete).
    BoundedModelCheck { depth: u64 },
    /// Exhaustive finite-state exploration (e.g., ty BFS, complete for finite).
    ExhaustiveFinite(u64),
    /// An inductive safety invariant was found (e.g., k-induction, IC3/PDR, CEGAR).
    ///
    /// These techniques prove safety properties (AG !bad) — that bad states
    /// are unreachable. They do NOT prove termination, which requires ranking functions,
    /// well-founded orderings, or decreases clauses.
    Inductive,
    /// Deductive verification via pre/postcondition reasoning (e.g., trust-wp, trust-vc).
    Deductive,
    /// Constructive proof term produced (e.g., clean).
    Constructive,
    /// Property-directed reachability (IC3/PDR) — proves safety properties (AG !bad).
    ///
    /// PDR/IC3 finds inductive invariants that prove bad states are
    /// unreachable. It does NOT prove termination or liveness. Termination requires
    /// ranking function synthesis; liveness requires fairness + ranking or Buchi automata.
    Pdr,
    /// Constrained Horn Clause solving via Spacer.
    ChcSpacer,
    /// Abstract interpretation discharged the obligation (sound over-approximation).
    AbstractInterpretation,

    // --- New variants for SMT proof technique granularity ---
    /// CDCL resolution proof from SAT/SMT Boolean skeleton.
    CdclResolution,
    /// Theory-specific lemma (LIA, BV, UF, arrays, etc.).
    TheoryLemma { theory: SmtTheory },
    /// Bitvector to SAT reduction.
    BitBlasting,

    // --- Solver-specific techniques ---
    /// Symbolic execution (future concolic/SE backends).
    SymbolicExecution,
    /// Ownership and borrow-checker reasoning (trust-vc).
    OwnershipAnalysis,
    /// Explicit-state model checking (ty BFS/DFS complete check).
    ExplicitStateModel,
    /// Neural network verification via bounding (`ny`). Incomplete by
    /// construction: a bound holds over an epsilon ball, not over all inputs,
    /// which is why `is_complete` excludes it.
    NeuralBounding,
    /// Craig interpolation for modular verification.
    Interpolation,
}

impl ReasoningKind {
    /// Whether this reasoning method is complete (covers all inputs).
    ///
    /// Returns `true` for `Smt`, `ExhaustiveFinite`, `Inductive`,
    /// `Deductive`, `Constructive`, `Pdr`, `ChcSpacer`, `AbstractInterpretation`,
    /// `CdclResolution`, `TheoryLemma`, `BitBlasting`, `OwnershipAnalysis`,
    /// `ExplicitStateModel`, `Interpolation`.
    /// Returns `false` for `BoundedModelCheck` (only checks up to a depth),
    /// `SymbolicExecution` (bounded by path depth), `NeuralBounding` (epsilon-bounded).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        !matches!(
            self,
            Self::BoundedModelCheck { .. } | Self::SymbolicExecution | Self::NeuralBounding
        )
    }
}

/// How much confidence the proof provides.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AssuranceLevel {
    /// Complete, sound proof — property holds for all inputs.
    Sound,
    /// Property checked up to a bounded depth (no violation found within depth).
    BoundedSound { depth: u64 },
    /// Best-effort / heuristic — no formal guarantee.
    Heuristic,
    /// Solver said so, no independent validation.
    Unchecked,
    /// Solver UNSAT, trusted TCB.
    Trusted,
    /// ay axiom in clean, not fully reconstructed.
    SmtBacked,
    /// clean kernel independently verified.
    Certified,
}

impl AssuranceLevel {
    /// Numeric strength ordering for comparison.
    ///
    /// `Unchecked`/`Heuristic`=0, `Trusted`/`BoundedSound`=1,
    /// `SmtBacked`/`Sound`=2, `Certified`=3.
    #[must_use]
    pub fn strength_order(&self) -> u8 {
        match self {
            Self::Unchecked | Self::Heuristic => 0,
            Self::Trusted | Self::BoundedSound { .. } => 1,
            Self::SmtBacked | Self::Sound => 2,
            Self::Certified => 3,
        }
    }

    /// R-U Phase B (named policy predicates; design §5/§7): the REPORTING
    /// floor. A positive proof result is reportable as proved only at
    /// `SmtBacked` strength or above; weaker levels (`Unchecked` — a bare
    /// unvalidated solver "unsat" — `Heuristic`, `Trusted`, `BoundedSound`)
    /// are below the floor. Centralizes the scattered
    /// `strength_order() >= SmtBacked.strength_order()` comparisons so this
    /// policy has ONE name and one seam to migrate onto `GradeRecord` axes.
    #[must_use]
    pub fn meets_reporting_floor(&self) -> bool {
        self.strength_order() >= Self::SmtBacked.strength_order()
    }
}

/// How strong the proof is: combines *how* it was done with *how much* assurance it provides.
///
/// # Examples
///
/// ```
/// use trust_types::ProofStrength;
///
/// // Most common: SMT solver returned UNSAT
/// let smt = ProofStrength::smt_unsat();
///
/// // Bounded model checking to depth 100
/// let bmc = ProofStrength::bounded(100);
///
/// // Deductive (pre/postcondition) proof
/// let ded = ProofStrength::deductive();
///
/// // Compare assurance levels
/// assert!(smt.assurance.strength_order() > bmc.assurance.strength_order());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
pub struct ProofStrength {
    /// The reasoning technique used to obtain this proof.
    pub reasoning: ReasoningKind,
    /// The level of assurance the proof provides.
    pub assurance: AssuranceLevel,
}

/// R-U Phase E (§7 grade migration): the serialized form carries a third,
/// DERIVED `grade` field alongside the two legacy fields, so JSON consumers
/// can read the multi-axis record without re-implementing the legacy
/// mapping. The field is write-only by construction: `Deserialize` stays
/// derived over the two legacy fields (serde ignores unknown fields), and
/// the grade is recomputed from them on every [`ProofStrength::grade`]
/// call — an inbound JSON with a forged or stale `grade` cannot influence
/// any verdict or floor. Old readers ignore the extra field; old payloads
/// (two fields) still deserialize.
/// Binary formats (bincode: positional, non-self-describing) keep the exact
/// legacy two-field wire — a third field would break every existing cache
/// entry and old-reader pairing — so the grade rides only self-describing
/// human-readable formats, where unknown fields are ignorable by contract.
impl Serialize for ProofStrength {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        if !serializer.is_human_readable() {
            let mut out = serializer.serialize_struct("ProofStrength", 2)?;
            out.serialize_field("reasoning", &self.reasoning)?;
            out.serialize_field("assurance", &self.assurance)?;
            return out.end();
        }
        let mut out = serializer.serialize_struct("ProofStrength", 3)?;
        out.serialize_field("reasoning", &self.reasoning)?;
        out.serialize_field("assurance", &self.assurance)?;
        out.serialize_field("grade", &self.grade())?;
        out.end()
    }
}

impl ProofStrength {
    /// The §7 multi-axis view of this strength (two-language design, R-U).
    /// See [`ProofEvidence::grade`].
    #[must_use]
    pub fn grade(&self) -> crate::grade::GradeRecord {
        crate::grade::GradeRecord::from_legacy_evidence(&self.reasoning, &self.assurance)
    }

    /// The §7 multi-axis view with the clause's independently transported
    /// certified-monitor disposition attached to the executability axis.
    #[must_use]
    pub fn grade_with_monitor(
        &self,
        monitor: Option<&TransportMonitorEvidence>,
    ) -> crate::grade::GradeRecord {
        self.grade().with_monitor_evidence(monitor)
    }

    /// SMT solver returned UNSAT — sound, complete proof.
    ///
    /// NOTE: this stamps [`AssuranceLevel::Sound`], which is only honest when the
    /// solver's UNSAT was *independently validated* (a strict-checked proof, or a
    /// sound-by-construction backend). A bare solver "unsat" with no proof check
    /// is [`AssuranceLevel::Unchecked`] — use [`Self::smt_unsat_unvalidated`].
    /// A strict-checked proof is [`Self::smt_unsat_strict_checked`]; a kernel-
    /// reconstructed proof is [`Self::smt_unsat_certified`]. Mislabeling an
    /// unvalidated verdict `Sound` is the type-level root of solver-core
    /// false-PROVEs (a wrong UNSAT is then reported as a complete proof).
    #[must_use]
    pub fn smt_unsat() -> Self {
        Self { reasoning: ReasoningKind::Smt, assurance: AssuranceLevel::Sound }
    }

    /// SMT solver returned UNSAT but the proof was NOT independently validated
    /// (no proof produced, or produced-but-unchecked). Honest assurance is
    /// [`AssuranceLevel::Unchecked`] — "solver said so, no independent
    /// validation". A boundary that requires real proof (see
    /// [`VerificationResult::require_assurance`]) downgrades this to `Unknown`,
    /// so a buggy solver-core UNSAT cannot surface as a proof.
    #[must_use]
    pub fn smt_unsat_unvalidated() -> Self {
        Self { reasoning: ReasoningKind::Smt, assurance: AssuranceLevel::Unchecked }
    }

    /// SMT solver returned UNSAT and its proof was accepted by an SMT-level
    /// strict proof checker (e.g. ay's `check_proof_strict`). Assurance is
    /// [`AssuranceLevel::SmtBacked`]. This is defense-in-depth, NOT a kernel
    /// proof: the checker is itself trusted code (and has historically had
    /// meta-soundness bugs), so it is below [`AssuranceLevel::Certified`].
    #[must_use]
    pub fn smt_unsat_strict_checked() -> Self {
        Self { reasoning: ReasoningKind::Smt, assurance: AssuranceLevel::SmtBacked }
    }

    /// SMT solver returned UNSAT and its proof was independently reconstructed
    /// and re-checked by a verified kernel (clean/CIC or Lean). Assurance is
    /// [`AssuranceLevel::Certified`] — the highest rung, "true proof": soundness
    /// reduces to the kernel, not to the solver or the SMT checker.
    #[must_use]
    pub fn smt_unsat_certified() -> Self {
        Self { reasoning: ReasoningKind::Smt, assurance: AssuranceLevel::Certified }
    }

    /// BMC checked all states to depth k with no violation.
    #[must_use]
    pub fn bounded(depth: u64) -> Self {
        Self {
            reasoning: ReasoningKind::BoundedModelCheck { depth },
            assurance: AssuranceLevel::BoundedSound { depth },
        }
    }

    /// An inductive safety invariant was found — sound proof of safety (AG !bad).
    ///
    /// Does NOT prove termination. See `TerminationStrategy` for
    /// termination proof techniques.
    #[must_use]
    pub fn inductive() -> Self {
        Self { reasoning: ReasoningKind::Inductive, assurance: AssuranceLevel::Sound }
    }

    /// Deductive verification (pre/postcondition reasoning) — sound proof.
    #[must_use]
    pub fn deductive() -> Self {
        Self { reasoning: ReasoningKind::Deductive, assurance: AssuranceLevel::Sound }
    }

    /// Constructive proof term (clean) — sound proof.
    #[must_use]
    pub fn constructive() -> Self {
        Self { reasoning: ReasoningKind::Constructive, assurance: AssuranceLevel::Sound }
    }

    /// Property-directed reachability (IC3/PDR) — sound proof of safety (AG !bad).
    ///
    /// PDR proves safety properties only. It does NOT prove termination
    /// or liveness. Termination requires ranking functions or well-founded orderings.
    #[must_use]
    pub fn pdr() -> Self {
        Self { reasoning: ReasoningKind::Pdr, assurance: AssuranceLevel::Sound }
    }

    /// CHC solving via Spacer — sound proof.
    #[must_use]
    pub fn chc_spacer() -> Self {
        Self { reasoning: ReasoningKind::ChcSpacer, assurance: AssuranceLevel::Sound }
    }

    /// Abstract interpretation — sound proof via over-approximation.
    #[must_use]
    pub fn abstract_interpretation() -> Self {
        Self { reasoning: ReasoningKind::AbstractInterpretation, assurance: AssuranceLevel::Sound }
    }

    /// Whether the proof provides full (sound) assurance.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::Sound)
    }

    /// Whether the proof is only bounded (checked up to a depth).
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::BoundedSound { .. })
    }

    /// Get the bounded depth, if this is a bounded proof.
    #[must_use]
    pub fn bounded_depth(&self) -> Option<u64> {
        match &self.assurance {
            AssuranceLevel::BoundedSound { depth } => Some(*depth),
            _ => None,
        }
    }

    /// R-U Phase B (named policy predicates; design §5): FACT/SUMMARY
    /// REUSABILITY — whether this strength licenses minting the result as
    /// reusable cross-function evidence (a callee `#[ensures]` fact, a modular
    /// summary). Requires an UNBOUNDED result, a COMPLETE reasoning method,
    /// and `Sound`/`Certified` assurance exactly (match-based, deliberately
    /// NOT the order floor: `SmtBacked` is a per-obligation validation level,
    /// not a whole-behavior soundness claim, so it does not mint reusable
    /// facts). Centralizes the predicate previously duplicated verbatim in
    /// trust-types::facts and trust-vcgen::modular.
    #[must_use]
    pub fn is_reusable_complete_unbounded(&self) -> bool {
        !self.is_bounded()
            && self.reasoning.is_complete()
            && matches!(self.assurance, AssuranceLevel::Sound | AssuranceLevel::Certified)
    }
}

// ---------------------------------------------------------------------------
// ProofEvidence — combined reasoning + assurance (new type system)
// ---------------------------------------------------------------------------

/// Combined proof evidence: what method was used + how much we trust it.
///
/// This is the correct replacement for using `ProofStrength` directly.
/// `ProofStrength` conflates reasoning method with certification status;
/// `ProofEvidence` keeps them orthogonal so that e.g. a `BoundedDepth`
/// result can never silently upgrade to `Certified`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProofEvidence {
    /// What kind of reasoning was used to prove the property.
    pub reasoning: ReasoningKind,
    /// How much independent assurance backs the proof.
    pub assurance: AssuranceLevel,
}

impl ProofEvidence {
    /// Create a new `ProofEvidence` from reasoning kind and assurance level.
    #[must_use]
    pub fn new(reasoning: ReasoningKind, assurance: AssuranceLevel) -> Self {
        Self { reasoning, assurance }
    }

    /// Whether this evidence has been independently certified (clean kernel).
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.assurance, AssuranceLevel::Certified)
    }

    /// Whether this evidence comes from bounded (incomplete) reasoning.
    #[must_use]
    pub fn is_bounded(&self) -> bool {
        matches!(self.reasoning, ReasoningKind::BoundedModelCheck { .. })
    }

    /// The §7 multi-axis view of this evidence (two-language design, R-U).
    /// Lossless: `grade().to_legacy()` reproduces `self.assurance` (up to the
    /// documented `Certified`↔empty-closure identification); bounded
    /// reasoning refines the coverage axis only.
    #[must_use]
    pub fn grade(&self) -> crate::grade::GradeRecord {
        crate::grade::GradeRecord::from_legacy_evidence(&self.reasoning, &self.assurance)
    }

    /// The §7 multi-axis view with the clause's independently transported
    /// certified-monitor disposition attached to the executability axis.
    #[must_use]
    pub fn grade_with_monitor(
        &self,
        monitor: Option<&TransportMonitorEvidence>,
    ) -> crate::grade::GradeRecord {
        self.grade().with_monitor_evidence(monitor)
    }
}

impl From<ProofStrength> for ProofEvidence {
    /// Backward-compatible conversion from legacy `ProofStrength`.
    ///
    /// Maps existing `AssuranceLevel` variants into the new evidence model:
    /// `Sound` maps to `SmtBacked`, `BoundedSound` preserves its depth, and
    /// `Heuristic` to `Unchecked`. New variants pass through directly.
    fn from(ps: ProofStrength) -> Self {
        let assurance = match ps.assurance {
            AssuranceLevel::Sound => AssuranceLevel::SmtBacked,
            AssuranceLevel::BoundedSound { depth } => AssuranceLevel::BoundedSound { depth },
            AssuranceLevel::Heuristic => AssuranceLevel::Unchecked,
            // New variants pass through directly.
            other => other,
        };
        Self { reasoning: ps.reasoning, assurance }
    }
}

/// How unresolved verification results should be classified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[non_exhaustive]
pub enum RuntimeCheckPolicy {
    /// Use Rust's existing runtime checks when verification is inconclusive and
    /// the VC kind has a corresponding runtime fallback.
    #[default]
    Auto,
    /// Require a static proof. Unknown or timeout results become compile errors.
    ForceStatic,
    /// Always classify the obligation as runtime-checked unless a concrete
    /// counterexample was found.
    ForceRuntime,
}

/// Final disposition for an obligation after applying runtime-check policy.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RuntimeDisposition {
    /// The obligation was discharged statically.
    Proved,
    /// The obligation will be enforced dynamically at runtime.
    RuntimeChecked { note: String },
    /// The obligation has a concrete counterexample.
    Failed,
    /// Verification was inconclusive and no runtime fallback was applied.
    Unknown { reason: String },
    /// Verification timed out and no runtime fallback was applied.
    Timeout { timeout_ms: u64 },
    /// Compilation should fail because static proof was required.
    CompileError { reason: String },
}

const FORCED_RUNTIME_NOTE: &str = "forced by #[trust(runtime)]";

/// Classify a solver result into a static, runtime-checked, or compile-error
/// disposition after applying the requested runtime-check policy.
#[must_use]
pub fn classify_runtime_disposition(
    vc_kind: &VcKind,
    result: &VerificationResult,
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
) -> RuntimeDisposition {
    match result {
        VerificationResult::Failed { .. } => RuntimeDisposition::Failed,
        VerificationResult::Proved { .. } => {
            if policy == RuntimeCheckPolicy::ForceRuntime {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            } else {
                RuntimeDisposition::Proved
            }
        }
        VerificationResult::Unknown { reason, .. } => match policy {
            RuntimeCheckPolicy::Auto if vc_kind.has_runtime_fallback(overflow_checks) => {
                RuntimeDisposition::RuntimeChecked { note: vc_kind.description() }
            }
            RuntimeCheckPolicy::Auto => RuntimeDisposition::Unknown { reason: reason.clone() },
            RuntimeCheckPolicy::ForceStatic => RuntimeDisposition::CompileError {
                reason: format!(
                    "`#[trust(static)]` requires a static proof, but the solver returned unknown: {reason}"
                ),
            },
            RuntimeCheckPolicy::ForceRuntime => {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            }
        },
        VerificationResult::Timeout { timeout_ms, .. } => match policy {
            RuntimeCheckPolicy::Auto if vc_kind.has_runtime_fallback(overflow_checks) => {
                RuntimeDisposition::RuntimeChecked { note: vc_kind.description() }
            }
            RuntimeCheckPolicy::Auto => RuntimeDisposition::Timeout { timeout_ms: *timeout_ms },
            RuntimeCheckPolicy::ForceStatic => RuntimeDisposition::CompileError {
                reason: format!(
                    "`#[trust(static)]` requires a static proof, but verification timed out after {timeout_ms}ms"
                ),
            },
            RuntimeCheckPolicy::ForceRuntime => {
                RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.to_string() }
            }
        },
    }
}

/// A counterexample: concrete variable assignments that violate the property.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Counterexample {
    pub assignments: Vec<(String, CounterexampleValue)>,
    /// Trust: Optional step-by-step execution trace from BMC counterexample.
    /// Each step maps to one unrolling depth with variable assignments and
    /// an optional MIR basic block index.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trace: Option<CounterexampleTrace>,
}

impl Counterexample {
    pub fn new(assignments: Vec<(String, CounterexampleValue)>) -> Self {
        Counterexample { assignments, trace: None }
    }

    /// Trust: Create a counterexample with an execution trace from BMC.
    pub fn with_trace(
        assignments: Vec<(String, CounterexampleValue)>,
        trace: CounterexampleTrace,
    ) -> Self {
        Counterexample { assignments, trace: Some(trace) }
    }
}

impl std::fmt::Display for Counterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts: Vec<String> =
            self.assignments.iter().map(|(name, val)| format!("{name} = {val}")).collect();
        write!(f, "{}", parts.join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CounterexampleValue {
    Bool(bool),
    // Trust: serde_json without `arbitrary_precision` cannot deserialize a bare
    // JSON number into i128/u128 (it errors "i128 is not supported"). Because a
    // failed obligation's counterexample rides the SAME transport line as any
    // co-located proved obligations, that error fails the whole line and silently
    // downgrades every proved obligation on it to `unknown` (lost proof credit).
    // Keep 64-bit values as ordinary JSON numbers, serialize wider values as
    // decimal strings, and deserialize both forms through `deserialize_any`.
    // This makes the emitter/parser pair closed under round-trip without an
    // `arbitrary_precision` switch.
    Int(
        #[serde(
            serialize_with = "serialize_flexible_i128",
            deserialize_with = "deserialize_flexible_i128"
        )]
        i128,
    ),
    Uint(
        #[serde(
            serialize_with = "serialize_flexible_u128",
            deserialize_with = "deserialize_flexible_u128"
        )]
        u128,
    ),
    Float(f64),
}

/// Serialize an `i128` without producing JSON that our own deserializer cannot
/// read. JSON numbers outside serde_json's signed/unsigned 64-bit range are
/// emitted as decimal strings; binary formats retain their native `i128`
/// representation.
#[allow(clippy::trivially_copy_pass_by_ref)] // serde's serialize_with signature
fn serialize_flexible_i128<S>(value: &i128, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    if !serializer.is_human_readable() {
        return serializer.serialize_i128(*value);
    }
    if let Ok(value) = i64::try_from(*value) {
        serializer.serialize_i64(value)
    } else if let Ok(value) = u64::try_from(*value) {
        serializer.serialize_u64(value)
    } else {
        serializer.serialize_str(&value.to_string())
    }
}

/// Serialize a `u128` as a JSON number when it fits serde_json's supported
/// range and as a decimal string otherwise. Binary formats retain `u128`.
#[allow(clippy::trivially_copy_pass_by_ref)] // serde's serialize_with signature
fn serialize_flexible_u128<S>(value: &u128, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    if !serializer.is_human_readable() {
        return serializer.serialize_u128(*value);
    }
    if let Ok(value) = u64::try_from(*value) {
        serializer.serialize_u64(value)
    } else {
        serializer.serialize_str(&value.to_string())
    }
}

/// Deserialize an `i128` from a JSON number (via `u64`/`i64`), a native
/// `i128`/`u128`, or a decimal string — the fail-closed workaround for
/// serde_json's missing bare-number `i128` support (see `CounterexampleValue`).
fn deserialize_flexible_i128<'de, D>(deserializer: D) -> Result<i128, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct FlexI128;
    impl serde::de::Visitor<'_> for FlexI128 {
        type Value = i128;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("an integer as a JSON number or its decimal string")
        }
        fn visit_i64<E: serde::de::Error>(self, v: i64) -> Result<i128, E> {
            Ok(i128::from(v))
        }
        fn visit_u64<E: serde::de::Error>(self, v: u64) -> Result<i128, E> {
            Ok(i128::from(v))
        }
        fn visit_i128<E: serde::de::Error>(self, v: i128) -> Result<i128, E> {
            Ok(v)
        }
        fn visit_u128<E: serde::de::Error>(self, v: u128) -> Result<i128, E> {
            i128::try_from(v).map_err(serde::de::Error::custom)
        }
        fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<i128, E> {
            v.parse::<i128>().map_err(serde::de::Error::custom)
        }
    }
    if deserializer.is_human_readable() {
        deserializer.deserialize_any(FlexI128)
    } else {
        deserializer.deserialize_i128(FlexI128)
    }
}

/// Deserialize a `u128` from a JSON number (via `u64`/`i64`), a native
/// `u128`/`i128`, or a decimal string — the `u128` twin of
/// [`deserialize_flexible_i128`].
fn deserialize_flexible_u128<'de, D>(deserializer: D) -> Result<u128, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct FlexU128;
    impl serde::de::Visitor<'_> for FlexU128 {
        type Value = u128;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("a non-negative integer as a JSON number or its decimal string")
        }
        fn visit_i64<E: serde::de::Error>(self, v: i64) -> Result<u128, E> {
            u128::try_from(v).map_err(serde::de::Error::custom)
        }
        fn visit_u64<E: serde::de::Error>(self, v: u64) -> Result<u128, E> {
            Ok(u128::from(v))
        }
        fn visit_i128<E: serde::de::Error>(self, v: i128) -> Result<u128, E> {
            u128::try_from(v).map_err(serde::de::Error::custom)
        }
        fn visit_u128<E: serde::de::Error>(self, v: u128) -> Result<u128, E> {
            Ok(v)
        }
        fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<u128, E> {
            v.parse::<u128>().map_err(serde::de::Error::custom)
        }
    }
    if deserializer.is_human_readable() {
        deserializer.deserialize_any(FlexU128)
    } else {
        deserializer.deserialize_u128(FlexU128)
    }
}

impl std::fmt::Display for CounterexampleValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CounterexampleValue::Bool(b) => write!(f, "{b}"),
            CounterexampleValue::Int(n) => write!(f, "{n}"),
            CounterexampleValue::Uint(n) => write!(f, "{n}"),
            CounterexampleValue::Float(n) => write!(f, "{n}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Trust: BMC counterexample trace types
// ---------------------------------------------------------------------------

/// Trust: Step-by-step execution trace extracted from a BMC counterexample.
///
/// Each step corresponds to one unrolling depth in the BMC encoding. The trace
/// maps variable assignments at each step back to MIR basic block indices,
/// enabling source-level debugging of counterexamples.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CounterexampleTrace {
    /// Ordered sequence of trace steps, one per BMC unrolling depth.
    pub steps: Vec<TraceStep>,
}

impl CounterexampleTrace {
    /// Create a trace from a list of steps.
    pub fn new(steps: Vec<TraceStep>) -> Self {
        Self { steps }
    }

    /// Number of steps in the trace.
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the trace is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

impl std::fmt::Display for CounterexampleTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for step in &self.steps {
            write!(f, "  step {}: ", step.step)?;
            if let Some(ref pp) = step.program_point {
                write!(f, "[{pp}] ")?;
            }
            let assigns: Vec<String> =
                step.assignments.iter().map(|(k, v)| format!("{k}={v}")).collect();
            writeln!(f, "{}", assigns.join(", "))?;
        }
        Ok(())
    }
}

/// Trust: A single step in a BMC counterexample trace.
///
/// Captures the variable assignments at one unrolling depth, plus an optional
/// mapping back to the MIR basic block that this step corresponds to.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraceStep {
    /// The BMC unrolling step index (0-based).
    pub step: u32,
    /// Variable assignments at this step, keyed by variable name.
    pub assignments: std::collections::BTreeMap<String, String>,
    /// Optional program point label (e.g., "bb3" for MIR basic block 3).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub program_point: Option<String>,
}

/// Summary of verification results for a function.
#[derive(Debug, Clone, Serialize)]
pub struct FunctionReport {
    pub function: String,
    pub proved: Vec<ProvedProperty>,
    pub failed: Vec<FailedProperty>,
    pub unknown: Vec<UnknownProperty>,
}

/// Function-level summary with obligation counts and timing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSummary {
    /// Total obligations checked.
    pub total_obligations: usize,
    /// Number proved safe.
    pub proved: usize,
    /// Number checked at runtime instead of proved statically.
    #[serde(default)]
    pub runtime_checked: usize,
    /// Number with counterexamples (violations).
    pub failed: usize,
    /// Number unknown or timed out.
    pub unknown: usize,
    /// Number timed out.
    #[serde(default)]
    pub timed_out: usize,
    /// Number of hardened-boundary design mandates (source must move off a
    /// raw/opaque API). Tracked separately so they never count as proved or
    /// failed — they are design requirements, not proof outcomes.
    #[serde(default)]
    pub design_requirements: usize,
    /// Backend failures that could not be attributed to one stable obligation ID.
    #[serde(default)]
    pub unattributed_failed: usize,
    /// Backend unknown/timeout results that could not be attributed to one stable obligation ID.
    #[serde(default)]
    pub unattributed_unknown: usize,
    /// Backend proofs that could not be attributed to one stable obligation ID.
    ///
    /// These are intentionally not counted as proved obligations.
    #[serde(default)]
    pub unattributed_proved: usize,
    /// Total solver wall-clock time in milliseconds for this function.
    pub total_time_ms: u64,
    /// Highest proof level achieved across all obligations.
    pub max_proof_level: Option<ProofLevel>,
    /// Overall verdict for the function.
    pub verdict: FunctionVerdict,
}

/// Overall verification verdict for one scope — a function, or the crate that
/// aggregates them.
///
/// A crate verdict is not a different judgement from a function verdict; it is
/// the same judgement over a wider set of obligations, decided by the same rule
/// from the same counts. Both scopes therefore name one type ([`FunctionVerdict`]
/// and [`CrateVerdict`] are aliases of it), and the rule itself lives once, in
/// [`ScopeVerdict::from_counts`]. Two copies of a proof-relevant classification
/// drift silently; one copy cannot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ScopeVerdict {
    /// Every obligation in scope was proved safe.
    Verified,
    /// No violations, but some obligations in scope rest on runtime checks.
    RuntimeChecked,
    /// At least one obligation in scope has a counterexample.
    HasViolations,
    /// No violations, but some obligations in scope are unresolved.
    Inconclusive,
    /// No verification obligations existed in scope.
    NoObligations,
}

/// Obligation counts for one scope, as the verdict rule reads them.
///
/// The unattributed fields hold backend results that could not be tied to a
/// stable obligation ID. They are residual verification work even though no
/// concrete obligation row survived attribution, so they must reach the verdict
/// rule — a scope whose only signal is an unattributed refutation is not
/// `NoObligations`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ScopeVerdictCounts {
    /// Every obligation attributed to this scope.
    pub total: usize,
    /// Obligations proved safe.
    pub proved: usize,
    /// Obligations resting on a runtime check instead of a static proof.
    pub runtime_checked: usize,
    /// Obligations with a counterexample.
    pub failed: usize,
    /// Obligations with no verdict either way.
    pub unknown: usize,
    /// Refutations that could not be attributed to one stable obligation ID.
    pub unattributed_failed: usize,
    /// Unresolved results that could not be attributed to one stable obligation ID.
    pub unattributed_unknown: usize,
    /// Proof claims that could not be attributed to one stable obligation ID.
    /// These never count as proved — an unbound proof claim is residual work.
    pub unattributed_proved: usize,
}

impl From<&FunctionSummary> for ScopeVerdictCounts {
    /// Read the verdict inputs out of a summary that has already been counted.
    ///
    /// `timed_out` and `design_requirements` are deliberately absent: a timeout
    /// is already inside `unknown`, and a design mandate is not a discharge
    /// target at all. Both would double-count if the verdict rule saw them
    /// again — but neither is dropped from the judgement, because an obligation
    /// they account for still raises `total` above `proved`, which is what makes
    /// the scope fail closed to `Inconclusive`.
    fn from(summary: &FunctionSummary) -> Self {
        Self {
            total: summary.total_obligations,
            proved: summary.proved,
            runtime_checked: summary.runtime_checked,
            failed: summary.failed,
            unknown: summary.unknown,
            unattributed_failed: summary.unattributed_failed,
            unattributed_unknown: summary.unattributed_unknown,
            unattributed_proved: summary.unattributed_proved,
        }
    }
}

impl ScopeVerdict {
    /// The one verdict rule, for every scope.
    ///
    /// `Verified` is a POSITIVE invariant: it requires `proved == total &&
    /// proved > 0`, not merely the absence of bad news. An obligation counted
    /// by none of the buckets — a future `#[non_exhaustive]` [`ObligationOutcome`]
    /// variant that a cross-crate match had to leave under a `_` arm — makes
    /// `proved < total`, so the verdict fails closed to `Inconclusive` rather
    /// than being promoted to a false `Verified`.
    ///
    /// Bad news is read before the empty-inventory case so an unattributed
    /// refutation or unbound proof claim can never be erased into
    /// `NoObligations`.
    #[must_use]
    pub const fn from_counts(counts: ScopeVerdictCounts) -> Self {
        if counts.failed > 0 || counts.unattributed_failed > 0 {
            Self::HasViolations
        } else if counts.unknown > 0
            || counts.unattributed_unknown > 0
            || counts.unattributed_proved > 0
        {
            Self::Inconclusive
        } else if counts.total == 0 {
            Self::NoObligations
        } else if counts.runtime_checked > 0 {
            Self::RuntimeChecked
        } else if counts.proved == counts.total && counts.proved > 0 {
            Self::Verified
        } else {
            Self::Inconclusive
        }
    }
}

/// Overall verification verdict for a function. See [`ScopeVerdict`].
pub type FunctionVerdict = ScopeVerdict;

/// Overall crate-level verification verdict. See [`ScopeVerdict`].
pub type CrateVerdict = ScopeVerdict;

/// Per-obligation detail in the JSON report. Every obligation gets one of these,
/// regardless of outcome. This is the atomic unit of the report.
#[derive(Debug, Clone, Serialize)]
pub struct ObligationReport {
    /// Stable router obligation ID, when the report came from a native per-obligation path.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_id: Option<String>,
    /// Human-readable description of the property checked.
    pub description: String,
    /// Structured kind tag for machine consumption (e.g., "arithmetic_overflow").
    pub kind: String,
    /// Proof level this obligation belongs to.
    pub proof_level: ProofLevel,
    /// Source location where the obligation originates.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Verification outcome.
    pub outcome: ObligationOutcome,
    /// Which solver produced this result.
    pub solver: String,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// Proof evidence (reasoning + assurance) for proved obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<ProofEvidence>,
    /// Native/router proof evidence tied to this exact obligation ID.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_evidence: Option<ObligationProofEvidenceReport>,
    /// Raw compiler/router transport evidence tied to this exact obligation ID.
    ///
    /// This is intentionally separate from `proof_evidence`: transport rows can
    /// be unsupported, rejected, or missing artifacts. Only `proof_evidence`
    /// represents publishable proof-grade evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub transport_evidence: Option<ObligationTransportEvidenceReport>,
}

// ObligationLocation alias removed — use SourceSpan directly.

/// Where a per-obligation proof evidence record came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
pub enum ObligationEvidenceProvenanceReport {
    /// A legacy router/per-VC path produced this result directly for the obligation.
    RouterAttributed,
    /// A native backend produced a result with a stable obligation identity.
    NativeBackend { verifier: String },
}

/// Proof evidence preserved for one stable obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationProofEvidenceReport {
    /// Verification suite or integration family for structured native proof evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub suite: Option<String>,
    /// Backend or router that produced the proof evidence.
    pub backend: String,
    /// Backend request/correlation ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub request_id: Option<String>,
    /// Backend proof/certificate/run ID, or the exact content-addressed
    /// certificate identity for an identity-bound kernel proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_id: Option<String>,
    /// Backend-native obligation or IR ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_id: Option<String>,
    /// Machine-stable proof status, when this report came from structured transport.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status: Option<TransportProofStatus>,
    /// How the proof evidence was attributed to this obligation.
    pub provenance: ObligationEvidenceProvenanceReport,
    /// Legacy proof-strength label preserved from the backend result.
    pub strength: ProofStrength,
    /// Normalized proof-evidence model derived from `strength`.
    pub evidence: ProofEvidence,
    /// Raw proof certificate bytes, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_certificate: Option<Vec<u8>>,
    /// Structured native TrustIr evidence carried by the full-verifier transport.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_trust_ir: Option<TransportNativeTrustIrEvidence>,
    /// Structured proof artifacts carried by the full-verifier transport.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_transport_evidence_artifacts"
    )]
    pub artifacts: Vec<TransportEvidenceArtifact>,
    /// Structured proof diagnostics carried by the full-verifier transport.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<TransportEvidenceDiagnostic>,
    /// Solver/backend warnings emitted while producing the proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_warnings: Option<Vec<String>>,
}

/// Raw transport evidence preserved for one stable obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationTransportEvidenceReport {
    /// Stable obligation ID from compiler transport, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_id: Option<String>,
    /// Compiler digest of the complete canonical VC payload. This remains
    /// useful for offline correlation, but is diagnostic-only and cannot
    /// recreate the live verifier authority that accepted the claim.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim_digest_sha256: Option<String>,
    /// Exact compiler VC classification, including parameterized temporal and
    /// deep-property fields that the compact report tag cannot reconstruct.
    /// This remains diagnostic metadata and never recreates live authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub typed_kind: Option<Box<VcKind>>,
    /// Structured native TrustIr evidence carried by the compiler transport.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_trust_ir: Option<TransportNativeTrustIrEvidence>,
    /// Structured proof evidence carried by the compiler transport.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_evidence: Option<TransportProofEvidence>,
    /// Kernel-certified runtime-monitor status carried by the compiler for
    /// this exact contract-derived obligation. This is execution evidence for
    /// the proposition, never static proof credit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub monitor: Option<TransportMonitorEvidence>,
}

/// Structured verification outcome for a single obligation.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "status")]
#[non_exhaustive]
pub enum ObligationOutcome {
    /// Property proved safe — no violation possible.
    #[serde(rename = "proved")]
    Proved { strength: ProofStrength },
    /// Property violated — counterexample available.
    #[serde(rename = "failed")]
    Failed {
        #[serde(skip_serializing_if = "Option::is_none")]
        counterexample: Option<CounterexampleReport>,
    },
    /// Solver could not determine outcome.
    #[serde(rename = "unknown")]
    Unknown { reason: String },
    /// Property was checked dynamically at runtime rather than proved statically.
    #[serde(rename = "runtime_checked")]
    RuntimeChecked {
        #[serde(skip_serializing_if = "Option::is_none")]
        note: Option<String>,
    },
    /// Solver timed out.
    #[serde(rename = "timeout")]
    Timeout { timeout_ms: u64 },
    /// a hardened-boundary DESIGN MANDATE — the source must
    /// move off a raw/opaque API (e.g. a raw path or process call). This is NOT
    /// a proof obligation and NOT a proof failure: it is emitted for hardened
    /// boundaries whose violation condition is the tautology `true`, which can
    /// never be discharged by construction. It rides its own channel so it
    /// never inflates `failed`/`unknown` and never renders as `FAILED`.
    #[serde(rename = "design_requirement")]
    DesignRequirement { detail: String },
}

/// Private serde representation for an obligation outcome.
///
/// The public [`ObligationOutcome`] can be constructed as `Proved` by a live,
/// trusted report builder, but a serialized enum has no process-local verifier
/// capability. Keeping the raw wire enum private lets every public serde entry
/// point fail closed while the canonical saved-report decoder can still capture
/// the producer's untrusted pre-sanitization claim.
#[derive(Deserialize)]
#[serde(tag = "status")]
enum ObligationOutcomeWire {
    #[serde(rename = "proved")]
    Proved { strength: ProofStrength },
    #[serde(rename = "failed")]
    Failed {
        #[serde(skip_serializing_if = "Option::is_none")]
        counterexample: Option<CounterexampleReport>,
    },
    #[serde(rename = "unknown")]
    Unknown { reason: String },
    #[serde(rename = "runtime_checked")]
    RuntimeChecked {
        #[serde(skip_serializing_if = "Option::is_none")]
        note: Option<String>,
    },
    #[serde(rename = "timeout")]
    Timeout { timeout_ms: u64 },
    #[serde(rename = "design_requirement")]
    DesignRequirement { detail: String },
}

impl ObligationOutcomeWire {
    fn into_public_untrusted(self) -> ObligationOutcome {
        match self {
            Self::Proved { strength } => ObligationOutcome::Proved { strength },
            Self::Failed { counterexample } => ObligationOutcome::Failed { counterexample },
            Self::Unknown { reason } => ObligationOutcome::Unknown { reason },
            Self::RuntimeChecked { note } => ObligationOutcome::RuntimeChecked { note },
            Self::Timeout { timeout_ms } => ObligationOutcome::Timeout { timeout_ms },
            Self::DesignRequirement { detail } => ObligationOutcome::DesignRequirement { detail },
        }
    }

    fn into_public_fail_closed(self) -> ObligationOutcome {
        match self {
            Self::Proved { .. } => ObligationOutcome::Unknown {
                reason: DIRECT_DESERIALIZED_PROVED_DOWNGRADE_REASON.to_string(),
            },
            Self::RuntimeChecked { .. } => ObligationOutcome::Unknown {
                reason: DIRECT_DESERIALIZED_RUNTIME_CHECKED_DOWNGRADE_REASON.to_string(),
            },
            other => other.into_public_untrusted(),
        }
    }
}

const DIRECT_DESERIALIZED_PROVED_DOWNGRADE_REASON: &str = "deserialized proved outcome has no live verifier replay capability; serialized proof evidence is diagnostic-only and cannot carry proof authority";
const DIRECT_DESERIALIZED_RUNTIME_CHECKED_DOWNGRADE_REASON: &str = "deserialized runtime_checked outcome has no live authenticated compiler/monitor capability; serialized monitor evidence is diagnostic-only and cannot carry runtime-check authority";

impl<'de> Deserialize<'de> for ObligationOutcome {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(ObligationOutcomeWire::deserialize(deserializer)?.into_public_fail_closed())
    }
}

impl From<&ObligationOutcome> for Outcome {
    /// Project a report obligation onto the shared outcome vocabulary.
    ///
    /// [`ObligationOutcome`] is this taxonomy plus the payload each conclusion
    /// carries (the proof strength, the counterexample, the reason text). The
    /// projection drops the payload and keeps the conclusion, so the report DTO
    /// and the transport row are guaranteed to classify a row identically
    /// instead of each re-deriving the classification from its own match.
    ///
    /// `DesignRequirement` is not a conclusion about an obligation at all — it
    /// is a hardened-boundary design mandate whose violation formula is the
    /// tautology `true`, so no decision procedure can ever discharge it. It
    /// projects to `Unsupported`, the closest honest statement: the claim is
    /// outside anything a backend can encode. Report consumers that need to
    /// keep mandates out of proof denominators must read the variant itself,
    /// not this projection.
    fn from(outcome: &ObligationOutcome) -> Self {
        match outcome {
            ObligationOutcome::Proved { .. } => Self::Proved,
            ObligationOutcome::Failed { .. } => Self::Failed,
            ObligationOutcome::Unknown { .. } => Self::Unknown,
            ObligationOutcome::RuntimeChecked { .. } => Self::RuntimeChecked,
            ObligationOutcome::Timeout { .. } => Self::Timeout,
            ObligationOutcome::DesignRequirement { .. } => Self::Unsupported,
        }
    }
}

/// Machine-friendly counterexample with named variables and typed values.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleReport {
    pub variables: Vec<CounterexampleVariable>,
}

/// A single variable assignment in a counterexample.
///
/// Values are represented as strings because serde_json does not support
/// i128/u128 natively. The `value_type` field provides type information
/// for machine consumers that need to parse the value.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleVariable {
    pub name: String,
    /// The value as a string (supports arbitrarily large integers).
    pub value: String,
    /// Type of the value for machine parsing: "bool", "int", "uint", "float".
    pub value_type: String,
    /// Display-friendly string representation of the value.
    pub display: String,
}

/// Enriched per-function report with obligations and summary.
#[derive(Debug, Clone, Serialize)]
pub struct FunctionProofReport {
    /// Fully qualified function name.
    pub function: String,
    /// Function-level summary.
    pub summary: FunctionSummary,
    /// Per-obligation details, in source order.
    pub obligations: Vec<ObligationReport>,
}

/// Private raw function/obligation mirrors used by the canonical saved-report
/// boundary. Their field schema intentionally matches the public DTOs exactly;
/// only the outcome type differs so [`JsonProofReport::decode_saved_json`] can
/// retain an observational receipt for a serialized `proved` claim before the
/// claim is downgraded.
#[derive(Deserialize)]
struct FunctionProofReportWire {
    function: String,
    summary: FunctionSummary,
    obligations: Vec<ObligationReportWire>,
}

#[derive(Deserialize)]
struct ObligationReportWire {
    #[serde(default)]
    obligation_id: Option<String>,
    description: String,
    kind: String,
    proof_level: ProofLevel,
    location: Option<SourceSpan>,
    outcome: ObligationOutcomeWire,
    solver: String,
    time_ms: u64,
    #[serde(default)]
    evidence: Option<ProofEvidence>,
    #[serde(default)]
    proof_evidence: Option<ObligationProofEvidenceReport>,
    #[serde(default)]
    transport_evidence: Option<ObligationTransportEvidenceReport>,
}

impl ObligationReportWire {
    fn into_public_untrusted(self) -> ObligationReport {
        ObligationReport {
            obligation_id: self.obligation_id,
            description: self.description,
            kind: self.kind,
            proof_level: self.proof_level,
            location: self.location,
            outcome: self.outcome.into_public_untrusted(),
            solver: self.solver,
            time_ms: self.time_ms,
            evidence: self.evidence,
            proof_evidence: self.proof_evidence,
            transport_evidence: self.transport_evidence,
        }
    }

    fn into_public_fail_closed(self) -> ObligationReport {
        let mut report = ObligationReport {
            obligation_id: self.obligation_id,
            description: self.description,
            kind: self.kind,
            proof_level: self.proof_level,
            location: self.location,
            outcome: self.outcome.into_public_fail_closed(),
            solver: self.solver,
            time_ms: self.time_ms,
            evidence: self.evidence,
            proof_evidence: self.proof_evidence,
            transport_evidence: self.transport_evidence,
        };
        scrub_deserialized_monitor_claim(&mut report);
        report
    }
}

impl<'de> Deserialize<'de> for ObligationReport {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(ObligationReportWire::deserialize(deserializer)?.into_public_fail_closed())
    }
}

/// Serialized monitor metadata cannot remain on the public report DTO after
/// deserialization because every report formatter maps this field directly
/// onto the §7 executability
/// grade. Retaining it would let hand-edited JSON render `Monitored` without the
/// compiler's process-local monitor authority. Live, in-memory compiler reports
/// never pass this boundary and retain their exact monitor evidence.
fn scrub_deserialized_monitor_claim(report: &mut ObligationReport) {
    if let Some(transport) = &mut report.transport_evidence {
        transport.monitor = None;
    }
}

impl FunctionProofReportWire {
    fn into_public_untrusted(self) -> FunctionProofReport {
        FunctionProofReport {
            function: self.function,
            summary: self.summary,
            obligations: self
                .obligations
                .into_iter()
                .map(ObligationReportWire::into_public_untrusted)
                .collect(),
        }
    }

    fn into_public_fail_closed(self) -> FunctionProofReport {
        let mut report = FunctionProofReport {
            function: self.function,
            summary: self.summary,
            obligations: self
                .obligations
                .into_iter()
                .map(ObligationReportWire::into_public_fail_closed)
                .collect(),
        };
        recompute_deserialized_function_summary(&mut report);
        report
    }
}

impl<'de> Deserialize<'de> for FunctionProofReport {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(FunctionProofReportWire::deserialize(deserializer)?.into_public_fail_closed())
    }
}

/// Crate-level metadata for the proof report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportMetadata {
    /// JSON schema version for this report format.
    pub schema_version: String,
    /// Trust version that produced this report.
    pub trust_version: String,
    /// ISO 8601 timestamp when the report was generated.
    pub timestamp: String,
    /// Total wall-clock time for all verification in milliseconds.
    pub total_time_ms: u64,
    /// Per-obligation solver timeout selected by the frontend, in
    /// milliseconds. Absent for producers and older reports that do not carry
    /// canonical timeout policy metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_ms: Option<u64>,
    /// Per-function cooperative wall-clock verification budget selected by
    /// the frontend, in milliseconds. Absent for producers and older reports
    /// that do not have a canonical function-budget policy.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_budget_ms: Option<u64>,
}

/// Crate-level summary aggregating all function results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrateSummary {
    /// Total functions analyzed.
    pub functions_analyzed: usize,
    /// Functions with all obligations proved.
    pub functions_verified: usize,
    /// Functions with no violations, but some runtime-checked obligations.
    #[serde(default)]
    pub functions_runtime_checked: usize,
    /// Functions with at least one violation.
    pub functions_with_violations: usize,
    /// Functions with inconclusive results.
    pub functions_inconclusive: usize,
    /// Total obligations across all functions.
    pub total_obligations: usize,
    /// Obligations proved safe. This is a single blended count and carries NO
    /// assurance information: a kernel-certified proof and a merely solver-trusted
    /// one both land here. For the deviation-from-vanilla breakdown by strength of
    /// basis (certified / smt-backed / runtime-checked / unknown / assumed-trusted)
    /// use [`TrustSurface::from_functions`], which the report renders at session end.
    pub total_proved: usize,
    /// Obligations checked at runtime instead of proved statically.
    #[serde(default)]
    pub total_runtime_checked: usize,
    /// Obligations with counterexamples.
    pub total_failed: usize,
    /// Obligations unknown or timed out.
    pub total_unknown: usize,
    /// Obligations timed out.
    #[serde(default)]
    pub total_timed_out: usize,
    /// Hardened-boundary design mandates across all functions (separate bucket;
    /// never counted as proved or failed).
    #[serde(default)]
    pub total_design_requirements: usize,
    /// Backend failures that could not be attributed to one stable obligation ID.
    #[serde(default)]
    pub total_unattributed_failed: usize,
    /// Backend unknown/timeout results that could not be attributed to one stable obligation ID.
    #[serde(default)]
    pub total_unattributed_unknown: usize,
    /// Backend proofs that could not be attributed to one stable obligation ID.
    ///
    /// These are intentionally not counted as proved obligations.
    #[serde(default)]
    pub total_unattributed_proved: usize,
    /// Native proof engine statuses for proof-grade evidence.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub proof_grade_engine_statuses: Vec<ProofGradeEngineStatus>,
    /// Overall crate verdict.
    pub verdict: CrateVerdict,
}

/// Status of a native proof engine for proof-grade evidence.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct ProofGradeEngineStatus {
    /// Engine name (e.g., "trust-mc", "trust-wp", "trust-vc").
    pub engine: String,
    /// Total obligations encountered by this engine.
    pub total_obligations: usize,
    /// Obligations that reached proof-grade status.
    pub proof_grade_obligations: usize,
    /// Number of functions where this engine was the primary route.
    pub functions_routed: usize,
}

/// Summarize proof-grade engine statuses from a list of function reports.
pub fn summarize_proof_grade_engine_statuses(
    functions: &[FunctionProofReport],
) -> Vec<ProofGradeEngineStatus> {
    use std::collections::{BTreeMap, HashSet};

    let mut engines: BTreeMap<String, ProofGradeEngineStatus> = BTreeMap::new();

    for func in functions {
        let mut functions_routed = HashSet::new();

        for obl in &func.obligations {
            if let Some(proof) = &obl.proof_evidence
                && let Some(suite) = &proof.suite
            {
                let entry = engines.entry(suite.clone()).or_insert_with(|| {
                    ProofGradeEngineStatus { engine: suite.clone(), ..Default::default() }
                });
                entry.total_obligations += 1;
                // this runs on DESERIALIZED report functions, so
                // `proof.status` is an untrusted field — a hand-edited report.json
                // can set status=Proved with `strength.assurance = Unchecked`. Only
                // count toward `proof_grade_obligations` when the proof's assurance
                // meets the reported-proof floor (SmtBacked); otherwise it stays in
                // `total_obligations` only. Fail closed, never a false-PROVE count.
                if matches!(obl.outcome, ObligationOutcome::Proved { .. })
                    && proof.status == Some(TransportProofStatus::Proved)
                    && proof.strength.assurance.meets_reporting_floor()
                {
                    entry.proof_grade_obligations += 1;
                }
                functions_routed.insert(suite.clone());
            }
        }

        for engine in functions_routed {
            if let Some(entry) = engines.get_mut(&engine) {
                entry.functions_routed += 1;
            }
        }
    }

    engines.into_values().collect()
}

// Trust: per-compile "Trust Surface" — how the proof report deviates from what
// vanilla rustc accepts unchanged. Vanilla rustc compiles this code with zero of
// these obligations; Trust adds them and classifies each by the *strength of the
// basis* it rests on, not by a single blended `proved` total. The collapsed
// `CrateSummary::total_proved` answers "how many obligations are green"; it cannot
// answer "how many are independently certified vs solver-backed vs merely trusted",
// which is the only honest way to state the assurance Trust actually delivers.
//
// This is a pure aggregation over the existing per-obligation classification
// (`ObligationOutcome` + `ProofStrength::assurance`). It invents no proof result:
// every count comes from an obligation row that already carries that outcome and
// assurance. It is derived from the obligation lists (the source of truth) rather
// than stored, so it always reconciles with the per-obligation detail and can
// never go stale after `JsonProofReport::sanitize_deserialized` re-gates and
// downgrades obligations.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustSurface {
    /// Total obligations Trust added on top of what vanilla rustc accepts.
    pub total_obligations: usize,
    /// Proved with a kernel-reconstructed, independently re-checked proof
    /// (`AssuranceLevel::Certified`) — soundness reduces to the verified kernel.
    pub certified: usize,
    /// Proved with a solver/SMT-backed proof (`AssuranceLevel::SmtBacked` or the
    /// legacy `Sound`) — sound modulo the trusted solver/checker, but not
    /// kernel-reconstructed.
    pub smt_backed: usize,
    /// Discharged by an inserted runtime check rather than a static proof
    /// (`ObligationOutcome::RuntimeChecked`).
    pub runtime_checked: usize,
    /// Left unknown — the solver could not decide and no runtime fallback applied
    /// (`ObligationOutcome::Unknown`/`Timeout`).
    pub unknown: usize,
    /// "Proved" only by resting on an assumed contract / bounded basis
    /// (`AssuranceLevel::Trusted` or `BoundedSound`): a known assumption was taken
    /// on faith, not independently discharged.
    pub contract_assumed: usize,
    /// "Proved" only by fully trusting the solver verdict with no validation at
    /// all (`AssuranceLevel::Unchecked`/`Heuristic`). The weakest rung.
    pub fully_trusted: usize,
    /// Refuted — a concrete counterexample (`ObligationOutcome::Failed`). Not part
    /// of the "additionally proved" story; tracked so the surface reconciles with
    /// the crate totals and a violation never hides.
    pub failed: usize,
}

impl TrustSurface {
    /// Derive the Trust Surface from per-function reports by classifying every
    /// obligation. The obligation list is the source of truth, so this stays in
    /// sync with `sanitize_deserialized` (which re-gates those same rows).
    #[must_use]
    pub fn from_functions(functions: &[FunctionProofReport]) -> Self {
        let mut surface = Self::default();
        for func in functions {
            for obl in &func.obligations {
                surface.add_outcome(&obl.outcome);
            }
        }
        surface
    }

    fn add_outcome(&mut self, outcome: &ObligationOutcome) {
        match outcome {
            ObligationOutcome::Proved { strength } => {
                self.total_obligations += 1;
                match &strength.assurance {
                    AssuranceLevel::Certified => self.certified += 1,
                    AssuranceLevel::SmtBacked | AssuranceLevel::Sound => self.smt_backed += 1,
                    AssuranceLevel::Trusted | AssuranceLevel::BoundedSound { .. } => {
                        self.contract_assumed += 1
                    }
                    AssuranceLevel::Unchecked | AssuranceLevel::Heuristic => {
                        self.fully_trusted += 1
                    } // `AssuranceLevel` is `#[non_exhaustive]`, but that has no effect
                      // within its defining crate, so this match must stay exhaustive
                      // without a wildcard. A new variant added later will fail-closed
                      // here as a compile error — bucket it as `fully_trusted` (the
                      // weakest assurance) rather than reading it as certified.
                }
            }
            ObligationOutcome::RuntimeChecked { .. } => {
                self.total_obligations += 1;
                self.runtime_checked += 1;
            }
            ObligationOutcome::Unknown { .. } | ObligationOutcome::Timeout { .. } => {
                self.total_obligations += 1;
                self.unknown += 1;
            }
            ObligationOutcome::Failed { .. } => {
                self.total_obligations += 1;
                self.failed += 1;
            }
            // A hardened-boundary design mandate is not a proof outcome and never
            // counts toward any surface bucket; a future outcome variant is left
            // uncounted rather than minting a phantom proof.
            ObligationOutcome::DesignRequirement { .. } => {}
        }
    }

    /// Total obligations Trust additionally proved statically (certified +
    /// smt-backed). Excludes contract-assumed/fully-trusted, which rest on an
    /// assumption rather than an independent proof.
    #[must_use]
    pub fn additionally_proved(&self) -> usize {
        self.certified + self.smt_backed
    }

    /// Total obligations whose "proof" rests on a trusted/assumed dependency
    /// (contract-assumed + fully-trusted).
    #[must_use]
    pub fn assumed_or_trusted(&self) -> usize {
        self.contract_assumed + self.fully_trusted
    }
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

fn is_false(value: &bool) -> bool {
    !*value
}

/// Hardened verification context attached to a proof report.
///
/// This context is intentionally separate from per-obligation proof evidence:
/// inventory and model-assumption entries describe what was observed or assumed,
/// while `ProofEvidence` and `role = "proof_evidence"` entries identify facts
/// that were actually proved.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HardenedReportContext {
    /// Hardened profile that selected the boundary inventory.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub profile: Option<HardenedProfileReport>,
    /// Assurance policy for interpreting hardened context entries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assurance: Option<HardenedAssuranceReport>,
    /// Aggregate counts for the hardened context.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<HardenedSummaryReport>,
    /// Boundary inventory, model assumptions, and links to proof evidence.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub boundary_inventory: Vec<HardenedBoundaryInventoryEntry>,
}

/// Hardened profile metadata.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HardenedProfileReport {
    /// Profile name, for example `unix_hardened` or `coreutils_hardened`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Profile version or policy revision.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    /// Boundary categories enabled by this profile.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub enabled_categories: Vec<String>,
}

/// Assurance metadata for hardened report context.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HardenedAssuranceReport {
    /// Human/machine-stable assurance label, for example `inventory_only` or `proof_backed`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub level: Option<String>,
    /// Model whose assumptions are inventoried, for example `unix_fs_process`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<String>,
    /// Policy text or identifier explaining when proof evidence is required.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_evidence_policy: Option<String>,
    /// Whether hardened boundary claims require linked proof evidence.
    #[serde(default, skip_serializing_if = "is_false")]
    pub proof_evidence_required: bool,
}

/// Aggregate counts for hardened report context.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HardenedSummaryReport {
    /// Hardened verification obligations represented in the report.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub hardened_obligations: usize,
    /// Hardened obligations discharged by proof evidence.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub proved_hardened_obligations: usize,
    /// Entries that are inventory only.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub inventory_entries: usize,
    /// Entries that are model assumptions, not proofs.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub model_assumptions: usize,
    /// Entries that link to proof evidence.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub proof_evidence_entries: usize,
}

/// Role of a hardened boundary inventory entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum HardenedBoundaryInventoryRole {
    /// Observed boundary surface; this is not a model assumption or proof.
    #[default]
    Inventory,
    /// Explicit model assumption that must not be counted as proof evidence.
    ModelAssumption,
    /// Link to proof evidence for a hardened boundary claim.
    ProofEvidence,
}

/// One hardened boundary inventory row.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct HardenedBoundaryInventoryEntry {
    /// Stable entry ID for cross-report diffing.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// Whether this row is inventory, a model assumption, or proof evidence.
    #[serde(default)]
    pub role: HardenedBoundaryInventoryRole,
    /// Hardened category, for example `byte_loss` or `raw_path_api`.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub category: String,
    /// Boundary item, such as a callee, API, trust transition, or model fact.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub boundary: String,
    /// Function where the entry was observed, if applicable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    /// Human-readable detail for the entry.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    /// Source location for the boundary entry.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Obligation this entry describes or is linked to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_id: Option<String>,
    /// Proof evidence ID when `role` is `ProofEvidence`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_evidence_id: Option<String>,
    /// Backend or inventory source that produced this entry.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

/// Trust (assumption ledger, Stage 1): a machine-readable unverified-assumption
/// entry. The report's verdict is conditional on every entry here. Never
/// counted in proved/failed; obligations remain the only verdict inputs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AssumptionEntry {
    /// `"function"` (a body the verifier could not lower) or `"crate"`
    /// (a dependency-scope assumption from the dep-TCB set).
    pub scope: String,
    /// Def-path of the assumed function, or the crate name.
    pub subject: String,
    /// Stable tag from the assumption registry: `UnsupportedReason::tag()`
    /// values (`pattern-type`, `coroutine`, `addr-of-field`,
    /// `thread-local-ref`, `escaped-binder`, ...), `unreachable-start`,
    /// `dependency-scope`, `native-lowering` (a body the native TrustIr bridge
    /// could not lower at all — the compiler backstop), or `extern-call` (a
    /// print/format/write dispatch that runs a user `Display`/`Debug` impl the
    /// bridge cannot verify panic-free; see `crate::assumption`).
    pub tag: String,
    /// Human-readable capability-gap description. Must never claim proof and
    /// must never contain full-verifier marker text.
    pub detail: String,
    /// Span of the assumed body, when function-scoped.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// The decider that recorded the assumption:
    /// `"trust-classifier"` | `"trust-policy"` | `"trust-bridge"` | `"dep-tcb"`.
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedTestExecutableReport {
    pub target: String,
    pub path: String,
    pub sha256: String,
    pub size: u64,
}

/// Schema for the nested certified-test execution record.
///
/// Keep this independent of the enclosing report schema: execution semantics
/// can evolve without silently changing what an older `trust.report.v1`
/// consumer interprets from the same field names.
pub const CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION: &str = "trust.certified-test-execution.v2";

/// Exact human-readable boundary paired with
/// [`CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1`].
pub const CERTIFIED_TEST_EXECUTION_SCOPE: &str = "authorized selected-package non-doctest test executable paths under Cargo; monitors installed in authenticated artifacts; authenticated launch permits ordinary child spawning and is host-specific: Linux uses a sealed anonymous executable image, so current_exe/self-reexecution and pathname/inode/xattr/mode identity are not preserved; macOS uses a private signed pathname snapshot whose bytes and suspended live-process code identity are reauthenticated before release, so snapshot-path current_exe/self-reexecution is preserved during that process lifetime but original-artifact pathname/inode/xattr/mode identity is not; completion attests only the top-level Cargo child exit, not libtest-case completion, monitor coverage, exec replacement, descendant processes, or runtime-loaded code";

/// Machine-readable meaning of a phase-B completion state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CertifiedTestExecutionCompletionScope {
    /// Only the top-level Cargo child reaching an exit status is attested.
    /// This is not libtest-case completion, monitor coverage, process-tree,
    /// `exec`, runtime dynamic-load, or host launch/original-artifact identity
    /// attestation.
    TopLevelCargoChildExitOnlyV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CertifiedTestExecutionPhaseState {
    NotRequested,
    Blocked,
    Started,
    /// The top-level phase-B Cargo child was reaped with `phase_b_exit`.
    /// A zero exit is not evidence that every libtest case or monitor ran.
    CargoInvocationExited,
}

/// Authenticated two-phase state for `targo trust test`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedTestExecutionReport {
    /// Required schema for this nested execution record.
    pub schema: String,
    /// Required machine-readable boundary on completion claims.
    pub completion_scope: CertifiedTestExecutionCompletionScope,
    pub requested: bool,
    pub scope: String,
    pub compile_only: bool,
    pub phase_a_status: i32,
    pub phase_a_success: bool,
    pub phase_b_state: CertifiedTestExecutionPhaseState,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub blocker: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub phase_b_exit: Option<i32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub authorized_executables: Vec<CertifiedTestExecutableReport>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub authorized_inventory_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target_directory: Option<String>,
}

/// Trust (green front door, Stage 2): the tiered exit-code gate decision for a
/// `targo trust check` run. This is DELIBERATELY separate from the verdict
/// lattice (`CrateSummary::verdict`): the verdict stays fail-closed and never
/// rises above `Inconclusive` on a conditional pass, while this object records
/// *why the shell exited 0* (or did not). Additive; absent in pre-gate reports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationGateReport {
    /// Which gate lane produced this decision: `"advisory"`, `"memory-safe"`,
    /// or `"strict"`. Only advisory may admit contract-panic conditional
    /// evidence; strict and memory-safe never do.
    pub lane: String,
    /// Canonical configured verification level (`"L0"`, `"L1"`, or `"L2"`).
    ///
    /// This is policy metadata rather than a result-derived maximum: two runs
    /// that happened to emit the same obligation kinds are not comparable when
    /// they were configured to search different proof levels. Absent in older
    /// and non-Targo reports, which diff consumers must treat as unscoped.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verification_level: Option<String>,
    /// `"pass"` | `"conditional-pass"` | `"inconclusive"` | `"fail"`.
    pub decision: String,
    /// The final process exit code persisted by the frontend after every
    /// verification, evidence, and setup gate has been applied.
    pub exit_code: u8,
    /// The outcome partition the decision was computed from.
    pub counts: VerificationGateCounts,
    /// The pass is conditional on ≥1 `assumption:*` ledger row.
    #[serde(default)]
    pub conditional_on_assumption_rows: bool,
    /// The pass is conditional on ≥1 dependency-scope (dep-TCB) ledger entry.
    /// Exact active Cargo units that remain outside the authenticated proof
    /// subject (including policy, control, documentation, and filtered-unit
    /// exclusions) make the result conditional.  The canonical inventory and
    /// gate decide whether such a result is publishable; this flag is only the
    /// saved-report summary of that dependency/exclusion condition.
    #[serde(default)]
    pub conditional_on_dependency_entries: bool,
    /// The pass is conditional on ≥1 runtime-checked obligation.
    #[serde(default)]
    pub conditional_on_runtime_checks: bool,
    /// The pass is conditional on ≥1 crate-scope visitation-rowless entry.
    #[serde(default)]
    pub conditional_on_visitation_entries: bool,
    /// Trust (assertion-grade coverage, roadmap §4.1): the run's verification-
    /// coverage accounting, from the compiler's `coverage_summary` transport
    /// row. `None` means the compiler emitted no coverage row (an older
    /// toolchain) — coverage UNKNOWN: reported as such, but absence alone never
    /// fails the gate. When present with `coverage_complete == false`, the gate
    /// decision was capped at inconclusive (a run with unverified eligible
    /// functions must never read as a pass). `#[serde(default)]` keeps
    /// pre-coverage JSON deserializable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage: Option<VerificationCoverage>,
    /// Authenticated compile/execute state for `targo trust test`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub test_execution: Option<CertifiedTestExecutionReport>,
}

/// Trust (assertion-grade coverage, roadmap §4.1): verification-coverage counts
/// recorded into `report.json` (under `verification_gate.coverage`). `eligible`
/// is the number of local `mir_keys` function bodies the compiler's eager
/// whole-crate walk demanded verification for; `processed` is how many of those
/// reached an attributable per-body outcome. `coverage_complete == false` is a
/// FAIL-CLOSED condition: some functions were never verified, so the run is
/// inconclusive at best regardless of how green the verified subset looks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationCoverage {
    /// Eligible local function bodies (the eager whole-crate walk's selection).
    pub eligible: usize,
    /// Bodies that reached an attributable verification-pass outcome.
    pub processed: usize,
    /// `processed == eligible`. Any mismatch, including an over-count, is
    /// malformed/incomplete coverage and therefore never a pass.
    pub coverage_complete: bool,
}

impl VerificationCoverage {
    /// Build from raw counts; `coverage_complete` is derived, never asserted.
    #[must_use]
    pub fn from_counts(eligible: usize, processed: usize) -> Self {
        Self { eligible, processed, coverage_complete: processed == eligible }
    }
}

/// Trust (green front door, Stage 2): the disjoint outcome partition backing a
/// `VerificationGateReport`. `total == proved + failed + unknown +
/// runtime_checked + assumed + mandated + contract_panics`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct VerificationGateCounts {
    /// All transport rows.
    pub total: usize,
    /// Rows genuinely proved.
    pub proved: usize,
    /// Rows refuted (a counterexample).
    pub failed: usize,
    /// Genuine unknowns: every inconclusive row that is neither an explicit
    /// `assumption:*` ledger row nor a compiler design mandate (includes
    /// timeouts and defective assumption rows counted fail-closed).
    pub unknown: usize,
    /// Rows discharged by an enforced runtime check.
    pub runtime_checked: usize,
    /// Explicit `assumption:*` ledger rows (inconclusive on the wire).
    pub assumed: usize,
    /// Compiler design-mandate rows (inconclusive + the `design_mandate` bit).
    pub mandated: usize,
    /// Trust (T9 contract-panic): rows whose kind starts with `contract-panic:`
    /// — an annotated, message-matched INTENTIONAL fail-closed panic (see
    /// `assumption::CONTRACT_PANIC_ROW_KIND_PREFIX`). Conditional-pass-eligible
    /// only in advisory survey mode, rejected by strict and memory-safe,
    /// and never proof credit. `#[serde(default)]` keeps pre-T9 JSON deserializable.
    #[serde(default)]
    pub contract_panics: usize,
}

/// Authority label attached to every serialized [`JsonProofReport`].
///
/// A report-shaped byte string is an observational record. It cannot recreate
/// the private live verifier capability that authorized an in-process result,
/// even when every embedded digest is structurally valid.
pub const SERIALIZED_REPORT_AUTHORITY: &str = "untrusted_observational_only_no_proof_credit";

/// Schema emitted for the observational Cargo proof-inventory projection in a
/// canonical report.
pub const CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1: &str = "trust.cargo-proof-inventory-report.v1";
pub const CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2: &str = "trust.cargo-proof-inventory-report.v2";

/// Closed Cargo-resolved profile configuration bound into one proof Unit's
/// identity.
///
/// This mirrors the authoritative Cargo producer's versioned projection. The
/// report remains observational, but preserving the closed fields makes
/// cross-run feature/profile/backend drift visible and comparable.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CargoUnitProfileSemanticsReport {
    pub opt_level: String,
    pub requested_lto: String,
    pub effective_lto: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub codegen_backend: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub codegen_units: Option<u32>,
    pub debuginfo: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub split_debuginfo: Option<String>,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub rpath: bool,
    pub incremental: bool,
    pub panic: String,
    pub strip: String,
    pub rustflags: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trim_paths: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint_mostly_unused: Option<bool>,
}

/// Closed compiler frontend/backend identity for one Cargo proof Unit.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CargoUnitCompilerSemanticsReport {
    pub frontend: String,
    pub codegen_backend: String,
    pub rustc_release: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_commit_hash: Option<String>,
    pub rustc_host: String,
    pub rustc_verbose_version_sha256: String,
}

/// Canonical, closed Cargo-resolved Unit configuration descriptor hashed by
/// Cargo and repeated in every compiler/artifact envelope for this Unit.
///
/// It does not bind source bytes, dependency adjacency or extern artifact
/// identities, late build-script output, or proc-macro behavior; those remain
/// separate proof and exclusion frontiers.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CargoUnitSemanticsReport {
    pub schema: String,
    pub features: Vec<String>,
    pub target_cfg: Vec<String>,
    pub cfg_test: bool,
    pub target_edition: String,
    pub target_crate_types: Vec<String>,
    pub target_harness: bool,
    pub target_proc_macro: bool,
    pub profile: CargoUnitProfileSemanticsReport,
    pub compiler: CargoUnitCompilerSemanticsReport,
    pub unit_rustflags: Vec<String>,
    pub manifest_lint_rustflags: Vec<String>,
    pub extra_compiler_args: Vec<String>,
}

/// Exact identity of one Cargo compiler unit recorded in a proof report.
///
/// This is deliberately an observational DTO. In particular, the unit index,
/// role, and target-spec digest cannot recreate Targo's private live transport
/// authority when this value is deserialized from JSON.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CargoProofUnitReport {
    /// Cargo's full package identity, including source and version.
    pub package_id: String,
    /// Manifest package name (not globally unique).
    pub package_name: String,
    /// Cargo target name.
    pub target_name: String,
    /// Exact Cargo target-kind vector.
    pub target_kinds: Vec<String>,
    /// Exact rustc compile target selected for this unit.
    pub compile_target: String,
    /// SHA-256 of a custom target specification, or `None` for a built-in
    /// target whose semantics come from the pinned compiler.
    #[serde(default)]
    pub compile_target_spec_sha256: Option<String>,
    /// Cargo-owned invocation-local Unit index.
    pub proof_unit_index: u64,
    /// Exact Cargo compile mode for this Unit.
    pub proof_unit_mode: String,
    /// Targo proof role (`primary`, `test-execution`, `dependency`, or
    /// `excluded` in the excluded-active partition).
    pub proof_unit_role: String,
    /// Unit's role in Cargo's resolved graph. For proof-frontier Units this is
    /// equal to `proof_unit_role`; excluded Units retain their pre-exclusion
    /// role (`primary`, `test-execution`, `dependency`, or `control`).
    pub graph_role: String,
    /// Closed-set reason for a Unit in the excluded-active partition. Proof
    /// frontier Units omit this field; every excluded Unit emitted by current
    /// Targo carries one so a report never conflates policy exclusions with
    /// Cargo control/execution jobs that cannot produce compiler evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exclusion_reason: Option<String>,
    /// Canonical SHA-256 of `semantics`. Optional only so legacy v1 saved
    /// reports remain readable as non-authoritative observations; v2 live
    /// reports require both fields for every declared and excluded Unit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub semantics_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub semantics: Option<CargoUnitSemanticsReport>,
}

/// Explicit role partition for one phase of Cargo's proof frontier.
///
/// Empty roles remain serialized as empty arrays so a report never leaves the
/// reader to infer whether a role was omitted or contained no units. Producers
/// emit every vector in ascending `proof_unit_index` order, with the complete
/// unit identity as a deterministic tie-breaker.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CargoProofUnitPartitions {
    /// Selected root Units.
    pub primary_roots: Vec<CargoProofUnitReport>,
    /// Build-mode Units directly executed by test, doctest, or bench roots.
    pub test_execution_units: Vec<CargoProofUnitReport>,
    /// Dependency Units admitted by the include-dependencies policy.
    pub dependency_units: Vec<CargoProofUnitReport>,
}

/// Observational projection of Targo's exact, Cargo-authenticated proof-unit
/// inventory and the units that subsequently completed and emitted coverage.
///
/// `declared`, `completed`, and `covered` are partitioned by proof role instead
/// of being combined into a name-based aggregate. `excluded_active_units`
/// records resolved graph units that were deliberately outside the proof
/// frontier. This object is serialized evidence for audit and comparison only;
/// it is never proof authority after a report crosses a serialization boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CargoProofInventoryReport {
    /// Schema governing this report projection.
    pub schema: String,
    /// Whether the resolved graph's dependency Units were proof subjects.
    pub include_dependencies: bool,
    /// Exact proof frontier declared by Cargo before compilation.
    pub declared: CargoProofUnitPartitions,
    /// Declared proof Units that emitted authenticated terminal completion.
    pub completed: CargoProofUnitPartitions,
    /// Declared proof Units that emitted authenticated coverage inventory.
    pub covered: CargoProofUnitPartitions,
    /// Resolved active Units deliberately outside the proof frontier.
    pub excluded_active_units: Vec<CargoProofUnitReport>,
}

/// The complete in-memory JSON proof report projection. All other formats
/// (text, HTML, terminal) are derived from this projection.
///
/// Serialization always adds [`SERIALIZED_REPORT_AUTHORITY`]. The in-memory
/// value can participate in proof-consuming logic only while an owning verifier
/// separately retains and revalidates its opaque live capability.
#[derive(Debug, Clone)]
pub struct JsonProofReport {
    /// Report metadata (version, timestamp, timing).
    pub metadata: ReportMetadata,
    /// Crate being verified.
    pub crate_name: String,
    /// Crate-level summary.
    pub summary: CrateSummary,
    /// Per-function results with full obligation details.
    pub functions: Vec<FunctionProofReport>,
    /// Optional hardened boundary context.
    pub hardened: Option<HardenedReportContext>,
    /// Trust (assumption ledger): everything this report's verdict is
    /// conditional on. Additive; absent in pre-ledger reports.
    pub assumptions: Vec<AssumptionEntry>,
    /// Trust (green front door, Stage 2): the tiered exit-code gate decision for
    /// this run. Separate from `summary.verdict`; records why the shell exited
    /// as it did. Additive; absent in pre-gate reports (old JSON deserializes).
    pub verification_gate: Option<VerificationGateReport>,
    /// Exact Cargo proof frontier, role partition, and completion/coverage
    /// observations for Targo crate-mode reports. Direct single-file reports
    /// omit this field. Serialized contents are observational only.
    pub cargo_proof_inventory: Option<CargoProofInventoryReport>,
}

#[derive(Serialize)]
struct JsonProofReportSerialization<'a> {
    authority: &'static str,
    metadata: &'a ReportMetadata,
    crate_name: &'a str,
    summary: &'a CrateSummary,
    functions: &'a [FunctionProofReport],
    #[serde(skip_serializing_if = "Option::is_none")]
    hardened: &'a Option<HardenedReportContext>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    assumptions: &'a Vec<AssumptionEntry>,
    #[serde(skip_serializing_if = "Option::is_none")]
    verification_gate: &'a Option<VerificationGateReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    cargo_proof_inventory: &'a Option<CargoProofInventoryReport>,
}

impl Serialize for JsonProofReport {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        JsonProofReportSerialization {
            authority: SERIALIZED_REPORT_AUTHORITY,
            metadata: &self.metadata,
            crate_name: &self.crate_name,
            summary: &self.summary,
            functions: &self.functions,
            hardened: &self.hardened,
            assumptions: &self.assumptions,
            verification_gate: &self.verification_gate,
            cargo_proof_inventory: &self.cargo_proof_inventory,
        }
        .serialize(serializer)
    }
}

/// Serde wire mirror for [`JsonProofReport`]. Keeping deserialization on this
/// private type prevents any public serde entry point from returning an
/// unsanitized saved report.
#[derive(Deserialize)]
struct JsonProofReportWire {
    /// Additive declaration emitted by current writers. It is deliberately
    /// ignored on input: an attacker may omit or forge a label, and all saved
    /// reports are fail-closed regardless.
    #[serde(default, rename = "authority")]
    _authority: Option<String>,
    metadata: ReportMetadata,
    crate_name: String,
    summary: CrateSummary,
    functions: Vec<FunctionProofReportWire>,
    #[serde(default)]
    hardened: Option<HardenedReportContext>,
    #[serde(default)]
    assumptions: Vec<AssumptionEntry>,
    #[serde(default)]
    verification_gate: Option<VerificationGateReport>,
    #[serde(default)]
    cargo_proof_inventory: Option<CargoProofInventoryReport>,
}

impl<'de> Deserialize<'de> for JsonProofReport {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = JsonProofReportWire::deserialize(deserializer)?;
        let (report, _, _) = Self::from_saved_wire(wire, None);
        Ok(report)
    }
}

impl JsonProofReport {
    fn from_saved_wire(
        wire: JsonProofReportWire,
        trusted_root: Option<&Path>,
    ) -> (Self, SavedReportSanitization, UntrustedSavedReportClaims) {
        let functions = wire
            .functions
            .into_iter()
            .map(FunctionProofReportWire::into_public_untrusted)
            .collect::<Vec<_>>();
        let untrusted_claims = UntrustedSavedReportClaims::from_functions(&functions);
        let mut report = Self {
            metadata: wire.metadata,
            crate_name: wire.crate_name,
            summary: wire.summary,
            functions,
            hardened: wire.hardened,
            assumptions: wire.assumptions,
            verification_gate: wire.verification_gate,
            cargo_proof_inventory: wire.cargo_proof_inventory,
        };
        let sanitization = report.sanitize_deserialized_with_root(trusted_root);
        (report, sanitization, untrusted_claims)
    }
}

/// What `JsonProofReport::sanitize_deserialized` changed while re-gating a
/// report loaded from disk or transport.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SavedReportSanitization {
    /// Number of deserialized `proved` obligations downgraded to `unknown`.
    pub downgraded_proved: usize,
    /// Number of deserialized `runtime_checked` obligations downgraded to
    /// `unknown`.
    pub downgraded_runtime_checked: usize,
    /// Number of downgraded `proved` rows that lacked live proof authority.
    ///
    /// Serialized evidence can be structurally well formed, but it cannot carry
    /// the process-local verifier capability that authorized the original
    /// `proved` outcome. Consequently every deserialized `proved` row is an
    /// evidence defect until a verifier replays it. Runtime-check downgrades are
    /// counted separately because they concern compiler/monitor authority, not
    /// proof evidence.
    pub evidence_defects: usize,
    /// Number of deserialized `proved` rows whose serialized evidence is also
    /// structurally malformed or below the publication-grade reporting floor.
    ///
    /// This is a subset of [`Self::evidence_defects`]. A structurally valid
    /// serialized proof still has no live replay authority and is therefore an
    /// `evidence_defect`, but consumers can use this separate count to reject
    /// corrupted or presence-only proof shapes without conflating them with the
    /// unavoidable authority downgrade at a saved-report boundary.
    pub structural_evidence_defects: usize,
}

impl SavedReportSanitization {
    #[must_use]
    pub fn has_evidence_defects(self) -> bool {
        self.evidence_defects > 0
    }

    /// Whether any serialized proved row also failed structural evidence
    /// validation, independently of the mandatory live-authority downgrade.
    #[must_use]
    pub fn has_structural_evidence_defects(self) -> bool {
        self.structural_evidence_defects > 0
    }

    /// Whether any favorable serialized outcome lost its non-serializable live
    /// authority at the saved-report boundary.
    #[must_use]
    pub fn has_authority_downgrades(self) -> bool {
        self.downgraded_proved > 0 || self.downgraded_runtime_checked > 0
    }
}

/// Minimal snapshot of serialized outcome claims captured before a saved report
/// is sanitized.
///
/// This is explicitly untrusted, observational metadata. It can explain that a
/// prior file claimed an obligation was proved, but it can never grant proof
/// credit or recreate the live verifier capability that made the original
/// decision. The snapshot intentionally excludes proof evidence and summaries.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UntrustedSavedReportClaims {
    obligations: Vec<UntrustedSavedObligationClaim>,
}

impl UntrustedSavedReportClaims {
    fn from_functions(functions: &[FunctionProofReport]) -> Self {
        let mut obligations = Vec::new();
        for (function_index, function) in functions.iter().enumerate() {
            for (obligation_index, obligation) in function.obligations.iter().enumerate() {
                obligations.push(UntrustedSavedObligationClaim {
                    function: function.function.clone(),
                    function_index,
                    obligation_id: obligation.obligation_id.clone(),
                    obligation_index,
                    claim_fingerprint: untrusted_saved_claim_fingerprint(obligation),
                    outcome: UntrustedSavedOutcomeClaim::from_outcome(&obligation.outcome),
                });
            }
        }
        Self { obligations }
    }

    /// Capture claims from an in-memory representation of untrusted saved
    /// input, before calling a saved-report sanitizer.
    #[must_use]
    pub fn from_untrusted_report(report: &JsonProofReport) -> Self {
        Self::from_functions(&report.functions)
    }

    /// Serialized outcome claims, retained for observational comparison only.
    #[must_use]
    pub fn obligations(&self) -> &[UntrustedSavedObligationClaim] {
        &self.obligations
    }
}

/// Identity and outcome of one serialized obligation claim in an
/// [`UntrustedSavedReportClaims`] snapshot.
///
/// Stable obligation IDs are preferred by consumers. The function and row
/// ordinals are retained as a conservative fallback for legacy reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UntrustedSavedObligationClaim {
    function: String,
    function_index: usize,
    obligation_id: Option<String>,
    obligation_index: usize,
    claim_fingerprint: String,
    outcome: UntrustedSavedOutcomeClaim,
}

impl UntrustedSavedObligationClaim {
    /// Fully qualified function name copied from the serialized report.
    #[must_use]
    pub fn function(&self) -> &str {
        &self.function
    }

    /// Zero-based function row used only when no stable obligation ID exists.
    #[must_use]
    pub fn function_index(&self) -> usize {
        self.function_index
    }

    /// Stable serialized obligation ID, when the producer supplied one.
    #[must_use]
    pub fn obligation_id(&self) -> Option<&str> {
        self.obligation_id.as_deref()
    }

    /// Zero-based obligation row used only when no stable obligation ID exists.
    #[must_use]
    pub fn obligation_index(&self) -> usize {
        self.obligation_index
    }

    /// Observational identity for the semantic claim asserted by the row.
    ///
    /// A canonical compiler claim digest is preferred. Older rows fall back to
    /// a domain-separated digest of kind, exact typed VC identity, description,
    /// proof level, and source location. This remains untrusted metadata, but
    /// prevents a saved diff from treating an obligation-ID reuse for a changed
    /// claim as unchanged.
    #[must_use]
    pub fn claim_fingerprint(&self) -> &str {
        &self.claim_fingerprint
    }

    /// Outcome asserted by the serialized row. This is not verifier authority.
    #[must_use]
    pub fn outcome(&self) -> UntrustedSavedOutcomeClaim {
        self.outcome
    }
}

fn untrusted_saved_claim_fingerprint(obligation: &ObligationReport) -> String {
    if let Some(digest) = obligation
        .transport_evidence
        .as_ref()
        .and_then(|evidence| evidence.claim_digest_sha256.as_deref())
        .filter(|digest| canonical_sha256_value(digest))
    {
        return format!("trustc-exact-vc-sha256:{digest}");
    }

    let typed_kind =
        obligation.transport_evidence.as_ref().and_then(|evidence| evidence.typed_kind.as_deref());
    let encoded = serde_json::to_vec(&(
        &obligation.kind,
        typed_kind,
        &obligation.description,
        obligation.proof_level,
        &obligation.location,
    ))
    .expect("serializing report claim identity cannot fail");
    let mut digest = Sha256::new();
    digest.update(b"trust.saved-observational-claim-fallback.v2");
    digest.update((encoded.len() as u64).to_be_bytes());
    digest.update(encoded);
    format!("fallback-sha256:{}", lowercase_transport_hex(&digest.finalize()))
}

/// Outcome asserted by an untrusted serialized obligation row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UntrustedSavedOutcomeClaim {
    /// Serialized row asserted `proved`.
    Proved,
    /// Serialized row asserted `failed`.
    Failed,
    /// Serialized row asserted `unknown`.
    Unknown,
    /// Serialized row asserted `runtime_checked`.
    RuntimeChecked,
    /// Serialized row asserted `timeout`.
    Timeout,
    /// Serialized row asserted a design requirement.
    DesignRequirement,
}

impl UntrustedSavedOutcomeClaim {
    fn from_outcome(outcome: &ObligationOutcome) -> Self {
        match outcome {
            ObligationOutcome::Proved { .. } => Self::Proved,
            ObligationOutcome::Failed { .. } => Self::Failed,
            ObligationOutcome::Unknown { .. } => Self::Unknown,
            ObligationOutcome::RuntimeChecked { .. } => Self::RuntimeChecked,
            ObligationOutcome::Timeout { .. } => Self::Timeout,
            ObligationOutcome::DesignRequirement { .. } => Self::DesignRequirement,
        }
    }
}

impl JsonProofReport {
    /// Decode an untrusted canonical saved JSON report and return the exact
    /// sanitization performed at that first deserialization boundary, plus a
    /// minimal pre-sanitization claim snapshot for observational comparison.
    ///
    /// Consumers that must reject authority-bearing saved input, rather than
    /// merely observe its fail-closed `Unknown` form, must use this method and
    /// inspect the returned [`SavedReportSanitization`]. Calling
    /// [`Self::sanitize_deserialized`] again would lose that provenance because
    /// sanitization is intentionally idempotent.
    ///
    /// `trusted_root` permits bounded diagnostic inspection of path-backed
    /// artifact materializations. It never restores serialized proof or
    /// runtime-check authority. Callers remain responsible for bounding `json`
    /// before invoking this decoder.
    pub fn decode_saved_json(
        json: &[u8],
        trusted_root: Option<&Path>,
    ) -> serde_json::Result<(Self, SavedReportSanitization, UntrustedSavedReportClaims)> {
        let wire = serde_json::from_slice::<JsonProofReportWire>(json)?;
        Ok(Self::from_saved_wire(wire, trusted_root))
    }

    /// Re-establish the cardinal soundness invariant on a
    /// report that was DESERIALIZED from disk/transport, where the summary
    /// counts, per-function verdicts, and per-obligation outcomes are UNTRUSTED
    /// input — a stale or hand-edited `report.json` can claim `proved: 1000` with
    /// zero proved obligations, or `outcome: proved` with `assurance: unchecked`.
    ///
    /// (1) Downgrades EVERY deserialized `ObligationOutcome::Proved` and
    /// `ObligationOutcome::RuntimeChecked` to `Unknown`, then (2) RECOMPUTES
    /// each `FunctionSummary`, the `CrateSummary`, and every verdict from the
    /// gated obligations. Serialized
    /// proof/transport evidence is self-authenticating data: hashes and schema
    /// shape can detect accidental corruption, but cannot recreate the private
    /// verifier/compiler capability or prove that a verifier accepted these
    /// exact bytes or installed the exact certified monitor. Only an actual
    /// verifier/compiler replay may restore proof or runtime-check credit.
    ///
    /// [`Deserialize`] invokes this automatically before returning a
    /// `JsonProofReport`. The explicit method remains available for defensive
    /// callers and alternate decoders, and is idempotent. Fail-closed: never a
    /// false-PROVE.
    pub fn sanitize_deserialized(&mut self) -> SavedReportSanitization {
        self.sanitize_deserialized_with_root(None)
    }

    /// Re-gate a saved report while permitting diagnostic inspection of
    /// canonical path-backed proof materializations beneath `trusted_root`.
    ///
    /// The root grants filesystem containment only. It does NOT grant proof
    /// authority and cannot preserve a deserialized `Proved` outcome. Every
    /// such row is still downgraded until a verifier actually replays it.
    pub fn sanitize_deserialized_at_root(
        &mut self,
        trusted_root: &Path,
    ) -> SavedReportSanitization {
        self.sanitize_deserialized_with_root(Some(trusted_root))
    }

    fn sanitize_deserialized_with_root(
        &mut self,
        trusted_root: Option<&Path>,
    ) -> SavedReportSanitization {
        let mut sanitization = SavedReportSanitization::default();
        // Preserve fail-closed summary-only residuals from legacy or partial
        // reports. They have no concrete obligation rows to recount, so
        // dropping them would turn missing data into good news.
        let reported_residuals = self
            .functions
            .iter()
            .map(|function| DeserializedFunctionResiduals::from(&function.summary))
            .collect::<Vec<_>>();
        let crate_residuals =
            DeserializedCrateResiduals::from_report(&self.summary, &reported_residuals);

        for func in &mut self.functions {
            for obl in &mut func.obligations {
                match &obl.outcome {
                    ObligationOutcome::Proved { strength } => {
                        let diagnostic_defect = deserialized_proved_obligation_structural_defect(
                            obl,
                            strength,
                            trusted_root,
                        );
                        sanitization.downgraded_proved += 1;
                        sanitization.evidence_defects += 1;
                        sanitization.structural_evidence_defects +=
                            usize::from(diagnostic_defect.is_some());
                        obl.outcome = ObligationOutcome::Unknown {
                            reason: deserialized_proved_obligation_downgrade_reason(
                                diagnostic_defect,
                            ),
                        };
                    }
                    ObligationOutcome::RuntimeChecked { .. } => {
                        sanitization.downgraded_runtime_checked += 1;
                        obl.outcome = ObligationOutcome::Unknown {
                            reason: DIRECT_DESERIALIZED_RUNTIME_CHECKED_DOWNGRADE_REASON
                                .to_string(),
                        };
                    }
                    _ => {}
                }
                // A serialized monitor row has no live compiler capability.
                // Scrub even Unknown/Failed/Timeout rows: report formatters
                // render the monitor field independently of the outcome, so an
                // attacker must not be able to assert a favorable §7 grade on
                // any deserialized row.
                scrub_deserialized_monitor_claim(obl);
            }
        }

        // Saved side channels must not retain a second, contradictory PASS or
        // proof-backed claim after the per-obligation rows are downgraded.
        // These fields are reporting caches/metadata, not replay authority.
        self.sanitize_deserialized_authority_side_channels();

        self.recompute_summaries_from_obligation_outcomes_impl(
            Some(&reported_residuals),
            Some(crate_residuals),
        );
        sanitization
    }

    fn sanitize_deserialized_authority_side_channels(&mut self) {
        if let Some(gate) = &mut self.verification_gate {
            gate.counts.unknown = gate
                .counts
                .unknown
                .saturating_add(gate.counts.proved)
                .saturating_add(gate.counts.runtime_checked);
            gate.counts.proved = 0;
            gate.counts.runtime_checked = 0;
            gate.conditional_on_runtime_checks = false;
            gate.decision = if gate.counts.failed > 0 {
                "fail".to_string()
            } else {
                "inconclusive".to_string()
            };
            if gate.exit_code == 0 {
                gate.exit_code = 1;
            }
        }

        if let Some(hardened) = &mut self.hardened {
            hardened
                .boundary_inventory
                .retain(|entry| entry.role != HardenedBoundaryInventoryRole::ProofEvidence);
            for entry in &mut hardened.boundary_inventory {
                entry.proof_evidence_id = None;
            }
            let inventory_entries = hardened
                .boundary_inventory
                .iter()
                .filter(|entry| entry.role == HardenedBoundaryInventoryRole::Inventory)
                .count();
            let model_assumptions = hardened
                .boundary_inventory
                .iter()
                .filter(|entry| entry.role == HardenedBoundaryInventoryRole::ModelAssumption)
                .count();
            if let Some(summary) = &mut hardened.summary {
                summary.proved_hardened_obligations = 0;
                summary.proof_evidence_entries = 0;
                summary.inventory_entries = inventory_entries;
                summary.model_assumptions = model_assumptions;
            }
            if let Some(assurance) = &mut hardened.assurance {
                assurance.level = Some("inventory_only".to_string());
            }
        }
    }

    /// Recompute all function/crate counts and verdicts from the current
    /// obligation outcomes.
    ///
    /// This is aggregation ONLY. It deliberately performs no proof validation,
    /// replay, evidence authentication, or deserialization hardening; in
    /// particular, an existing `Proved` row remains `Proved`. Calling this
    /// method therefore grants no proof authority. It is intended for a trusted
    /// same-process report builder that already validated each outcome using a
    /// private verifier capability. A report loaded from disk or transport MUST
    /// use [`Self::sanitize_deserialized`] instead.
    pub fn recompute_summaries_from_obligation_outcomes(&mut self) {
        self.recompute_summaries_from_obligation_outcomes_impl(None, None);
    }

    fn recompute_summaries_from_obligation_outcomes_impl(
        &mut self,
        reported_residuals: Option<&[DeserializedFunctionResiduals]>,
        crate_residuals: Option<DeserializedCrateResiduals>,
    ) {
        let (
            mut c_proved,
            mut c_runtime,
            mut c_failed,
            mut c_unknown,
            mut c_timed_out,
            mut c_design,
            mut c_total,
        ) = (0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
        let (mut f_verified, mut f_runtime, mut f_violations, mut f_inconclusive) =
            (0usize, 0usize, 0usize, 0usize);

        let (mut c_unattributed_failed, mut c_unattributed_unknown, mut c_unattributed_proved) =
            (0usize, 0usize, 0usize);

        for (function_index, func) in self.functions.iter_mut().enumerate() {
            recompute_function_summary(
                func,
                reported_residuals.and_then(|residuals| residuals.get(function_index).copied()),
            );
            match func.summary.verdict {
                FunctionVerdict::Verified => f_verified += 1,
                FunctionVerdict::RuntimeChecked => f_runtime += 1,
                FunctionVerdict::HasViolations => f_violations += 1,
                FunctionVerdict::Inconclusive => f_inconclusive += 1,
                _ => {}
            }
            c_total = c_total.saturating_add(func.summary.total_obligations);
            c_proved = c_proved.saturating_add(func.summary.proved);
            c_runtime = c_runtime.saturating_add(func.summary.runtime_checked);
            c_failed = c_failed.saturating_add(func.summary.failed);
            c_unknown = c_unknown.saturating_add(func.summary.unknown);
            c_timed_out = c_timed_out.saturating_add(func.summary.timed_out);
            c_design = c_design.saturating_add(func.summary.design_requirements);
            c_unattributed_failed =
                c_unattributed_failed.saturating_add(func.summary.unattributed_failed);
            c_unattributed_unknown =
                c_unattributed_unknown.saturating_add(func.summary.unattributed_unknown);
            c_unattributed_proved =
                c_unattributed_proved.saturating_add(func.summary.unattributed_proved);
        }
        if let Some(residuals) = crate_residuals {
            c_unattributed_failed = c_unattributed_failed.saturating_add(residuals.failed);
            c_unattributed_unknown = c_unattributed_unknown
                .saturating_add(residuals.unknown)
                .saturating_add(residuals.proved);
            c_unattributed_proved = 0;
        }
        // (3) Recompute the crate summary from the gated functions.
        self.summary.functions_analyzed = self.functions.len();
        self.summary.functions_verified = f_verified;
        self.summary.functions_runtime_checked = f_runtime;
        self.summary.functions_with_violations = f_violations;
        self.summary.functions_inconclusive = f_inconclusive;
        self.summary.total_obligations = c_total;
        self.summary.total_proved = c_proved;
        self.summary.total_runtime_checked = c_runtime;
        self.summary.total_failed = c_failed;
        self.summary.total_unknown = c_unknown;
        self.summary.total_timed_out = c_timed_out;
        self.summary.total_design_requirements = c_design;
        self.summary.total_unattributed_failed = c_unattributed_failed;
        self.summary.total_unattributed_unknown = c_unattributed_unknown;
        self.summary.total_unattributed_proved = c_unattributed_proved;
        self.summary.proof_grade_engine_statuses =
            summarize_proof_grade_engine_statuses(&self.functions);
        self.summary.verdict = ScopeVerdict::from_counts(ScopeVerdictCounts {
            total: c_total,
            proved: c_proved,
            runtime_checked: c_runtime,
            failed: c_failed,
            unknown: c_unknown,
            unattributed_failed: c_unattributed_failed,
            unattributed_unknown: c_unattributed_unknown,
            unattributed_proved: c_unattributed_proved,
        });
    }
}

fn deserialized_proved_obligation_structural_defect(
    obligation: &ObligationReport,
    outcome_strength: &ProofStrength,
    trusted_root: Option<&Path>,
) -> Option<String> {
    if !outcome_strength.assurance.meets_reporting_floor() {
        Some("proof assurance is below the reported-proof floor".to_string())
    } else if !proof_strength_is_publication_grade(outcome_strength) {
        Some("proved outcome strength is not publication-grade".to_string())
    } else if obligation
        .proof_evidence
        .as_ref()
        .is_some_and(|proof| &proof.strength != outcome_strength)
    {
        Some("proved outcome strength does not match proof_evidence.strength".to_string())
    } else {
        saved_report_publishable_proof_defect(obligation, trusted_root)
    }
}

fn deserialized_proved_obligation_downgrade_reason(diagnostic_defect: Option<String>) -> String {
    const NO_REPLAY_AUTHORITY: &str = "deserialized proved obligation has no live verifier replay capability; serialized proof/transport evidence is diagnostic-only and cannot carry proof authority";

    // Retain structural diagnostics because they are useful when investigating
    // corrupt reports, but never mistake the absence of a structural defect for
    // proof authority. A producer can synthesize both payload and matching hash.
    diagnostic_defect.map_or_else(
        || NO_REPLAY_AUTHORITY.to_string(),
        |defect| format!("{NO_REPLAY_AUTHORITY}; diagnostic evidence defect: {defect}"),
    )
}

fn saved_report_publishable_proof_defect(
    obligation: &ObligationReport,
    trusted_root: Option<&Path>,
) -> Option<String> {
    let Some(proof) = obligation.proof_evidence.as_ref() else {
        return Some("proof_evidence is missing".to_string());
    };
    if obligation.evidence.as_ref() != Some(&proof.evidence) {
        return Some("obligation evidence does not match proof_evidence.evidence".to_string());
    }
    let defect = publishable_obligation_proof_defect(
        proof,
        obligation.obligation_id.as_deref(),
        trusted_root,
    )
    .or_else(|| matching_transport_evidence_defect(obligation, proof));
    defect
}

/// Return a diagnostic defect when a saved obligation's serialized proof
/// evidence is not publication-grade in structure.
///
/// This validates exact typed identities, matching transport evidence,
/// canonical native TrustIr materializations, and the bound artifact DAG. An
/// absent defect does **not** restore proof authority: serialized hashes and
/// evidence remain self-authored data until a live verifier replays them. This
/// API exists so saved-report consumers can reject malformed proof claims
/// without duplicating the structural validator.
#[must_use]
pub fn saved_obligation_structural_proof_defect(
    obligation: &ObligationReport,
    trusted_root: Option<&Path>,
) -> Option<String> {
    saved_report_publishable_proof_defect(obligation, trusted_root)
}

/// Canonical suite/backend/artifact identity of a Clean-kernel-certified proof.
/// A kernel certificate is a distinct, STRONGER authority class than a routed
/// solver proof (trust-wp / trust-mc / trust-vc): its publication-grade evidence
/// is the bound `clean_cic` certificate artifact, not a solver request +
/// native-TrustIr bundle. Identity is pinned across suite, backend, AND
/// provenance so a routed solver proof that is merely missing its bundle can
/// never be misclassified onto the kernel lane.
const CLEAN_KERNEL_PROOF_SUITE: &str = "trust-certify";
const CLEAN_KERNEL_PROOF_BACKEND: &str = "clean-kernel";
const CLEAN_KERNEL_CERTIFICATE_KIND: &str = "clean_cic";
const CLEAN_KERNEL_CERTIFICATE_FORMAT: &str = "trust-ir-cleancic-v2";
const CLEAN_KERNEL_PROOF_ID_PREFIX: &str = "clean-cic:v2:";
const CLEAN_KERNEL_CERTIFICATE_URI_PREFIX: &str = "trust-certify://clean-cic/";

fn is_clean_kernel_certified_proof(proof: &ObligationProofEvidenceReport) -> bool {
    proof.suite.as_deref() == Some(CLEAN_KERNEL_PROOF_SUITE)
        && proof.backend == CLEAN_KERNEL_PROOF_BACKEND
        && matches!(
            &proof.provenance,
            ObligationEvidenceProvenanceReport::NativeBackend { verifier }
                if verifier == CLEAN_KERNEL_PROOF_BACKEND
        )
}

/// A Clean-kernel proof's publication-grade evidence is exactly one `clean_cic`
/// certificate artifact whose id, digest, and URI are mutually bound. This does
/// not re-run the kernel type-checker (that is live-replay authority, not a
/// saved-report structural check); it pins the certificate's self-consistent
/// content-addressed identity so a malformed or unbound claim is rejected.
fn clean_kernel_certificate_artifact_defect(
    proof_id: &str,
    artifacts: &[TransportEvidenceArtifact],
) -> Option<String> {
    if artifacts.len() != 1 {
        return Some(format!(
            "clean-kernel proof_evidence must carry exactly one certificate artifact, found {}",
            artifacts.len()
        ));
    }
    let artifact = &artifacts[0];
    if normalized_artifact_kind(&artifact.kind) != CLEAN_KERNEL_CERTIFICATE_KIND {
        return Some("clean-kernel certificate artifact is not a clean_cic node".to_string());
    }
    if artifact.format.as_deref() != Some(CLEAN_KERNEL_CERTIFICATE_FORMAT) {
        return Some(
            "clean-kernel certificate artifact format is not trust-ir-cleancic-v2".to_string(),
        );
    }
    if artifact.artifact_id.as_deref() != Some(proof_id) {
        return Some("clean-kernel certificate artifact_id is not bound to proof_id".to_string());
    }
    let Some(digest) = artifact.digest.as_ref() else {
        return Some("clean-kernel certificate artifact has no digest".to_string());
    };
    if !digest.algorithm.eq_ignore_ascii_case("sha256") {
        return Some("clean-kernel certificate digest algorithm is not sha256".to_string());
    }
    let digest_value = digest.value.trim().to_ascii_lowercase();
    if digest_value.len() != 64 || !digest_value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Some("clean-kernel certificate digest value is not a 64-hex sha256".to_string());
    }
    // proof_id (`clean-cic:v2:<digest>`) and the content-addressed URI must both
    // reconstruct from the certificate digest.
    if proof_id.to_ascii_lowercase() != format!("{CLEAN_KERNEL_PROOF_ID_PREFIX}{digest_value}") {
        return Some(
            "clean-kernel proof_id does not reconstruct from the certificate digest".to_string(),
        );
    }
    if artifact.uri.as_deref().map(str::to_ascii_lowercase)
        != Some(format!("{CLEAN_KERNEL_CERTIFICATE_URI_PREFIX}{digest_value}"))
    {
        return Some(
            "clean-kernel certificate uri does not bind the certificate digest".to_string(),
        );
    }
    if artifact.metadata.is_none() {
        return Some("clean-kernel certificate artifact carries no CleanCic metadata".to_string());
    }
    None
}

/// Structural publication-grade check for a Clean-kernel-certified proved row.
/// It is exactly as strict as the solver lane, but validates the KERNEL
/// certificate (proof_id + bound `clean_cic` artifact + native-backend
/// provenance + publication-grade strength) rather than a routed-solver
/// request/native-TrustIr bundle, which a kernel certificate legitimately does
/// not carry. A kernel proof that smuggles any solver-transport field is
/// rejected so it cannot masquerade as a routed proof.
fn publishable_clean_kernel_proof_defect(proof: &ObligationProofEvidenceReport) -> Option<String> {
    if proof.request_id.is_some() {
        return Some("clean-kernel proof_evidence must not carry a solver request_id".to_string());
    }
    if proof.native_id.is_some() {
        return Some("clean-kernel proof_evidence must not carry a solver native_id".to_string());
    }
    if proof.native_trust_ir.is_some() {
        return Some(
            "clean-kernel proof_evidence must not carry a solver native_trust_ir bundle"
                .to_string(),
        );
    }
    let Some(proof_id) =
        proof.proof_id.as_deref().map(str::trim).filter(|proof_id| !proof_id.is_empty())
    else {
        return Some("clean-kernel proof_evidence.proof_id is missing".to_string());
    };
    if !proof_strength_is_publication_grade(&proof.strength) {
        return Some("clean-kernel proof_evidence.strength is not publication-grade".to_string());
    }
    if !proof_evidence_is_publication_grade(&proof.evidence) {
        return Some("clean-kernel proof_evidence.evidence is not publication-grade".to_string());
    }
    if proof.evidence != ProofEvidence::from(proof.strength.clone()) {
        return Some(
            "clean-kernel proof_evidence.evidence does not match proof_evidence.strength"
                .to_string(),
        );
    }
    if proof.proof_certificate.is_some() {
        return Some(
            "clean-kernel proof_evidence carries unbound raw certificate bytes; certificates must be bound artifacts"
                .to_string(),
        );
    }
    if let Some(defect) = clean_kernel_certificate_artifact_defect(proof_id, &proof.artifacts) {
        return Some(defect);
    }
    if !transport_diagnostics_are_publishable(&proof.diagnostics) {
        return Some("clean-kernel proof_evidence.diagnostics include an error".to_string());
    }
    None
}

fn publishable_obligation_proof_defect(
    proof: &ObligationProofEvidenceReport,
    obligation_id: Option<&str>,
    trusted_root: Option<&Path>,
) -> Option<String> {
    let Some(suite) = proof.suite.as_deref().map(str::trim).filter(|suite| !suite.is_empty())
    else {
        return Some("proof_evidence.suite is missing".to_string());
    };
    if !nonempty(&proof.backend) {
        return Some("proof_evidence.backend is empty".to_string());
    }
    if proof.status != Some(TransportProofStatus::Proved) {
        return Some("proof_evidence.status is not proved".to_string());
    }
    // A Clean-kernel certificate is a distinct, stronger authority class than a
    // routed solver proof: its publication-grade evidence is the bound
    // `clean_cic` certificate artifact, not a solver request + native-TrustIr
    // bundle. Validate it on its own equally-strict lane. The identity predicate
    // pins suite+backend+provenance, so a solver proof missing its bundle cannot
    // reach this branch.
    if is_clean_kernel_certified_proof(proof) {
        return publishable_clean_kernel_proof_defect(proof);
    }
    if proof.request_id.as_deref().map_or(true, |request_id| !nonempty(request_id)) {
        return Some("proof_evidence.request_id is missing".to_string());
    }
    if proof.proof_id.as_deref().map_or(true, |proof_id| !nonempty(proof_id)) {
        return Some("proof_evidence.proof_id is missing".to_string());
    }
    if proof.native_id.as_deref().map_or(true, |native_id| !nonempty(native_id)) {
        return Some("proof_evidence.native_id is missing".to_string());
    }
    if !proof_strength_is_publication_grade(&proof.strength) {
        return Some("proof_evidence.strength is not publication-grade".to_string());
    }
    if !proof_evidence_is_publication_grade(&proof.evidence) {
        return Some("proof_evidence.evidence is not publication-grade".to_string());
    }
    if proof.evidence != ProofEvidence::from(proof.strength.clone()) {
        return Some("proof_evidence.evidence does not match proof_evidence.strength".to_string());
    }
    match &proof.provenance {
        ObligationEvidenceProvenanceReport::NativeBackend { verifier }
            if verifier == &proof.backend => {}
        ObligationEvidenceProvenanceReport::NativeBackend { .. } => {
            return Some("proof_evidence native verifier does not match backend".to_string());
        }
        ObligationEvidenceProvenanceReport::RouterAttributed => {
            return Some("proof_evidence provenance is not native-backend attributed".to_string());
        }
    }
    if proof.proof_certificate.is_some() {
        return Some(
            "proof_evidence carries unbound raw certificate bytes; certificates must be bound artifacts"
                .to_string(),
        );
    }

    let Some(native_trust_ir) = &proof.native_trust_ir else {
        return Some("proof_evidence.native_trust_ir is missing".to_string());
    };
    if let Some(defect) = publishable_native_trust_ir_defect(suite, proof, native_trust_ir) {
        return Some(defect);
    }

    let topology_defect = match trusted_root {
        Some(root) => transport_proof_artifact_topology_defect_at_root(
            suite,
            &proof.artifacts,
            obligation_id,
            root,
        ),
        None => transport_proof_artifact_topology_defect(suite, &proof.artifacts, obligation_id),
    };
    if let Some(defect) = topology_defect {
        return Some(format!("proof_evidence.artifact topology is invalid: {defect}"));
    }
    if !transport_diagnostics_are_publishable(&proof.diagnostics) {
        return Some("proof_evidence.diagnostics include an error".to_string());
    }
    let native_shape_is_publishable = match trusted_root {
        Some(root) => native_trust_ir_artifact_shape_is_publishable_at_root(native_trust_ir, root),
        None => native_trust_ir_artifact_shape_is_publishable(native_trust_ir),
    };
    if !native_shape_is_publishable {
        return Some(
            "proof_evidence.native_trust_ir lacks the canonical bundle/request/obligation artifact shape"
                .to_string(),
        );
    }

    None
}

fn matching_transport_evidence_defect(
    obligation: &ObligationReport,
    proof: &ObligationProofEvidenceReport,
) -> Option<String> {
    let Some(transport) = &obligation.transport_evidence else {
        return Some("transport_evidence is missing".to_string());
    };
    if transport.obligation_id.as_deref() != obligation.obligation_id.as_deref() {
        return Some("transport_evidence.obligation_id does not match obligation_id".to_string());
    }

    // A Clean-kernel proof carries no solver native_trust_ir bundle; the
    // transport retains the ORIGINAL routed-dispatch bundle as provenance, so
    // the two legitimately differ and are not matched here. The transport's own
    // proof_evidence record must still match the published kernel proof exactly.
    if is_clean_kernel_certified_proof(proof) {
        return transport_proof_evidence_match_defect(transport, proof);
    }

    let Some(transport_native) = &transport.native_trust_ir else {
        return Some("transport_evidence.native_trust_ir is missing".to_string());
    };
    let Some(proof_native) = &proof.native_trust_ir else {
        return Some("proof_evidence.native_trust_ir is missing".to_string());
    };
    if transport_native != proof_native {
        return Some(
            "transport_evidence.native_trust_ir does not match proof_evidence".to_string(),
        );
    }

    transport_proof_evidence_match_defect(transport, proof)
}

/// The transport envelope's own `proof_evidence` record must reproduce the
/// published proof exactly. Shared by the routed-solver and Clean-kernel lanes;
/// only the separate native-TrustIr bundle relationship differs between them.
fn transport_proof_evidence_match_defect(
    transport: &ObligationTransportEvidenceReport,
    proof: &ObligationProofEvidenceReport,
) -> Option<String> {
    let Some(transport_proof) = &transport.proof_evidence else {
        return Some("transport_evidence.proof_evidence is missing".to_string());
    };
    if transport_proof.suite != proof.suite.as_deref().unwrap_or_default() {
        return Some("transport_evidence.proof_evidence.suite does not match".to_string());
    }
    if transport_proof.backend != proof.backend {
        return Some("transport_evidence.proof_evidence.backend does not match".to_string());
    }
    if transport_proof.request_id != proof.request_id {
        return Some("transport_evidence.proof_evidence.request_id does not match".to_string());
    }
    if transport_proof.proof_id != proof.proof_id {
        return Some("transport_evidence.proof_evidence.proof_id does not match".to_string());
    }
    if transport_proof.native_id != proof.native_id {
        return Some("transport_evidence.proof_evidence.native_id does not match".to_string());
    }
    if transport_proof.status != TransportProofStatus::Proved {
        return Some("transport_evidence.proof_evidence.status is not proved".to_string());
    }
    if transport_proof.strength.as_ref() != Some(&proof.strength) {
        return Some("transport_evidence.proof_evidence.strength does not match".to_string());
    }
    if transport_proof.evidence.as_ref() != Some(&proof.evidence) {
        return Some("transport_evidence.proof_evidence.evidence does not match".to_string());
    }
    if transport_proof.artifacts != proof.artifacts {
        return Some("transport_evidence.proof_evidence.artifacts do not match".to_string());
    }
    if transport_proof.diagnostics != proof.diagnostics {
        return Some("transport_evidence.proof_evidence.diagnostics do not match".to_string());
    }

    None
}

fn publishable_native_trust_ir_defect(
    suite: &str,
    proof: &ObligationProofEvidenceReport,
    native_trust_ir: &TransportNativeTrustIrEvidence,
) -> Option<String> {
    let canonical_suite = suite.trim().to_ascii_lowercase();
    if !matches!(canonical_suite.as_str(), "trust-wp" | "trust-mc" | "trust-vc") {
        return Some("proof_evidence.suite is not a canonical native TrustIr suite".to_string());
    }
    if !native_trust_ir.present {
        return Some("proof_evidence.native_trust_ir.present is false".to_string());
    }
    if native_trust_ir.suite.trim().to_ascii_lowercase() != canonical_suite {
        return Some("proof_evidence.native_trust_ir.suite does not match proof suite".to_string());
    }
    if proof.backend.trim().to_ascii_lowercase() != canonical_suite {
        return Some(
            "proof_evidence.backend is not bound to the canonical native TrustIr suite".to_string(),
        );
    }
    if native_trust_ir.backend.trim().to_ascii_lowercase() != canonical_suite {
        return Some(
            "proof_evidence.native_trust_ir.backend is not bound to the canonical suite"
                .to_string(),
        );
    }
    if native_trust_ir.request_id.as_deref() != proof.request_id.as_deref() {
        return Some("proof_evidence.native_trust_ir.request_id does not match".to_string());
    }
    if native_trust_ir.native_id.as_deref() != proof.native_id.as_deref() {
        return Some("proof_evidence.native_trust_ir.native_id does not match".to_string());
    }
    let request_id = proof.request_id.as_deref().expect("request_id checked before native shape");
    let proof_id = proof.proof_id.as_deref().expect("proof_id checked before native shape");
    let native_id = proof.native_id.as_deref().expect("native_id checked before native shape");
    let expected_native_id =
        format!("trust_ir-native-{canonical_suite}-request-{request_id}-proof-{proof_id}");
    if native_id != expected_native_id {
        return Some("proof_evidence.proof_id/request_id do not reconstruct native_id".to_string());
    }
    if proof.artifacts.iter().any(|artifact| {
        artifact
            .materialization
            .as_ref()
            .is_some_and(|materialization| materialization.proof_binding_id != native_id)
    }) {
        return Some(
            "proof_evidence artifact proof_binding_id does not match native_id".to_string(),
        );
    }
    if !transport_diagnostics_are_publishable(&native_trust_ir.diagnostics) {
        return Some("proof_evidence.native_trust_ir diagnostics include an error".to_string());
    }
    None
}

fn proof_strength_is_publication_grade(strength: &ProofStrength) -> bool {
    !strength.is_bounded()
        && strength.reasoning.is_complete()
        && strength.assurance.meets_reporting_floor()
}

fn proof_evidence_is_publication_grade(evidence: &ProofEvidence) -> bool {
    !evidence.is_bounded()
        && evidence.reasoning.is_complete()
        && evidence.assurance.meets_reporting_floor()
}

fn is_native_trust_ir_structural_artifact(artifact: &TransportEvidenceArtifact) -> bool {
    matches!(
        normalized_artifact_kind(&artifact.kind).as_str(),
        "engine_input" | "normalized_obligation"
    ) && artifact
        .uri
        .as_deref()
        .is_some_and(|uri| uri.starts_with("trust_ir-native://verification-bundle/"))
}

const EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC: &[u8] =
    b"trust.evidence-artifact-binding-envelope.v1\0";

/// Return a fail-closed defect for the exact materialized proof-artifact DAG.
/// Native TrustIr bundle/request/obligation artifacts form a separately
/// validated identity domain and are excluded only when they use that exact
/// structural URI/kind shape.
pub fn transport_proof_artifact_topology_defect(
    suite: &str,
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
) -> Option<String> {
    transport_proof_artifact_topology_defect_with_root(suite, artifacts, obligation_id, None)
}

/// Validate the exact proof-artifact DAG while resolving path-backed
/// materializations only beneath an explicit canonical trusted root.
pub fn transport_proof_artifact_topology_defect_at_root(
    suite: &str,
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
    trusted_root: &Path,
) -> Option<String> {
    transport_proof_artifact_topology_defect_with_root(
        suite,
        artifacts,
        obligation_id,
        Some(trusted_root),
    )
}

fn transport_proof_artifact_topology_defect_with_root(
    suite: &str,
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
    trusted_root: Option<&Path>,
) -> Option<String> {
    let Some(obligation_id) = obligation_id else {
        return Some("proof artifact owner obligation_id is missing".to_string());
    };
    if obligation_id.is_empty()
        || obligation_id.trim() != obligation_id
        || obligation_id.len() > 1024
        || obligation_id.bytes().any(|byte| !byte.is_ascii_graphic() || matches!(byte, b'?' | b'#'))
    {
        return Some("proof artifact owner obligation_id is not canonical".to_string());
    }
    if artifacts.len() > MAX_TRANSPORT_EVIDENCE_ARTIFACTS {
        return Some(format!(
            "proof artifacts exceed the per-evidence {}-artifact safety limit",
            MAX_TRANSPORT_EVIDENCE_ARTIFACTS
        ));
    }
    let mut identities = BTreeSet::new();
    let mut materialized_paths = BTreeSet::new();
    for artifact in artifacts {
        if let Some(digest) = artifact.digest.as_ref()
            && !identities.insert((artifact.kind.as_str(), digest))
        {
            return Some("proof artifacts contain a duplicate kind/digest node".to_string());
        }
        if let Some(path) = artifact
            .materialization
            .as_ref()
            .and_then(|materialization| materialization.materialized_path.as_deref())
            && !materialized_paths.insert(path)
        {
            return Some("proof artifacts contain a duplicate materialization path".to_string());
        }
    }

    let certificates = artifacts
        .iter()
        .filter(|artifact| normalized_artifact_kind(&artifact.kind) == "proof_certificate")
        .collect::<Vec<_>>();
    let transcripts = artifacts
        .iter()
        .filter(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
        .collect::<Vec<_>>();
    let replays = artifacts
        .iter()
        .filter(|artifact| {
            matches!(
                normalized_artifact_kind(&artifact.kind).as_str(),
                "proof_replay_trace" | "replay_log"
            )
        })
        .collect::<Vec<_>>();
    let checks = artifacts
        .iter()
        .filter(|artifact| normalized_artifact_kind(&artifact.kind) == "proof_check_report")
        .collect::<Vec<_>>();
    let models = artifacts
        .iter()
        .filter(|artifact| normalized_artifact_kind(&artifact.kind) == "model")
        .collect::<Vec<_>>();

    let certificate_route = certificates.len() == 1
        && transcripts.is_empty()
        && replays.is_empty()
        && checks.is_empty()
        && models.is_empty();
    if certificate_route {
        let certificate = certificates[0];
        if !suite.eq_ignore_ascii_case("trust-vc")
            || !is_trust_vc_digest_bound_proof_certificate_artifact(certificate)
            || !transport_artifact_has_bound_payload(certificate, obligation_id, trusted_root)
            || !certificate
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.referenced_artifacts.is_empty())
        {
            return Some(
                "exclusive proof-certificate route is not exactly materialized and digest-bound"
                    .to_string(),
            );
        }
        if artifacts.iter().any(|artifact| {
            artifact.materialization.is_some()
                && !is_native_trust_ir_structural_artifact(artifact)
                && !std::ptr::eq(artifact, certificate)
        }) {
            return Some(
                "proof-certificate route contains a materialized extra artifact".to_string(),
            );
        }
        return None;
    }

    if !certificates.is_empty() {
        return Some(
            "proof artifact routes are mixed or contain duplicate certificates".to_string(),
        );
    }
    if transcripts.len() != 1 || replays.len() > 1 || checks.len() > 1 || models.len() > 1 {
        return Some(format!(
            "proof DAG requires one transcript, at most one model, at most one replay, and at most one check; transcripts={}, models={}, replays={}, checks={}",
            transcripts.len(),
            models.len(),
            replays.len(),
            checks.len()
        ));
    }
    if replays.is_empty() && checks.is_empty() {
        return Some("proof DAG has no replay/check consumer".to_string());
    }
    let transcript = transcripts[0];
    if !transport_artifact_has_bound_payload(transcript, obligation_id, trusted_root) {
        return Some("solver transcript lacks an exact owner-bound materialization".to_string());
    }
    let binding = transcript.materialization.as_ref()?.proof_binding_id.as_str();

    let mut allowed = vec![transport_artifact_identity(transcript)?];
    let mut structural_inputs = Vec::new();
    let transcript_references = &transcript.materialization.as_ref()?.referenced_artifacts;
    if transcript_references.is_empty() {
        return Some(
            "solver transcript does not reference an exact structural proof input".to_string(),
        );
    }
    for reference in transcript_references {
        if !matches!(
            normalized_artifact_kind(&reference.kind).as_str(),
            "engine_input" | "normalized_obligation"
        ) {
            return Some(
                "solver transcript references a non-structural or future artifact role".to_string(),
            );
        }
        let mut targets = artifacts.iter().filter(|artifact| {
            artifact.kind == reference.kind && artifact.digest.as_ref() == Some(&reference.digest)
        });
        let Some(target) = targets.next() else {
            return Some("solver transcript structural reference has no target".to_string());
        };
        if targets.next().is_some()
            || !transport_artifact_has_bound_payload(target, obligation_id, trusted_root)
            || target.materialization.as_ref().map(|value| value.proof_binding_id.as_str())
                != Some(binding)
            || !target
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.referenced_artifacts.is_empty())
        {
            return Some(
                "solver transcript structural reference target is ambiguous or invalid".to_string(),
            );
        }
        allowed.push(transport_artifact_identity(target)?);
        structural_inputs.push(target);
    }

    let model = models.first().copied();
    if let Some(model) = model {
        if !transport_artifact_has_bound_payload(model, obligation_id, trusted_root)
            || model.materialization.as_ref().map(|value| value.proof_binding_id.as_str())
                != Some(binding)
            || !transport_artifact_references_exactly(model, &structural_inputs)
        {
            return Some(
                "invariant model does not consume exactly the transcript's structural proof inputs"
                    .to_string(),
            );
        }
        allowed.push(transport_artifact_identity(model)?);
    }

    if let Some(replay) = replays.first().copied() {
        let valid_references = model.map_or_else(
            || transport_artifact_references_exactly(replay, &[transcript]),
            |model| transport_artifact_references_exactly(replay, &[transcript, model]),
        );
        if !transport_artifact_has_bound_payload(replay, obligation_id, trusted_root)
            || replay.materialization.as_ref().map(|value| value.proof_binding_id.as_str())
                != Some(binding)
            || !valid_references
        {
            return Some("replay artifact has an invalid exact backward reference set".to_string());
        }
        allowed.push(transport_artifact_identity(replay)?);
    }
    if let Some(check) = checks.first().copied() {
        let valid_references = match (model, replays.first().copied()) {
            (Some(model), Some(replay)) => {
                transport_artifact_references_exactly(check, &[transcript, model, replay])
            }
            (Some(model), None) => {
                transport_artifact_references_exactly(check, &[transcript, model])
            }
            (None, Some(replay)) => {
                transport_artifact_references_exactly(check, &[replay])
                    || transport_artifact_references_exactly(check, &[transcript, replay])
            }
            (None, None) => transport_artifact_references_exactly(check, &[transcript]),
        };
        if !transport_artifact_has_bound_payload(check, obligation_id, trusted_root)
            || check.materialization.as_ref().map(|value| value.proof_binding_id.as_str())
                != Some(binding)
            || !valid_references
        {
            return Some("proof-check artifact has an invalid backward reference set".to_string());
        }
        allowed.push(transport_artifact_identity(check)?);
    }
    if artifacts.iter().any(|artifact| {
        artifact.materialization.is_some()
            && !is_native_trust_ir_structural_artifact(artifact)
            && transport_artifact_identity(artifact)
                .is_none_or(|identity| !allowed.contains(&identity))
    }) {
        return Some("proof DAG contains an unreferenced materialized extra artifact".to_string());
    }
    None
}

fn transport_artifact_identity(
    artifact: &TransportEvidenceArtifact,
) -> Option<(String, TransportArtifactDigest)> {
    Some((artifact.kind.clone(), artifact.digest.clone()?))
}

fn transport_artifact_references_exactly(
    consumer: &TransportEvidenceArtifact,
    consumed: &[&TransportEvidenceArtifact],
) -> bool {
    let Some(materialization) = &consumer.materialization else {
        return false;
    };
    let Some(mut expected) = consumed
        .iter()
        .map(|artifact| {
            artifact
                .digest
                .clone()
                .map(|digest| TransportArtifactReference { kind: artifact.kind.clone(), digest })
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    expected.sort();
    // The backward-reference contract is set equality. Producers order their
    // references by typed artifact role, which need not match this string-keyed
    // DTO's lexical order. Sort clones for membership comparison while keeping
    // the stored sequence unchanged for bound-envelope validation.
    let mut declared = materialization.referenced_artifacts.clone();
    declared.sort();
    declared == expected
}

fn transport_artifact_has_bound_payload(
    artifact: &TransportEvidenceArtifact,
    obligation_id: &str,
    trusted_root: Option<&Path>,
) -> bool {
    let Some(digest) = artifact.digest.as_ref() else {
        return false;
    };
    let Some(materialization) = artifact.materialization.as_ref() else {
        return false;
    };
    if !artifact.uri.as_deref().is_some_and(|uri| uri.contains(&digest.value)) {
        return false;
    }
    let bytes = match trusted_root {
        Some(root) => materialization.decoded_bytes_at_root(digest, root),
        None if materialization.matches_sha256_digest(digest) => materialization.decoded_bytes(),
        None => {
            Err("path-backed artifact materialization has no explicit trusted root".to_string())
        }
    };
    let Ok(bytes) = bytes else {
        return false;
    };
    transport_bound_payload_matches(
        &bytes,
        &artifact.kind,
        obligation_id,
        &materialization.proof_binding_id,
        &materialization.referenced_artifacts,
    )
}

fn transport_bound_payload_matches(
    bytes: &[u8],
    kind: &str,
    obligation_id: &str,
    proof_binding_id: &str,
    references: &[TransportArtifactReference],
) -> bool {
    let mut cursor = EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC.len();
    if !bytes.starts_with(EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC)
        || transport_binding_field(bytes, &mut cursor) != Some(kind.as_bytes())
        || transport_binding_field(bytes, &mut cursor) != Some(obligation_id.as_bytes())
        || transport_binding_field(bytes, &mut cursor) != Some(proof_binding_id.as_bytes())
        || transport_binding_u32(bytes, &mut cursor).map(|count| count as usize)
            != Some(references.len())
    {
        return false;
    }
    for reference in references {
        if transport_binding_field(bytes, &mut cursor) != Some(reference.kind.as_bytes())
            || transport_binding_field(bytes, &mut cursor)
                != Some(reference.digest.algorithm.as_bytes())
            || transport_binding_field(bytes, &mut cursor)
                != Some(reference.digest.value.as_bytes())
        {
            return false;
        }
    }
    let Some(payload_len) =
        transport_binding_u64(bytes, &mut cursor).and_then(|len| usize::try_from(len).ok())
    else {
        return false;
    };
    payload_len > 0 && cursor.checked_add(payload_len) == Some(bytes.len())
}

fn transport_binding_field<'a>(bytes: &'a [u8], cursor: &mut usize) -> Option<&'a [u8]> {
    let len = transport_binding_u32(bytes, cursor)? as usize;
    let end = (*cursor).checked_add(len)?;
    let field = bytes.get(*cursor..end)?;
    *cursor = end;
    Some(field)
}

fn transport_binding_u32(bytes: &[u8], cursor: &mut usize) -> Option<u32> {
    let end = (*cursor).checked_add(4)?;
    let value = u32::from_be_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    Some(value)
}

fn transport_binding_u64(bytes: &[u8], cursor: &mut usize) -> Option<u64> {
    let end = (*cursor).checked_add(8)?;
    let value = u64::from_be_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    Some(value)
}

/// Whether native TrustIr transport evidence has the exact artifact topology
/// produced by the in-tree router: one content-addressed bundle, one
/// suite/request view, and one normalized obligation view, all under the same
/// identity-bearing `trust_ir-native://verification-bundle/...` URI tree.
///
/// This is intentionally stricter than checking for any digest-bearing
/// artifact.  Artifact kinds and URIs are producer-controlled inputs at report
/// ingestion time, so an arbitrary artifact must not stand in for native
/// TrustIr identity evidence.
pub fn native_trust_ir_artifact_shape_is_publishable(
    native: &TransportNativeTrustIrEvidence,
) -> bool {
    native_trust_ir_artifact_shape_is_publishable_with_root(native, None)
}

/// Validate native TrustIr structural materializations while resolving any
/// path-backed bytes beneath an explicit canonical trusted root.
#[must_use]
pub fn native_trust_ir_artifact_shape_is_publishable_at_root(
    native: &TransportNativeTrustIrEvidence,
    trusted_root: &Path,
) -> bool {
    native_trust_ir_artifact_shape_is_publishable_with_root(native, Some(trusted_root))
}

fn native_trust_ir_artifact_shape_is_publishable_with_root(
    native: &TransportNativeTrustIrEvidence,
    trusted_root: Option<&Path>,
) -> bool {
    let suite = native.suite.trim().to_ascii_lowercase();
    if !matches!(suite.as_str(), "trust-wp" | "trust-mc" | "trust-vc") {
        return false;
    }
    let Some(request_id) =
        native.request_id.as_deref().map(str::trim).filter(|id| {
            !id.is_empty() && !id.contains('/') && !id.contains('?') && !id.contains('#')
        })
    else {
        return false;
    };
    let Some(native_id) = native.native_id.as_deref() else {
        return false;
    };
    let native_id_prefix = format!("trust_ir-native-{suite}-request-{request_id}-proof-");
    let Some(proof_id) = native_id
        .strip_prefix(&native_id_prefix)
        .filter(|id| !id.is_empty() && !id.contains('/') && !id.contains('?') && !id.contains('#'))
    else {
        return false;
    };
    if native.artifacts.len() != 3 {
        return false;
    }
    let mut materialized_paths = BTreeSet::new();
    if native
        .artifacts
        .iter()
        .filter_map(|artifact| {
            artifact
                .materialization
                .as_ref()
                .and_then(|materialization| materialization.materialized_path.as_deref())
        })
        .any(|path| !materialized_paths.insert(path))
    {
        return false;
    }

    const URI_PREFIX: &str = "trust_ir-native://verification-bundle/";
    let mut common_bundle = None::<String>;
    let mut bundle_digest = None::<String>;
    let mut request_digest = None::<String>;
    let mut normalized_digest = None::<String>;
    let mut normalized_request_digest = None::<String>;

    for artifact in &native.artifacts {
        let Some(digest) = artifact.digest.as_ref().filter(|digest| {
            is_canonical_sha256_digest(digest)
                && artifact.materialization.as_ref().is_some_and(|materialization| {
                    materialization.proof_binding_id == native_id
                        && match trusted_root {
                            Some(root) => {
                                materialization.matches_sha256_digest_at_root(digest, root)
                            }
                            None => materialization.matches_sha256_digest(digest),
                        }
                })
        }) else {
            return false;
        };
        let Some(uri) = artifact.uri.as_deref().and_then(|uri| uri.strip_prefix(URI_PREFIX)) else {
            return false;
        };
        let segments = uri.split('/').collect::<Vec<_>>();
        let Some(bundle) = segments.first().copied().filter(|bundle| {
            bundle.len() == 64
                && bundle.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        }) else {
            return false;
        };
        if common_bundle.as_deref().is_some_and(|expected| expected != bundle) {
            return false;
        }
        common_bundle.get_or_insert_with(|| bundle.to_string());

        match (normalized_artifact_kind(&artifact.kind).as_str(), segments.as_slice()) {
            ("engine_input", [_])
                if bundle_digest.is_none()
                    && digest.value == bundle
                    && artifact.materialization.as_ref().is_some_and(|materialization| {
                        materialization.referenced_artifacts.is_empty()
                            && native_materialization_envelope_matches(
                                materialization,
                                digest,
                                trusted_root,
                                "bundle",
                                None,
                                None,
                                None,
                            )
                    }) =>
            {
                bundle_digest = Some(digest.value.clone());
            }
            ("engine_input", [_, uri_suite, "request", uri_request, uri_request_digest])
                if request_digest.is_none()
                    && *uri_suite == suite
                    && *uri_request == request_id
                    && *uri_request_digest == digest.value
                    && artifact.materialization.as_ref().is_some_and(|materialization| {
                        native_materialization_envelope_matches(
                            materialization,
                            digest,
                            trusted_root,
                            "request",
                            Some(&suite),
                            Some(request_id),
                            None,
                        ) && materialization.referenced_artifacts.as_slice()
                            == [TransportArtifactReference {
                                kind: "EngineInput".to_string(),
                                digest: TransportArtifactDigest {
                                    algorithm: "sha256".to_string(),
                                    value: bundle.to_string(),
                                },
                            }]
                    }) =>
            {
                request_digest = Some(digest.value.clone());
            }
            (
                "normalized_obligation",
                [
                    _,
                    uri_suite,
                    "request",
                    uri_request,
                    uri_request_digest,
                    "proof",
                    uri_proof,
                    uri_proof_digest,
                ],
            ) if normalized_digest.is_none()
                && *uri_suite == suite
                && *uri_request == request_id
                && *uri_proof == proof_id
                && *uri_proof_digest == digest.value
                && artifact.materialization.as_ref().is_some_and(|materialization| {
                    native_materialization_envelope_matches(
                        materialization,
                        digest,
                        trusted_root,
                        "normalized_obligation",
                        Some(&suite),
                        Some(request_id),
                        Some(proof_id),
                    ) && materialization.referenced_artifacts.as_slice()
                        == [TransportArtifactReference {
                            kind: "EngineInput".to_string(),
                            digest: TransportArtifactDigest {
                                algorithm: "sha256".to_string(),
                                value: uri_request_digest.to_string(),
                            },
                        }]
                }) =>
            {
                normalized_digest = Some(digest.value.clone());
                normalized_request_digest = Some(uri_request_digest.to_string());
            }
            _ => return false,
        }
    }

    bundle_digest.is_some()
        && request_digest.is_some()
        && request_digest == normalized_request_digest
        && normalized_digest.is_some()
}

fn native_materialization_envelope_matches(
    materialization: &TransportArtifactMaterialization,
    digest: &TransportArtifactDigest,
    trusted_root: Option<&Path>,
    role: &str,
    suite: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
) -> bool {
    let bytes = match trusted_root {
        Some(root) => materialization.decoded_bytes_at_root(digest, root),
        None => materialization.decoded_bytes(),
    };
    let Ok(bytes) = bytes else {
        return false;
    };
    let Ok(mut value) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return false;
    };
    let Some(object) = value.as_object() else {
        return false;
    };
    if object.len() != 6
        || object.get("schema").and_then(serde_json::Value::as_str)
            != Some(NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA)
        || object.get("role").and_then(serde_json::Value::as_str) != Some(role)
        || json_optional_string(object.get("suite")) != Some(suite)
        || json_optional_string(object.get("request_id")) != Some(request_id)
        || json_optional_string(object.get("proof_id")) != Some(proof_id)
        || object.get("payload").is_none_or(serde_json::Value::is_null)
    {
        return false;
    }
    crate::digest::canonicalize_json_in_place(&mut value);
    serde_json::to_vec(&value).is_ok_and(|canonical| canonical == bytes)
}

fn json_optional_string(value: Option<&serde_json::Value>) -> Option<Option<&str>> {
    match value? {
        serde_json::Value::Null => Some(None),
        serde_json::Value::String(value) => Some(Some(value.as_str())),
        _ => None,
    }
}

fn is_canonical_sha256_digest(digest: &TransportArtifactDigest) -> bool {
    digest.algorithm == "sha256" && crate::digest::is_stable_sha256_hex(&digest.value)
}

/// URI prefix emitted for TrustIr-imported trust-vc proof certificates.
pub const TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX: &str =
    "artifact://trust-vc/native-trust-ir-proof-artifacts/";
/// URI prefix emitted for exported trust-vc replayable proof certificates.
pub const TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX: &str = "artifact://trust-vc/proof-artifacts/";
/// Artifact identity prefix emitted for trust-vc proof certificates.
pub const TRUST_VC_PROOF_ARTIFACT_ID_PREFIX: &str = "trust-vc-proof-certificate:v1:";

fn normalized_artifact_kind(kind: &str) -> String {
    let mut normalized = String::new();
    let mut previous_was_lower_or_digit = false;
    let mut previous_was_separator = false;

    for ch in kind.trim().chars() {
        if ch.is_ascii_alphanumeric() {
            if ch.is_ascii_uppercase() {
                if !normalized.is_empty() && !previous_was_separator && previous_was_lower_or_digit
                {
                    normalized.push('_');
                }
                normalized.push(ch.to_ascii_lowercase());
                previous_was_lower_or_digit = false;
            } else {
                normalized.push(ch.to_ascii_lowercase());
                previous_was_lower_or_digit = ch.is_ascii_lowercase() || ch.is_ascii_digit();
            }
            previous_was_separator = false;
        } else if !normalized.is_empty() && !previous_was_separator {
            normalized.push('_');
            previous_was_lower_or_digit = false;
            previous_was_separator = true;
        }
    }

    while normalized.ends_with('_') {
        normalized.pop();
    }

    normalized
}

/// Whether an artifact exactly matches one of the two certificate URI forms
/// emitted by the trust-vc producers and binds that URI to its SHA-256 digest.
pub fn is_trust_vc_digest_bound_proof_certificate_artifact(
    artifact: &TransportEvidenceArtifact,
) -> bool {
    if normalized_artifact_kind(&artifact.kind) != "proof_certificate" {
        return false;
    }
    let Some(digest) = artifact.digest.as_ref().filter(|digest| is_canonical_sha256_digest(digest))
    else {
        return false;
    };
    let Some(uri) = artifact.uri.as_deref().map(str::trim).filter(|uri| !uri.is_empty()) else {
        return false;
    };

    trust_vc_proof_certificate_uri_matches_digest(uri, &digest.value)
}

fn trust_vc_proof_certificate_uri_matches_digest(uri: &str, digest: &str) -> bool {
    let exported_id = format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{digest}");
    [
        format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{digest}.json"),
        format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}.alethe"),
    ]
    .iter()
    .any(|expected| uri == expected)
}

fn transport_diagnostics_are_publishable(diagnostics: &[TransportEvidenceDiagnostic]) -> bool {
    diagnostics
        .iter()
        .all(|diagnostic| diagnostic.severity != TransportEvidenceDiagnosticSeverity::Error)
}

fn nonempty(value: &str) -> bool {
    !value.trim().is_empty()
}

#[derive(Debug, Clone, Copy)]
struct DeserializedFunctionResiduals {
    total: usize,
    failed: usize,
    unknown: usize,
    timed_out: usize,
    unattributed_failed: usize,
    unattributed_unknown: usize,
    unattributed_proved: usize,
}

impl From<&FunctionSummary> for DeserializedFunctionResiduals {
    fn from(summary: &FunctionSummary) -> Self {
        Self {
            total: summary.total_obligations,
            failed: summary.failed,
            unknown: summary.unknown,
            timed_out: summary.timed_out,
            unattributed_failed: summary.unattributed_failed,
            unattributed_unknown: summary.unattributed_unknown,
            unattributed_proved: summary.unattributed_proved,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct DeserializedCrateResiduals {
    failed: usize,
    unknown: usize,
    proved: usize,
}

impl DeserializedCrateResiduals {
    fn from_report(summary: &CrateSummary, functions: &[DeserializedFunctionResiduals]) -> Self {
        let (function_failed, function_unknown, function_proved) = functions.iter().fold(
            (0usize, 0usize, 0usize),
            |(failed, unknown, proved), function| {
                (
                    failed.saturating_add(function.unattributed_failed),
                    unknown.saturating_add(function.unattributed_unknown),
                    proved.saturating_add(function.unattributed_proved),
                )
            },
        );
        Self {
            failed: summary.total_unattributed_failed.saturating_sub(function_failed),
            unknown: summary.total_unattributed_unknown.saturating_sub(function_unknown),
            proved: summary.total_unattributed_proved.saturating_sub(function_proved),
        }
    }
}

fn recompute_deserialized_function_summary(function: &mut FunctionProofReport) {
    let residuals = DeserializedFunctionResiduals::from(&function.summary);
    recompute_function_summary(function, Some(residuals));
}

fn recompute_function_summary(
    function: &mut FunctionProofReport,
    deserialized: Option<DeserializedFunctionResiduals>,
) {
    let (mut proved, mut runtime, mut failed, mut unknown, mut timed_out, mut design) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for obligation in &function.obligations {
        match &obligation.outcome {
            ObligationOutcome::Proved { .. } => proved += 1,
            ObligationOutcome::RuntimeChecked { .. } => runtime += 1,
            ObligationOutcome::Failed { .. } => failed += 1,
            ObligationOutcome::Unknown { .. } => unknown += 1,
            ObligationOutcome::Timeout { .. } => {
                unknown += 1;
                timed_out += 1;
            }
            ObligationOutcome::DesignRequirement { .. } => design += 1,
        }
    }

    let mut total = function.obligations.len();
    if let Some(reported) = deserialized {
        let mut missing_rows = reported.total.saturating_sub(total);
        let residual_failed = reported.failed.saturating_sub(failed).min(missing_rows);
        failed = failed.saturating_add(residual_failed);
        missing_rows -= residual_failed;

        let wanted_timeouts = reported.timed_out.saturating_sub(timed_out);
        let wanted_unknown = reported.unknown.saturating_sub(unknown).max(wanted_timeouts);
        let residual_unknown = wanted_unknown.min(missing_rows);
        let residual_timeouts = wanted_timeouts.min(residual_unknown);
        unknown = unknown.saturating_add(residual_unknown);
        timed_out = timed_out.saturating_add(residual_timeouts);
        missing_rows -= residual_unknown;

        // Any remaining summary-only rows are unknown. Serialized `proved`,
        // runtime-check, and design-mandate counts have no row or live
        // authority and therefore cannot retain their optimistic category.
        unknown = unknown.saturating_add(missing_rows);
        total = total.saturating_add(
            residual_failed.saturating_add(residual_unknown).saturating_add(missing_rows),
        );
        function.summary.unattributed_failed = reported.unattributed_failed;
        function.summary.unattributed_unknown =
            reported.unattributed_unknown.saturating_add(reported.unattributed_proved);
        function.summary.unattributed_proved = 0;
    }
    function.summary.total_obligations = total;
    function.summary.proved = proved;
    function.summary.runtime_checked = runtime;
    function.summary.failed = failed;
    function.summary.unknown = unknown;
    function.summary.timed_out = timed_out;
    function.summary.design_requirements = design;
    function.summary.verdict =
        ScopeVerdict::from_counts(ScopeVerdictCounts::from(&function.summary));
}

/// A single NDJSON line for streaming output. Each line is one function result.
///
/// This wire DTO is intentionally Serialize-only. A standalone function line
/// lacks the crate-wide context needed to run [`JsonProofReport`]'s saved-report
/// authority gate, so typed deserialization would be a proof-gating bypass.
#[derive(Debug, Clone, Serialize)]
pub struct NdjsonFunctionRecord {
    /// Record type tag for stream parsing.
    pub record_type: String,
    /// Crate this function belongs to.
    pub crate_name: String,
    /// The function report.
    #[serde(flatten)]
    pub function: FunctionProofReport,
}

/// NDJSON header record emitted at the start of a stream.
///
/// NDJSON wire DTOs are intentionally Serialize-only; see
/// [`NdjsonFunctionRecord`].
#[derive(Debug, Clone, Serialize)]
pub struct NdjsonHeader {
    /// Always "header".
    pub record_type: String,
    /// Versioned stream schema.
    pub schema: String,
    /// Saved streams are observational records; they never carry live proof
    /// authority across the serialization boundary.
    pub authority: String,
    /// Report metadata.
    pub metadata: ReportMetadata,
    /// Crate being verified.
    pub crate_name: String,
    /// Number of ordered function records expected before the footer.
    pub expected_functions: usize,
    /// Hardened boundary policy/context from the canonical report.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hardened: Option<HardenedReportContext>,
    /// Assumption ledger from the canonical report.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub assumptions: Vec<AssumptionEntry>,
    /// Exact final Targo gate, including exit and coverage state.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verification_gate: Option<VerificationGateReport>,
    /// Observational Cargo proof-unit inventory from the canonical report.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cargo_proof_inventory: Option<CargoProofInventoryReport>,
}

/// NDJSON footer record emitted at the end of a stream.
///
/// NDJSON wire DTOs are intentionally Serialize-only; see
/// [`NdjsonFunctionRecord`].
#[derive(Debug, Clone, Serialize)]
pub struct NdjsonFooter {
    /// Always "footer".
    pub record_type: String,
    /// Versioned stream schema; must match the header.
    pub schema: String,
    /// Crate-level summary.
    pub summary: CrateSummary,
    /// Number of ordered function records actually emitted.
    pub functions_emitted: usize,
    /// Domain-separated SHA-256 over the exact ordered function-record bytes.
    pub function_records_sha256: String,
    /// Domain-separated SHA-256 over the exact compact canonical
    /// `JsonProofReport` serialization.
    pub canonical_report_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct ProvedProperty {
    pub description: String,
    pub solver: String,
    pub time_ms: u64,
    pub strength: ProofStrength,
    /// Proof evidence derived from `strength`.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<ProofEvidence>,
}

#[derive(Deserialize)]
struct ProvedPropertyWire {
    description: String,
    solver: String,
    time_ms: u64,
    strength: ProofStrength,
    #[serde(default)]
    evidence: Option<ProofEvidence>,
}

impl ProvedPropertyWire {
    fn into_untrusted_unknown(self) -> UnknownProperty {
        let _diagnostic_only = (self.time_ms, self.strength, self.evidence);
        UnknownProperty {
            description: self.description,
            solver: self.solver,
            reason: LEGACY_DESERIALIZED_PROVED_DOWNGRADE_REASON.to_string(),
        }
    }
}

const LEGACY_DESERIALIZED_PROVED_DOWNGRADE_REASON: &str = "deserialized legacy proved property has no live verifier replay capability; serialized proof evidence is diagnostic-only and cannot carry proof authority";

impl<'de> Deserialize<'de> for ProvedProperty {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let _ = ProvedPropertyWire::deserialize(deserializer)?;
        Err(de::Error::custom(
            "a standalone serialized ProvedProperty cannot carry live proof authority",
        ))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailedProperty {
    pub description: String,
    pub solver: String,
    pub counterexample: Option<Counterexample>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnknownProperty {
    pub description: String,
    pub solver: String,
    pub reason: String,
}

/// Full verification report for a crate (legacy format, still used by build_report).
#[derive(Debug, Clone, Serialize)]
pub struct ProofReport {
    pub crate_name: String,
    pub functions: Vec<FunctionReport>,
    pub total_proved: usize,
    pub total_failed: usize,
    pub total_unknown: usize,
}

#[derive(Deserialize)]
struct FunctionReportWire {
    function: String,
    proved: Vec<ProvedPropertyWire>,
    failed: Vec<FailedProperty>,
    unknown: Vec<UnknownProperty>,
}

impl FunctionReportWire {
    fn into_public_fail_closed(self) -> (FunctionReport, usize) {
        let claimed_proved = self.proved.len();
        let mut unknown = self.unknown;
        unknown.extend(self.proved.into_iter().map(ProvedPropertyWire::into_untrusted_unknown));
        (
            FunctionReport {
                function: self.function,
                proved: Vec::new(),
                failed: self.failed,
                unknown,
            },
            claimed_proved,
        )
    }
}

impl<'de> Deserialize<'de> for FunctionReport {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(FunctionReportWire::deserialize(deserializer)?.into_public_fail_closed().0)
    }
}

#[derive(Deserialize)]
struct ProofReportWire {
    crate_name: String,
    functions: Vec<FunctionReportWire>,
    total_proved: usize,
    total_failed: usize,
    total_unknown: usize,
}

impl<'de> Deserialize<'de> for ProofReport {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofReportWire::deserialize(deserializer)?;
        let mut claimed_function_proved = 0usize;
        let mut functions = Vec::with_capacity(wire.functions.len());
        for function in wire.functions {
            let (function, claimed_proved) = function.into_public_fail_closed();
            claimed_function_proved = claimed_function_proved.saturating_add(claimed_proved);
            functions.push(function);
        }
        let function_failed = functions
            .iter()
            .fold(0usize, |count, function| count.saturating_add(function.failed.len()));
        let function_preexisting_unknown = functions
            .iter()
            .fold(0usize, |count, function| count.saturating_add(function.unknown.len()));
        let function_original_unknown =
            function_preexisting_unknown.saturating_sub(claimed_function_proved);
        let residual_failed = wire.total_failed.saturating_sub(function_failed);
        let residual_unknown = wire.total_unknown.saturating_sub(function_original_unknown);
        let residual_proved = wire.total_proved.saturating_sub(claimed_function_proved);

        Ok(Self {
            crate_name: wire.crate_name,
            functions,
            total_proved: 0,
            total_failed: function_failed.saturating_add(residual_failed),
            total_unknown: function_preexisting_unknown
                .saturating_add(residual_unknown)
                .saturating_add(residual_proved),
        })
    }
}

// ---------------------------------------------------------------------------
// Trust: Whole-crate verification result
// ---------------------------------------------------------------------------

/// Per-function verification result collected during whole-crate verification.
///
/// Pairs a function's identity with its raw verification (VC, result) pairs
/// and cross-function spec composition metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionVerificationResult {
    /// Fully qualified function path (e.g., "crate::module::function").
    pub function_path: String,
    /// Human-readable function name.
    pub function_name: String,
    /// Raw (VC, result) pairs from the solver.
    pub results: Vec<(VerificationCondition, VerificationResult)>,
    /// Number of VCs satisfied from cross-function spec notes (free).
    pub from_notes: usize,
    /// Number of VCs sent to solver with callee postcondition assumptions.
    pub with_assumptions: usize,
}

/// Aggregated verification result for an entire crate.
///
/// Collects per-function results and provides crate-level summary statistics.
/// Built incrementally as the trust_verify MIR pass processes each function,
/// then finalized into a `JsonProofReport` via trust-report.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CrateVerificationResult {
    /// Crate name.
    pub crate_name: String,
    /// Per-function verification results, in processing order.
    pub functions: Vec<FunctionVerificationResult>,
    /// Total VCs satisfied from cross-function spec notes across all functions.
    pub total_from_notes: usize,
    /// Total VCs sent to solver with callee assumptions across all functions.
    pub total_with_assumptions: usize,
}

impl CrateVerificationResult {
    /// Create a new empty result for the given crate.
    #[must_use]
    pub fn new(crate_name: impl Into<String>) -> Self {
        Self { crate_name: crate_name.into(), ..Default::default() }
    }

    /// Add a function's verification result.
    pub fn add_function(&mut self, func: FunctionVerificationResult) {
        self.total_from_notes += func.from_notes;
        self.total_with_assumptions += func.with_assumptions;
        self.functions.push(func);
    }

    /// Total number of functions verified.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Flatten all per-function (VC, result) pairs into a single list.
    ///
    /// This is the format expected by `trust_report::build_json_report()`.
    #[must_use]
    pub fn all_results(&self) -> Vec<(VerificationCondition, VerificationResult)> {
        self.functions.iter().flat_map(|f| f.results.clone()).collect()
    }

    /// Total number of VCs across all functions.
    #[must_use]
    pub fn total_obligations(&self) -> usize {
        self.functions.iter().map(|f| f.results.len()).sum()
    }
}

// ---------------------------------------------------------------------------
// Structured data transport (compiler -> driver -> CLI)
// ---------------------------------------------------------------------------

/// Prefix used to identify structured JSON transport lines in stderr.
///
/// The compiler emits `TRUST_JSON:{json}\n` lines to stderr alongside normal
/// diagnostics. Consumers scan for this prefix to extract structured data.
pub const TRANSPORT_PREFIX: &str = "TRUST_JSON:";

/// Rust diagnostic code attached by trustc to proof transport notes. Cargo's
/// compiler-message envelope alone is insufficient authentication: source and
/// procedural macros can emit arbitrary diagnostic text. Targo therefore
/// requires this compiler-owned, registered-in-process tag as well as the
/// package/target envelope and terminal inventory.
pub const TRANSPORT_DIAGNOSTIC_CODE: &str = "trust_verification_transport_v1";

/// A structured transport message emitted by the compiler MIR pass.
///
/// Each message is serialized as a single JSON line prefixed with
/// [`TRANSPORT_PREFIX`] on stderr. Consumers parse these lines to get
/// structured verification results without fragile text parsing.
/// Deserialization is intentionally available only through
/// [`parse_transport_payload`], which avoids serde's 128-bit-unsafe buffering
/// for internally tagged enums.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
#[non_exhaustive]
pub enum TransportMessage {
    /// Per-function verification results.
    #[serde(rename = "function_result")]
    FunctionResult(FunctionTransportResult),
    /// Crate-level summary emitted after all functions are processed.
    #[serde(rename = "crate_summary")]
    CrateSummary(CrateTransportSummary),
    /// Trust (assertion-grade coverage, roadmap §4.1): crate-level
    /// verification-coverage accounting, emitted exactly once at the end of the
    /// compiler's eager whole-crate walk. A consumer MUST treat
    /// `processed != eligible` as fail-closed (the verification report does not
    /// cover the whole crate — never a passing gate); absence of this row (an
    /// older compiler) is coverage-UNKNOWN, reported but not gate-driving.
    #[serde(rename = "coverage_summary")]
    CoverageSummary(CoverageTransportSummary),
}

/// Structured verification results for a single function, emitted by the
/// compiler MIR pass for consumption by targo-trust.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionTransportResult {
    /// Fully qualified function path (e.g., "crate::module::function").
    pub function: String,
    /// Cargo package and rustc target identities for coverage accounting.
    /// Older producers omit these fields and therefore cannot satisfy a
    /// proof-grade multi-package coverage gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub package_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub crate_name: Option<String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub primary_package: bool,
    /// Exact frontend-generated verification-session nonce for this compiler
    /// invocation. Cargo proof consumers must require it to match the nonce in
    /// the authenticated rustflags; an omitted legacy value cannot earn proof
    /// credit.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub verification_session: String,
    /// Per-obligation (VC, result) pairs.
    pub results: Vec<TransportObligationResult>,
    /// Summary counts for this function.
    pub proved: usize,
    pub failed: usize,
    /// Legacy-compatible aggregate of unknown, timed-out, and skipped outcomes.
    pub unknown: usize,
    #[serde(default)]
    pub timed_out: usize,
    #[serde(default)]
    pub skipped: usize,
    pub runtime_checked: usize,
    /// Trust (verify-cache): obligations replayed from the persistent proof
    /// cache — proved earlier on byte-identical inputs (sound-key hit) and
    /// unchanged since, so re-verification was skipped this run. Sourced from
    /// the authoritative `TrustFunctionSummary::cached`; the per-obligation
    /// `results` rows above stay conservatively `unknown` (non-evidentiary
    /// cross-boundary fail-safe), so this field is the machine-readable signal
    /// for cache replays (e.g. for `targo trust` hit-rate aggregation).
    /// `#[serde(default)]` keeps older JSON (without this field) deserializable.
    #[serde(default)]
    pub cached: usize,
    pub total: usize,
}

/// A single obligation result in the transport format.
///
/// Carries the essential fields from `VerificationResult` in a flat,
/// JSON-friendly structure without requiring the full `VerificationCondition`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransportObligationResult {
    /// Stable router/native obligation ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_id: Option<String>,
    /// SHA-256 digest of the exact canonical verification claim (VC), when the
    /// live compiler transport can provide it.
    ///
    /// This is diagnostic identity and correlation data only. A digest is
    /// self-asserted serialized data and is NEVER standalone proof authority;
    /// proof credit still requires a private live verifier capability bound to
    /// this exact claim.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim_digest_sha256: Option<String>,
    /// Short tag for the VC kind (e.g., "overflow:add", "divzero", "bounds").
    pub kind: String,
    /// Exact typed VC kind when the producer has the original
    /// [`VerificationCondition`](crate::VerificationCondition).
    ///
    /// `kind` remains the compact, backward-compatible diagnostic tag.  It is
    /// intentionally lossy for parameterized families (operand types,
    /// temporal machines, liveness/fairness payloads, and similar fields), so
    /// consumers must prefer this field whenever present.  The payload is
    /// classification/diagnostic data only and never proof authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub typed_kind: Option<Box<VcKind>>,
    /// Human-readable description of the obligation.
    pub description: String,
    /// Source location for the obligation, when available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Verification outcome.
    ///
    /// This is the field the whole compiler→targo protocol turns on, so it
    /// carries the shared [`Outcome`] vocabulary rather than a free string:
    /// producer and consumer are held to the same alphabet by the type checker,
    /// and a spelling neither side agreed on can no longer slip through as a
    /// silently reclassified row. `skipped` in particular is an unverified
    /// assumption or capability gap — counted as unknown+skipped, never as
    /// proof.
    pub outcome: Outcome,
    /// Which solver produced this result.
    pub solver: String,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// Optional counterexample for failed obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<String>,
    /// Structured counterexample model for repair tooling and reports.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_model: Option<Counterexample>,
    /// Optional reason for unknown/timeout results.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// Compiler-provided design-mandate bit: `true` iff the compiler knows this
    /// obligation is a hardened DESIGN MANDATE — a hardened-category VC whose
    /// violation formula is the tautology `true` (e.g. "[unsafe] missing SAFETY
    /// comment", raw-API migration mandates). Such a row is by construction not
    /// a discharge target (a tautological violation can never be proved UNSAT),
    /// so report consumers may exclude it from proof-evidence denominators while
    /// keeping it as inventory. Only the compiler sees the VC formula, so only
    /// the compiler may set this; consumers must never infer it from row text.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub design_mandate: bool,
    /// Native TrustIr evidence associated with this obligation, when the backend
    /// transported the native representation instead of only a flattened VC.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_trust_ir: Option<TransportNativeTrustIrEvidence>,
    /// Structured proof evidence associated with this obligation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_evidence: Option<TransportProofEvidence>,
    /// Kernel-certified runtime-monitor status for this exact
    /// contract-derived obligation, when applicable. An `unmonitored` record
    /// is explicit evidence that no runtime decision procedure exists; it
    /// must never be interpreted as a successful check.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub monitor: Option<TransportMonitorEvidence>,
}

/// Machine-stable runtime executability status for one contract clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TransportMonitorStatus {
    /// A runtime decision procedure was accepted only after the Clean kernel
    /// checked its equivalence certificate against the proposition.
    Monitored,
    /// An E5 scalar evaluator was accepted only after the Clean kernel checked
    /// its exact typed binding. Authenticated test artifacts combine it with
    /// compiler-owned entry/transition provenance to check strict descent.
    Measured,
    /// No certified runtime decision procedure exists for this proposition.
    Unmonitored,
}

impl TransportMonitorStatus {
    /// Lossless mapping from the compiler transport status to the §7
    /// executability grade axis.  This does not grant runtime execution
    /// authority: it only reports whether the exact proposition has a
    /// certified monitor.
    #[must_use]
    pub const fn executability(self) -> crate::grade::Executability {
        match self {
            Self::Monitored => crate::grade::Executability::Monitored,
            Self::Measured => crate::grade::Executability::Measured,
            Self::Unmonitored => crate::grade::Executability::Unmonitored,
        }
    }
}

/// Durable compiler evidence describing whether one proposition has a
/// kernel-certified runtime monitor.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportMonitorEvidence {
    /// Typed runtime disposition; `Monitored` and `Measured` permit only their
    /// respective authenticated runtime lanes.
    pub status: TransportMonitorStatus,
    /// Bounded compiler explanation of the disposition.
    pub reason: String,
    /// Digest of the compiler-native predicate identity consumed by monitor
    /// certification, encoded as `sha256:<64 lowercase hex digits>`.
    pub predicate_digest: String,
}

/// Native TrustIr evidence preserved in compiler transport.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportNativeTrustIrEvidence {
    /// Verification suite or integration family (for example "trust-mc", "trust-wp", "trust-vc").
    pub suite: String,
    /// Backend instance that produced or consumed the native TrustIr.
    pub backend: String,
    /// Backend request/correlation ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub request_id: Option<String>,
    /// Backend-native TrustIr/module/function ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_id: Option<String>,
    /// Whether native TrustIr was available for this obligation.
    pub present: bool,
    /// Native artifacts such as module snapshots, normalized IR, or sidecar metadata.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_transport_evidence_artifacts"
    )]
    pub artifacts: Vec<TransportEvidenceArtifact>,
    /// Diagnostics explaining missing or unsupported native evidence.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<TransportEvidenceDiagnostic>,
}

/// Structured proof evidence preserved in compiler transport.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportProofEvidence {
    /// Verification suite or integration family (for example "trust-mc", "trust-wp", "trust-vc").
    pub suite: String,
    /// Backend instance that produced the proof evidence.
    pub backend: String,
    /// Backend request/correlation ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub request_id: Option<String>,
    /// Backend proof/certificate/run ID, or the exact content-addressed
    /// certificate identity for an identity-bound kernel proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_id: Option<String>,
    /// Backend-native obligation or IR ID, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_id: Option<String>,
    /// Machine-stable proof status.
    pub status: TransportProofStatus,
    /// Legacy proof-strength model, when the backend can provide one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub strength: Option<ProofStrength>,
    /// Normalized proof-evidence model, when the backend can provide one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub evidence: Option<ProofEvidence>,
    /// Proof artifacts such as certificates, traces, replay logs, or solver transcripts.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_transport_evidence_artifacts"
    )]
    pub artifacts: Vec<TransportEvidenceArtifact>,
    /// Diagnostics explaining unsupported, partial, or rejected evidence.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<TransportEvidenceDiagnostic>,
}

/// Machine-stable proof evidence status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TransportProofStatus {
    Proved,
    Failed,
    Unknown,
    Timeout,
    Unsupported,
    Rejected,
}

impl From<TransportProofStatus> for Outcome {
    /// An evidence status is a strict subset of the shared vocabulary, so this
    /// direction is total and loses nothing.
    fn from(status: TransportProofStatus) -> Self {
        match status {
            TransportProofStatus::Proved => Self::Proved,
            TransportProofStatus::Failed => Self::Failed,
            TransportProofStatus::Unknown => Self::Unknown,
            TransportProofStatus::Timeout => Self::Timeout,
            TransportProofStatus::Unsupported => Self::Unsupported,
            TransportProofStatus::Rejected => Self::Rejected,
        }
    }
}

impl From<Outcome> for TransportProofStatus {
    /// Narrow an obligation outcome to what a *proof evidence record* can say.
    ///
    /// Evidence describes an attempt to discharge a claim, so the three
    /// outcomes that describe the absence of such an attempt have no faithful
    /// image here and must not borrow a favorable one: a runtime check is
    /// execution evidence rather than proof, an admitted assumption was never
    /// dispatched, and a cancellation produced nothing. All three narrow to
    /// `Unknown` — the status that grants no proof credit — rather than to
    /// `Proved` or to `Unsupported`, which would assert a capability verdict
    /// nobody reached.
    fn from(outcome: Outcome) -> Self {
        match outcome {
            Outcome::Proved => Self::Proved,
            Outcome::Failed => Self::Failed,
            Outcome::Timeout => Self::Timeout,
            Outcome::Unsupported => Self::Unsupported,
            Outcome::Rejected => Self::Rejected,
            Outcome::Unknown
            | Outcome::RuntimeChecked
            | Outcome::Skipped
            | Outcome::Canceled => Self::Unknown,
        }
    }
}

/// External or embedded evidence artifact carried by transport.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportEvidenceArtifact {
    /// Artifact role (for example "certificate", "proof_trace", "native_trust_ir").
    pub kind: String,
    /// Artifact encoding or format (for example "lfsc", "json", "trust_ir-json").
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub format: Option<String>,
    /// Backend artifact ID, when distinct from request/proof/native IDs.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_id: Option<String>,
    /// Content digest for integrity checks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digest: Option<TransportArtifactDigest>,
    /// URI for external artifact storage.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub uri: Option<String>,
    /// Exact artifact bytes and producer-authored proof-set relationships.
    /// The payload is hex encoded so consumers can validate `byte_len` and the
    /// hard size cap before allocating or decoding it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub materialization: Option<TransportArtifactMaterialization>,
    /// Inline structured metadata. This is intentionally typed JSON rather than
    /// a string so native backends can carry small backend-specific facts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<serde_json::Value>,
}

/// Maximum number of evidence artifacts accepted for one native or proof
/// record. Publication-grade routes use only a small fixed DAG; this generous
/// ceiling preserves supplemental diagnostics while bounding deserialization
/// memory and topology-validation work for untrusted saved reports.
pub const MAX_TRANSPORT_EVIDENCE_ARTIFACTS: usize = 256;

/// Maximum decoded byte length accepted for an inline proof artifact.
pub const MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES: usize = 16 * 1024 * 1024;

/// Fixed directory, relative to an explicitly trusted report/output root, for
/// content-addressed path-backed proof materializations.
pub const TRANSPORT_ARTIFACT_STORE_DIRECTORY: &str = ".trust-proof-artifacts";

/// Canonical envelope schema for SHA-addressed native TrustIr structural
/// materializations.
pub const NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA: &str = "trust.native-trust-ir-materialization.v1";

/// Canonically encoded exact bytes and producer-authored cross-artifact
/// bindings for one evidence artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportArtifactMaterialization {
    /// Encoding of `encoded_bytes`; currently only canonical lowercase hex.
    pub encoding: String,
    /// Declared decoded length. Consumers check this and the size cap before
    /// decoding `encoded_bytes`.
    pub byte_len: u64,
    /// Canonical lowercase hexadecimal payload.
    #[serde(deserialize_with = "deserialize_bounded_materialization_hex")]
    pub encoded_bytes: String,
    /// Optional content-addressed file-store path. Exactly one of this path or
    /// non-empty `encoded_bytes` may carry the payload.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "deserialize_bounded_materialization_path"
    )]
    pub materialized_path: Option<String>,
    /// Stable proof-set identity supplied by the artifact producer.
    pub proof_binding_id: String,
    /// Producer-authored ordered sequence of materialized artifacts explicitly
    /// checked/incorporated by this artifact. Topology membership is compared
    /// as a set, while the bound payload envelope authenticates this exact
    /// sequence. Consumers must therefore preserve, not canonicalize, order.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_materialization_references"
    )]
    pub referenced_artifacts: Vec<TransportArtifactReference>,
}

/// Typed relationship to another materialized transport artifact.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TransportArtifactReference {
    pub kind: String,
    pub digest: TransportArtifactDigest,
}

const MAX_TRANSPORT_ARTIFACT_REFERENCES: usize = 32;

fn transport_artifact_references_are_valid(references: &[TransportArtifactReference]) -> bool {
    if references.len() > MAX_TRANSPORT_ARTIFACT_REFERENCES {
        return false;
    }
    let mut seen = BTreeSet::new();
    references.iter().all(|reference| {
        canonical_transport_artifact_role(&reference.kind)
            && is_canonical_sha256_digest(&reference.digest)
            && seen.insert(reference)
    })
}

impl TransportArtifactMaterialization {
    /// Encode an exact, bounded, non-empty artifact payload for transport.
    #[must_use]
    pub fn from_exact_bytes(
        bytes: &[u8],
        proof_binding_id: impl Into<String>,
        referenced_artifacts: Vec<TransportArtifactReference>,
    ) -> Option<Self> {
        let proof_binding_id = proof_binding_id.into();
        if bytes.is_empty()
            || bytes.len() > MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES
            || !canonical_transport_proof_binding_id(&proof_binding_id)
            || !transport_artifact_references_are_valid(&referenced_artifacts)
        {
            return None;
        }
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut encoded_bytes = String::with_capacity(bytes.len().saturating_mul(2));
        for byte in bytes {
            encoded_bytes.push(HEX[(byte >> 4) as usize] as char);
            encoded_bytes.push(HEX[(byte & 0x0f) as usize] as char);
        }
        Some(Self {
            encoding: "hex".to_string(),
            byte_len: bytes.len() as u64,
            encoded_bytes,
            materialized_path: None,
            proof_binding_id,
            referenced_artifacts,
        })
    }

    /// Decode an inline exact payload after checking encoding, declared
    /// length, canonical form, non-emptiness, and the hard size cap.
    ///
    /// Path-backed payloads deliberately fail closed here. Opening a path from
    /// deserialized transport without an explicitly trusted root would make
    /// generic report validation a confused deputy. Use
    /// [`Self::decoded_bytes_at_root`] when the caller owns such a root.
    pub fn decoded_bytes(&self) -> Result<Vec<u8>, String> {
        let byte_len = self.validate_shape()?;
        if self.materialized_path.is_some() {
            return Err("path-backed artifact materialization requires an explicit trusted root"
                .to_string());
        }
        decode_inline_materialization(&self.encoded_bytes, byte_len)
    }

    /// Decode exact path-backed bytes relative to a canonical trusted root.
    ///
    /// Only `.trust-proof-artifacts/sha256/<declared digest>` is accepted. The
    /// store directories and leaf must not be symlinks, and the leaf identity,
    /// type, and length must remain unchanged across the bounded read.
    pub fn decoded_bytes_at_root(
        &self,
        digest: &TransportArtifactDigest,
        trusted_root: &Path,
    ) -> Result<Vec<u8>, String> {
        if !is_canonical_sha256_digest(digest) {
            return Err("artifact digest is not canonical SHA-256".to_string());
        }
        let byte_len = self.validate_shape()?;
        let Some(relative_path) = self.materialized_path.as_deref() else {
            let bytes = decode_inline_materialization(&self.encoded_bytes, byte_len)?;
            return (lowercase_transport_hex(&Sha256::digest(&bytes)) == digest.value)
                .then_some(bytes)
                .ok_or_else(|| "inline artifact bytes do not match declared digest".to_string());
        };
        validate_materialized_relative_path(relative_path, Some(&digest.value))?;
        securely_read_materialized_path(trusted_root, relative_path, byte_len, &digest.value)
    }

    /// Whether inline exact bytes match a canonical SHA-256 declaration.
    /// Path-backed payloads receive no generic credit; callers with an
    /// explicit root use [`Self::matches_sha256_digest_at_root`].
    #[must_use]
    pub fn matches_sha256_digest(&self, digest: &TransportArtifactDigest) -> bool {
        if !is_canonical_sha256_digest(digest) {
            return false;
        }
        if self.validate_shape().is_err() {
            return false;
        }
        if self.materialized_path.is_some() {
            return false;
        }
        let mut hasher = Sha256::new();
        for pair in self.encoded_bytes.as_bytes().chunks_exact(2) {
            let Some(high) = canonical_hex_nibble(pair[0]) else { return false };
            let Some(low) = canonical_hex_nibble(pair[1]) else { return false };
            hasher.update([(high << 4) | low]);
        }
        let actual = hasher.finalize();
        lowercase_transport_hex(&actual) == digest.value
    }

    /// Whether exact bytes match SHA-256 when any path is resolved under the
    /// caller's explicit trusted report/output root.
    #[must_use]
    pub fn matches_sha256_digest_at_root(
        &self,
        digest: &TransportArtifactDigest,
        trusted_root: &Path,
    ) -> bool {
        if self.materialized_path.is_none() {
            return self.matches_sha256_digest(digest);
        }
        self.decoded_bytes_at_root(digest, trusted_root).is_ok()
    }

    /// Replace inline encoding with a content-addressed materialization file.
    #[must_use]
    pub fn with_materialized_path(mut self, path: impl Into<String>) -> Option<Self> {
        let path = path.into();
        if validate_materialized_relative_path(&path, None).is_err() {
            return None;
        }
        self.encoded_bytes.clear();
        self.materialized_path = Some(path);
        self.validate_shape().ok()?;
        Some(self)
    }

    fn validate_shape(&self) -> Result<usize, String> {
        if self.encoding != "hex" {
            return Err("artifact materialization encoding is not canonical `hex`".to_string());
        }
        let byte_len = usize::try_from(self.byte_len)
            .map_err(|_| "artifact materialization byte_len does not fit usize".to_string())?;
        if byte_len == 0 {
            return Err("artifact materialization is empty".to_string());
        }
        if byte_len > MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES {
            return Err(format!(
                "artifact materialization exceeds {} byte limit",
                MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES
            ));
        }
        if let Some(path) = &self.materialized_path {
            if !self.encoded_bytes.is_empty() {
                return Err(
                    "artifact materialization cannot carry both inline bytes and a file path"
                        .to_string(),
                );
            }
            validate_materialized_relative_path(path, None)?;
        } else {
            let encoded_len = byte_len
                .checked_mul(2)
                .ok_or_else(|| "artifact materialization encoded length overflow".to_string())?;
            if self.encoded_bytes.len() != encoded_len {
                return Err(
                    "artifact materialization byte_len does not match encoded payload".to_string()
                );
            }
        }
        if !canonical_transport_proof_binding_id(&self.proof_binding_id) {
            return Err("artifact materialization proof_binding_id is empty".to_string());
        }
        if !transport_artifact_references_are_valid(&self.referenced_artifacts) {
            return Err(
                "artifact materialization references are not canonical duplicate-free SHA-256"
                    .to_string(),
            );
        }
        Ok(byte_len)
    }
}

fn decode_inline_materialization(encoded: &str, byte_len: usize) -> Result<Vec<u8>, String> {
    let mut decoded = Vec::with_capacity(byte_len);
    for pair in encoded.as_bytes().chunks_exact(2) {
        let high = canonical_hex_nibble(pair[0]).ok_or_else(|| {
            "artifact materialization payload is not canonical lowercase hex".to_string()
        })?;
        let low = canonical_hex_nibble(pair[1]).ok_or_else(|| {
            "artifact materialization payload is not canonical lowercase hex".to_string()
        })?;
        decoded.push((high << 4) | low);
    }
    Ok(decoded)
}

fn validate_materialized_relative_path(
    path: &str,
    expected_digest: Option<&str>,
) -> Result<(), String> {
    if path.is_empty() || path.len() > 4096 || path.contains('\0') {
        return Err("artifact materialization file path is invalid".to_string());
    }
    let components = Path::new(path).components().collect::<Vec<_>>();
    let [Component::Normal(store), Component::Normal(algorithm), Component::Normal(digest)] =
        components.as_slice()
    else {
        return Err(
            "artifact materialization path must be a canonical relative content-addressed store path"
                .to_string(),
        );
    };
    if *store != std::ffi::OsStr::new(TRANSPORT_ARTIFACT_STORE_DIRECTORY)
        || *algorithm != std::ffi::OsStr::new("sha256")
    {
        return Err(
            "artifact materialization path is outside the fixed SHA-256 proof store".to_string()
        );
    }
    let digest =
        digest.to_str().filter(|value| canonical_sha256_value(value)).ok_or_else(|| {
            "artifact materialization path does not end in canonical SHA-256".to_string()
        })?;
    if expected_digest.is_some_and(|expected| digest != expected) {
        return Err(
            "artifact materialization path digest does not match the declared digest".to_string()
        );
    }
    Ok(())
}

fn canonical_sha256_value(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn securely_read_materialized_path(
    trusted_root: &Path,
    relative_path: &str,
    byte_len: usize,
    expected_digest: &str,
) -> Result<Vec<u8>, String> {
    let root_metadata = std::fs::symlink_metadata(trusted_root).map_err(|error| {
        format!("could not inspect trusted artifact materialization root: {error}")
    })?;
    if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
        return Err(
            "trusted artifact materialization root is not a non-symlink directory".to_string()
        );
    }
    let canonical_root = std::fs::canonicalize(trusted_root).map_err(|error| {
        format!("could not canonicalize trusted artifact materialization root: {error}")
    })?;
    if !trusted_root.is_absolute() || canonical_root != trusted_root {
        return Err("artifact materialization root is not an explicit canonical path".to_string());
    }

    let store = canonical_root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY);
    let algorithm_store = store.join("sha256");
    for directory in [&store, &algorithm_store] {
        let metadata = std::fs::symlink_metadata(directory).map_err(|error| {
            format!("could not inspect artifact materialization store directory: {error}")
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(
                "artifact materialization store contains a symlink or non-directory component"
                    .to_string(),
            );
        }
    }

    let candidate = canonical_root.join(relative_path);
    if candidate.parent() != Some(algorithm_store.as_path()) {
        return Err("artifact materialization path escaped the trusted store".to_string());
    }
    let entry_before = std::fs::symlink_metadata(&candidate)
        .map_err(|error| format!("could not inspect artifact materialization file: {error}"))?;
    if entry_before.file_type().is_symlink() || !entry_before.is_file() {
        return Err("artifact materialization path is not a non-symlink regular file".to_string());
    }
    if entry_before.len() != byte_len as u64 {
        return Err("artifact materialization file length does not match byte_len".to_string());
    }
    let canonical_candidate = std::fs::canonicalize(&candidate).map_err(|error| {
        format!("could not canonicalize artifact materialization file: {error}")
    })?;
    if canonical_candidate != candidate || !canonical_candidate.starts_with(&canonical_root) {
        return Err("artifact materialization path escaped the trusted store".to_string());
    }

    let mut file = std::fs::File::open(&candidate)
        .map_err(|error| format!("could not open artifact materialization file: {error}"))?;
    let opened_before = file
        .metadata()
        .map_err(|error| format!("could not inspect opened artifact materialization: {error}"))?;
    if !opened_before.is_file()
        || opened_before.len() != byte_len as u64
        || !same_file_identity(&entry_before, &opened_before)
    {
        return Err("artifact materialization file identity changed before reading".to_string());
    }

    let mut bytes = Vec::with_capacity(byte_len);
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("could not read artifact materialization file: {error}"))?;
        if read == 0 {
            break;
        }
        if bytes.len().saturating_add(read) > byte_len {
            return Err("artifact materialization file grew while reading".to_string());
        }
        hasher.update(&buffer[..read]);
        bytes.extend_from_slice(&buffer[..read]);
    }
    if bytes.len() != byte_len || lowercase_transport_hex(&hasher.finalize()) != expected_digest {
        return Err("artifact materialization bytes do not match length and digest".to_string());
    }

    let opened_after = file.metadata().map_err(|error| {
        format!("could not re-inspect opened artifact materialization: {error}")
    })?;
    let entry_after = std::fs::symlink_metadata(&candidate)
        .map_err(|error| format!("could not re-inspect artifact materialization path: {error}"))?;
    if entry_after.file_type().is_symlink()
        || !entry_after.is_file()
        || entry_after.len() != byte_len as u64
        || opened_after.len() != byte_len as u64
        || !same_file_identity(&entry_before, &opened_after)
        || !same_file_identity(&entry_before, &entry_after)
    {
        return Err("artifact materialization file identity changed while reading".to_string());
    }
    Ok(bytes)
}

#[cfg(unix)]
fn same_file_identity(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;
    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_file_identity(left: &std::fs::Metadata, right: &std::fs::Metadata) -> bool {
    left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
        && left.created().ok() == right.created().ok()
}

fn lowercase_transport_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn deserialize_bounded_materialization_hex<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedHexVisitor;

    impl<'de> Visitor<'de> for BoundedHexVisitor {
        type Value = String;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                formatter,
                "at most {} canonical hexadecimal characters",
                MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES * 2
            )
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            if value.len() > MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES * 2 {
                return Err(E::custom("artifact materialization encoded payload exceeds limit"));
            }
            Ok(value.to_string())
        }

        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            if value.len() > MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES * 2 {
                return Err(E::custom("artifact materialization encoded payload exceeds limit"));
            }
            Ok(value)
        }
    }

    deserializer.deserialize_string(BoundedHexVisitor)
}

fn deserialize_bounded_materialization_path<'de, D>(
    deserializer: D,
) -> Result<Option<String>, D::Error>
where
    D: Deserializer<'de>,
{
    let path = Option::<String>::deserialize(deserializer)?;
    if path.as_ref().is_some_and(|path| path.len() > 4096 || path.contains('\0')) {
        return Err(de::Error::custom("artifact materialization path exceeds limit"));
    }
    Ok(path)
}

fn deserialize_bounded_materialization_references<'de, D>(
    deserializer: D,
) -> Result<Vec<TransportArtifactReference>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedReferencesVisitor;

    impl<'de> Visitor<'de> for BoundedReferencesVisitor {
        type Value = Vec<TransportArtifactReference>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "at most {MAX_TRANSPORT_ARTIFACT_REFERENCES} artifact digests")
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut references = Vec::with_capacity(
                sequence.size_hint().unwrap_or(0).min(MAX_TRANSPORT_ARTIFACT_REFERENCES),
            );
            while let Some(reference) = sequence.next_element::<TransportArtifactReference>()? {
                if references.len() == MAX_TRANSPORT_ARTIFACT_REFERENCES {
                    return Err(de::Error::custom("too many artifact digest references"));
                }
                references.push(reference);
            }
            Ok(references)
        }
    }

    deserializer.deserialize_seq(BoundedReferencesVisitor)
}

fn deserialize_bounded_transport_evidence_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<TransportEvidenceArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedArtifactsVisitor;

    impl<'de> Visitor<'de> for BoundedArtifactsVisitor {
        type Value = Vec<TransportEvidenceArtifact>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                formatter,
                "at most {MAX_TRANSPORT_EVIDENCE_ARTIFACTS} transport evidence artifacts"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            if sequence.size_hint().is_some_and(|hint| hint > MAX_TRANSPORT_EVIDENCE_ARTIFACTS) {
                return Err(de::Error::custom("too many transport evidence artifacts"));
            }
            let mut artifacts = Vec::with_capacity(
                sequence.size_hint().unwrap_or(0).min(MAX_TRANSPORT_EVIDENCE_ARTIFACTS),
            );
            while artifacts.len() < MAX_TRANSPORT_EVIDENCE_ARTIFACTS {
                let Some(artifact) = sequence.next_element::<TransportEvidenceArtifact>()? else {
                    return Ok(artifacts);
                };
                artifacts.push(artifact);
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                return Err(de::Error::custom("too many transport evidence artifacts"));
            }
            Ok(artifacts)
        }
    }

    deserializer.deserialize_seq(BoundedArtifactsVisitor)
}

fn canonical_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn canonical_transport_proof_binding_id(value: &str) -> bool {
    const MAX_BINDING_ID_BYTES: usize = 256;
    !value.is_empty()
        && value.len() <= MAX_BINDING_ID_BYTES
        && value.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b':' | b'-'))
}

fn canonical_transport_artifact_role(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 64
        && value.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
}

/// Digest metadata for an evidence artifact.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TransportArtifactDigest {
    /// Digest algorithm, for example "sha256".
    pub algorithm: String,
    /// Hex/base64 digest value, as defined by `algorithm`.
    pub value: String,
}

/// Diagnostic attached to native/proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportEvidenceDiagnostic {
    /// Machine-stable diagnostic code.
    pub code: String,
    /// Diagnostic severity.
    pub severity: TransportEvidenceDiagnosticSeverity,
    /// Human-readable diagnostic message.
    pub message: String,
    /// Backend-specific detail that should not be used for stable matching.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

/// Severity for evidence diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TransportEvidenceDiagnosticSeverity {
    Info,
    Warning,
    Error,
}

/// Crate-level summary emitted after all functions are processed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrateTransportSummary {
    /// Crate name.
    pub crate_name: String,
    /// Cargo package identity and primary-package bit for exact coverage.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub package_name: Option<String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub primary_package: bool,
    /// Exact frontend-generated verification-session nonce. This binds the
    /// terminal summary itself, rather than relying on a separate coverage row
    /// from the same Cargo target to imply freshness.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub verification_session: String,
    /// Total function-result records emitted, regardless of verdict.
    pub functions_analyzed: usize,
    /// Functions whose emitted obligation inventory was nonempty and entirely
    /// proved. Failed, unknown, skipped, timed-out, and runtime-checked rows do
    /// not count as verified.
    pub functions_verified: usize,
    /// Aggregate counts.
    pub total_proved: usize,
    pub total_failed: usize,
    /// Legacy-compatible aggregate of unknown, timed-out, and skipped outcomes.
    pub total_unknown: usize,
    #[serde(default)]
    pub total_timed_out: usize,
    #[serde(default)]
    pub total_skipped: usize,
    pub total_runtime_checked: usize,
    pub total_obligations: usize,
}

/// Trust (assertion-grade coverage, roadmap §4.1): crate-level verification-
/// coverage accounting on the wire. Emitted once by the compiler after the
/// eager whole-crate walk (`trust_ensure_whole_crate_verification`) as a
/// `TRUST_JSON:{"type":"coverage_summary",...}` line. `eligible` counts the
/// local `mir_keys` bodies the walk demanded (fn / assoc fn / closure, runtime
/// or const-fn); `processed` counts how many of those reached an attributable
/// per-body outcome (the `TrustVerify` pass ran, or the body legitimately
/// early-outed: tainted-by-errors — the build already fails — or a lone
/// `unreachable` body with no executable path). `processed != eligible` means
/// the accounting is incomplete or malformed: fail-closed, never a passing
/// gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageTransportSummary {
    /// Crate name.
    pub crate_name: String,
    /// Exact Cargo package identity. Empty only when deserializing an older
    /// producer or compiling outside an authenticated Cargo package session.
    #[serde(default)]
    pub package_name: String,
    /// Whether Cargo authenticated this compilation unit as a primary package.
    #[serde(default)]
    pub primary_package: bool,
    /// Exact verification-session nonce injected by the authenticated frontend.
    /// Empty only for an older producer or an unscoped direct compiler run.
    #[serde(default)]
    pub verification_session: String,
    /// Eligible local function bodies (the eager whole-crate walk's selection).
    pub eligible: usize,
    /// Bodies that reached an attributable verification-pass outcome.
    pub processed: usize,
    /// Versioned exact function-identity inventory. Older count-only producers
    /// deserialize with `None`, but cannot satisfy a current strict coverage
    /// gate because equal cardinalities do not prove equal function sets.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_identities: Option<CoverageFunctionIdentityInventory>,
}

/// Schema for canonical exact function sets carried by
/// [`CoverageTransportSummary`]. Names are fully-qualified compiler def paths,
/// sorted strictly by their UTF-8 byte representation with no duplicates.
pub const COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1: &str = "trustc.coverage-function-identities.v1";

/// Exact eligible and processed function identities for one compiler unit.
///
/// This is accounting evidence, never proof authority. Consumers bind it to an
/// authenticated package/crate/target/session envelope and require exact set
/// equality with that unit's authenticated [`FunctionTransportResult`] rows.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageFunctionIdentityInventory {
    /// Exact schema/domain version for canonical ordering and set semantics.
    pub schema: String,
    /// Every function in the compiler unit's verification universe.
    pub eligible_functions: Vec<String>,
    /// Every eligible function that reached an attributable outcome.
    pub processed_functions: Vec<String>,
}

impl CoverageTransportSummary {
    /// `true` iff every eligible body reached an attributable outcome.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.processed == self.eligible
    }

    /// Number of eligible bodies that were never verified. This is zero for
    /// exact coverage and for malformed over-counts; callers must use
    /// [`Self::is_complete`] for the authoritative equality check.
    #[must_use]
    pub fn shortfall(&self) -> usize {
        self.eligible.saturating_sub(self.processed)
    }
}

/// Parse an unprefixed JSON payload into a [`TransportMessage`].
///
/// Trust (R1 corpus, transport-parse cascade): dispatch on the `"type"` tag
/// MANUALLY and deserialize the variant struct DIRECTLY from the original JSON
/// instead of using the derived internally-tagged (`#[serde(tag = "type")]`)
/// `Deserialize`. The derived impl buffers the payload through serde's private
/// `Content` representation, which does not support 128-bit integers — so any
/// function line containing a `counterexample_model` (whose
/// `CounterexampleValue::Int(i128)`/`Uint(u128)` arms drive a
/// `deserialize_i128` call) failed canonical parsing wholesale with
/// "i128 is not supported". Consumers then fell back to lossy row recovery,
/// which soundly DOWNGRADES every `proved` row in that function to Unknown —
/// on the first real-crate corpus sweep this single defect hid 279 of itoa's
/// 300 compiler-proved obligations (reported 2.5% proved vs the real 35%).
/// Direct struct deserialization never round-trips through `Content`, so the
/// same line parses with full fidelity; the extra `"type"` key is ignored by
/// serde's default unknown-field handling. Serialization is unchanged (same
/// tagged schema on the wire).
pub fn parse_transport_payload(payload: &str) -> Result<TransportMessage, serde_json::Error> {
    #[derive(Deserialize)]
    struct TransportMessageTag {
        r#type: String,
    }

    let tag: TransportMessageTag = serde_json::from_str(payload)?;
    match tag.r#type.as_str() {
        "function_result" => serde_json::from_str(payload).map(TransportMessage::FunctionResult),
        "crate_summary" => serde_json::from_str(payload).map(TransportMessage::CrateSummary),
        "coverage_summary" => serde_json::from_str(payload).map(TransportMessage::CoverageSummary),
        _ => Err(<serde_json::Error as de::Error>::custom(format!(
            "unknown Trust transport message type {:?}",
            tag.r#type
        ))),
    }
}

/// Parse a `TRUST_JSON:` prefixed line into a [`TransportMessage`].
///
/// Returns `None` if the line does not start with the transport prefix or if
/// [`parse_transport_payload`] rejects the JSON payload.
#[must_use]
pub fn parse_transport_line(line: &str) -> Option<TransportMessage> {
    parse_transport_payload(line.strip_prefix(TRANSPORT_PREFIX)?).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{StateMachineMetadata, VcKind};
    use crate::model::{BinOp, Ty};

    fn arithmetic_overflow_vc() -> VcKind {
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) }
    }

    // Trust (green front door, Stage 2): verification-gate serde tests.

    fn sample_gate() -> VerificationGateReport {
        VerificationGateReport {
            lane: "default".into(),
            verification_level: Some("L2".into()),
            decision: "conditional-pass".into(),
            exit_code: 0,
            counts: VerificationGateCounts {
                total: 3,
                proved: 1,
                failed: 0,
                unknown: 0,
                runtime_checked: 0,
                assumed: 1,
                mandated: 1,
                contract_panics: 0,
            },
            conditional_on_assumption_rows: true,
            conditional_on_dependency_entries: true,
            conditional_on_runtime_checks: false,
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
        }
    }

    fn minimal_gate_report(gate: Option<VerificationGateReport>) -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1".into(),
                trust_version: "t".into(),
                timestamp: "1970".into(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "c".into(),
            summary: CrateSummary {
                functions_analyzed: 0,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 0,
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: CrateVerdict::NoObligations,
            },
            functions: Vec::new(),
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: gate,
            cargo_proof_inventory: None,
        }
    }

    #[test]
    fn verification_gate_report_serde_round_trips() {
        let gate = sample_gate();
        let json = serde_json::to_string(&gate).expect("serialize gate");
        let back: VerificationGateReport = serde_json::from_str(&json).expect("deserialize gate");
        assert_eq!(gate, back);
    }

    #[test]
    fn json_proof_report_deserialization_downgrades_verification_gate_proof_credit() {
        let report = minimal_gate_report(Some(sample_gate()));
        let json = serde_json::to_string(&report).expect("serialize report");
        assert!(json.contains("verification_gate"), "gate must serialize when present");
        let back: JsonProofReport = serde_json::from_str(&json).expect("deserialize report");
        let gate = back.verification_gate.expect("gate remains diagnostic");
        assert_eq!(gate.decision, "inconclusive");
        assert_eq!(gate.exit_code, 1);
        assert_eq!(gate.counts.proved, 0);
        assert_eq!(gate.counts.unknown, 1);
        assert_eq!(gate.counts.assumed, 1);
        assert_eq!(gate.counts.mandated, 1);
    }

    fn cargo_report_unit(package_id: &str, index: u64, role: &str) -> CargoProofUnitReport {
        CargoProofUnitReport {
            package_id: package_id.to_string(),
            package_name: "shared-name".to_string(),
            target_name: "shared_target".to_string(),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            compile_target_spec_sha256: None,
            proof_unit_index: index,
            proof_unit_mode: "build".to_string(),
            proof_unit_role: role.to_string(),
            graph_role: if role == "excluded" { "dependency" } else { role }.to_string(),
            exclusion_reason: (role == "excluded")
                .then(|| "dependency-policy-excluded".to_string()),
            semantics_sha256: None,
            semantics: None,
        }
    }

    fn cargo_semantics_report() -> CargoUnitSemanticsReport {
        CargoUnitSemanticsReport {
            schema: "targo.trust-unit-semantics.v1".to_string(),
            features: vec!["default".to_string(), "serde".to_string()],
            target_cfg: vec!["target_arch = \"x86_64\"".to_string(), "unix".to_string()],
            cfg_test: false,
            target_edition: "2024".to_string(),
            target_crate_types: vec!["rlib".to_string()],
            target_harness: false,
            target_proc_macro: false,
            profile: CargoUnitProfileSemanticsReport {
                opt_level: "2".to_string(),
                requested_lto: "thin".to_string(),
                effective_lto: "run:thin".to_string(),
                codegen_backend: Some("trust-cg".to_string()),
                codegen_units: Some(1),
                debuginfo: "1".to_string(),
                split_debuginfo: Some("packed".to_string()),
                debug_assertions: false,
                overflow_checks: true,
                rpath: false,
                incremental: false,
                panic: "abort".to_string(),
                strip: "debuginfo".to_string(),
                rustflags: vec!["-Ctarget-cpu=x86-64-v3".to_string()],
                trim_paths: Some("all".to_string()),
                hint_mostly_unused: Some(false),
            },
            compiler: CargoUnitCompilerSemanticsReport {
                frontend: "rustc".to_string(),
                codegen_backend: "trust-cg".to_string(),
                rustc_release: "1.99.0-nightly".to_string(),
                rustc_commit_hash: Some("a".repeat(40)),
                rustc_host: "x86_64-unknown-linux-gnu".to_string(),
                rustc_verbose_version_sha256: "b".repeat(64),
            },
            unit_rustflags: vec!["-Zcodegen-backend=trust-cg".to_string()],
            manifest_lint_rustflags: vec!["-Dwarnings".to_string()],
            extra_compiler_args: vec!["--emit=metadata".to_string()],
        }
    }

    #[test]
    fn cargo_v2_unit_semantics_round_trip_as_a_closed_digest_bound_descriptor() {
        let semantics = cargo_semantics_report();
        let semantics_sha256 = format!(
            "{:x}",
            Sha256::digest(serde_json::to_vec(&semantics).expect("serialize semantics"))
        );
        let mut unit = cargo_report_unit("path+file:///workspace#root@0.1.0", 0, "primary");
        unit.semantics_sha256 = Some(semantics_sha256.clone());
        unit.semantics = Some(semantics.clone());

        let encoded = serde_json::to_value(&unit).expect("serialize v2 unit");
        assert_eq!(encoded["semantics_sha256"], semantics_sha256);
        assert_eq!(encoded["semantics"]["features"], serde_json::json!(["default", "serde"]));
        let decoded: CargoProofUnitReport =
            serde_json::from_value(encoded.clone()).expect("deserialize v2 unit");
        assert_eq!(decoded, unit);

        let mut extended = encoded;
        extended["semantics"]["compiler"]["unwired_future_field"] = serde_json::json!(true);
        let error = serde_json::from_value::<CargoProofUnitReport>(extended)
            .expect_err("semantic descriptor schema must reject unknown fields");
        assert!(error.to_string().contains("unknown field"), "{error}");
    }

    #[test]
    fn cargo_proof_inventory_saved_report_round_trips_exact_multi_version_identities() {
        let dependency_v1 = cargo_report_unit(
            "registry+https://example.invalid#index#shared-name@1.0.0",
            3,
            "dependency",
        );
        let dependency_v2 = cargo_report_unit(
            "registry+https://example.invalid#index#shared-name@2.0.0",
            4,
            "dependency",
        );
        let primary = cargo_report_unit("path+file:///workspace#root@0.1.0", 0, "primary");
        let test_execution =
            cargo_report_unit("path+file:///workspace#root@0.1.0", 1, "test-execution");
        let mut excluded = cargo_report_unit(
            "registry+https://example.invalid#index#excluded@1.0.0",
            2,
            "excluded",
        );
        excluded.proof_unit_mode = "doc".to_string();
        excluded.graph_role = "primary".to_string();
        excluded.exclusion_reason = Some("documentation-generation".to_string());
        let inventory = CargoProofInventoryReport {
            schema: CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1.to_string(),
            include_dependencies: true,
            declared: CargoProofUnitPartitions {
                primary_roots: vec![primary.clone()],
                test_execution_units: vec![test_execution.clone()],
                dependency_units: vec![dependency_v1.clone(), dependency_v2.clone()],
            },
            completed: CargoProofUnitPartitions {
                primary_roots: vec![primary],
                test_execution_units: vec![test_execution],
                dependency_units: vec![dependency_v1.clone(), dependency_v2.clone()],
            },
            covered: CargoProofUnitPartitions {
                primary_roots: Vec::new(),
                test_execution_units: Vec::new(),
                dependency_units: vec![dependency_v1.clone(), dependency_v2.clone()],
            },
            excluded_active_units: vec![excluded],
        };
        let mut report = minimal_gate_report(None);
        report.cargo_proof_inventory = Some(inventory.clone());

        let encoded = serde_json::to_vec(&report).expect("serialize report inventory");
        let encoded_value: serde_json::Value =
            serde_json::from_slice(&encoded).expect("inspect serialized inventory");
        assert_eq!(
            encoded_value["cargo_proof_inventory"]["schema"],
            CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1
        );
        assert_eq!(
            encoded_value["cargo_proof_inventory"]["covered"]["primary_roots"],
            serde_json::json!([])
        );
        assert_eq!(
            encoded_value["cargo_proof_inventory"]["covered"]["test_execution_units"],
            serde_json::json!([])
        );
        assert!(
            encoded_value["cargo_proof_inventory"]["declared"]["primary_roots"][0]
                .get("compile_target_spec_sha256")
                .is_some_and(serde_json::Value::is_null),
            "built-in compile targets retain an explicit null target-spec digest"
        );
        assert_eq!(
            encoded_value["cargo_proof_inventory"]["excluded_active_units"][0]["exclusion_reason"],
            "documentation-generation"
        );
        assert_eq!(
            encoded_value["cargo_proof_inventory"]["excluded_active_units"][0]["graph_role"],
            "primary"
        );
        let (decoded, sanitization, _) =
            JsonProofReport::decode_saved_json(&encoded, None).expect("decode saved report");
        assert_eq!(sanitization, SavedReportSanitization::default());
        assert_eq!(decoded.cargo_proof_inventory, Some(inventory));
        let dependencies = &decoded
            .cargo_proof_inventory
            .as_ref()
            .expect("inventory retained")
            .declared
            .dependency_units;
        assert_eq!(dependencies.len(), 2);
        assert_ne!(dependencies[0].package_id, dependencies[1].package_id);
        assert_eq!(dependencies[0].package_name, dependencies[1].package_name);
        assert_eq!(dependencies[0].target_name, dependencies[1].target_name);
    }

    #[test]
    fn pre_inventory_json_report_remains_backward_compatible() {
        let report = minimal_gate_report(None);
        let encoded = serde_json::to_string(&report).expect("serialize report");
        assert!(!encoded.contains("cargo_proof_inventory"));
        let decoded: JsonProofReport = serde_json::from_str(&encoded).expect("decode old shape");
        assert!(decoded.cargo_proof_inventory.is_none());
    }

    #[test]
    fn certified_test_execution_report_is_typed_and_round_trips() {
        assert!(
            CERTIFIED_TEST_EXECUTION_SCOPE.contains("Linux uses a sealed anonymous executable image")
                && CERTIFIED_TEST_EXECUTION_SCOPE
                    .contains("macOS uses a private signed pathname snapshot")
                && CERTIFIED_TEST_EXECUTION_SCOPE
                    .contains("original-artifact pathname/inode/xattr/mode identity is not"),
            "the public scope must disclose both host launch boundaries"
        );
        let mut gate = sample_gate();
        gate.test_execution = Some(CertifiedTestExecutionReport {
            schema: CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: CERTIFIED_TEST_EXECUTION_SCOPE.into(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit: Some(0),
            authorized_executables: vec![CertifiedTestExecutableReport {
                target: "demo::integration".into(),
                path: "/private/target/demo-test".into(),
                sha256: "a".repeat(64),
                size: 42,
            }],
            authorized_inventory_sha256: Some("b".repeat(64)),
            target_directory: Some("/private/target".into()),
        });
        let report = minimal_gate_report(Some(gate.clone()));
        let json = serde_json::to_string(&report).expect("serialize report");
        assert!(json.contains("\"test_execution\""), "{json}");
        assert!(json.contains("\"phase_b_state\":\"cargo-invocation-exited\""), "{json}");
        assert!(
            json.contains("\"completion_scope\":\"top-level-cargo-child-exit-only-v1\""),
            "{json}"
        );
        let back: JsonProofReport = serde_json::from_str(&json).expect("deserialize report");
        let restored_gate = back.verification_gate.expect("gate remains diagnostic");
        assert_eq!(restored_gate.decision, "inconclusive");
        assert_eq!(restored_gate.exit_code, 1);
        assert_eq!(restored_gate.counts.proved, 0);
        assert_eq!(restored_gate.counts.unknown, 1);
        assert_eq!(restored_gate.test_execution, gate.test_execution);

        for required in ["schema", "completion_scope"] {
            let mut value: serde_json::Value =
                serde_json::from_str(&json).expect("parse serialized report");
            value["verification_gate"]["test_execution"]
                .as_object_mut()
                .expect("test execution object")
                .remove(required);
            serde_json::from_value::<JsonProofReport>(value)
                .expect_err("certified-test nested semantics fields are required");
        }
    }

    #[test]
    fn old_json_without_verification_gate_deserializes_to_none() {
        // A pre-gate report has no `verification_gate` key (and, because the
        // field is None, serialization skips it). It must still deserialize,
        // defaulting the field to None — the additive-compatibility guarantee.
        let report = minimal_gate_report(None);
        let json = serde_json::to_string(&report).expect("serialize report");
        assert!(!json.contains("verification_gate"), "a None gate is skipped on serialize");
        let back: JsonProofReport = serde_json::from_str(&json).expect("old JSON must deserialize");
        assert!(back.verification_gate.is_none());
    }

    /// R-U Phase B2 pin: the NAMED reporting floor is extensionally identical
    /// to the variant-picking form for every assurance level and every verdict
    /// shape it can gate — one place defines the policy, and this test keeps
    /// them from ever diverging.
    #[test]
    fn named_reporting_floor_matches_the_variant_form() {
        let levels = [
            AssuranceLevel::Sound,
            AssuranceLevel::BoundedSound { depth: 3 },
            AssuranceLevel::Heuristic,
            AssuranceLevel::Unchecked,
            AssuranceLevel::Trusted,
            AssuranceLevel::SmtBacked,
            AssuranceLevel::Certified,
        ];
        use crate::Symbol;
        for level in levels {
            let proved = || VerificationResult::Proved {
                solver: Symbol::from("b2-pin"),
                time_ms: 1,
                strength: ProofStrength {
                    reasoning: ReasoningKind::Smt,
                    assurance: level.clone(),
                },
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            };
            let named = proved().require_reporting_floor();
            let variant = proved().require_assurance(AssuranceLevel::SmtBacked);
            assert_eq!(named.is_proved(), variant.is_proved(), "verdict for {level:?}");
            assert_eq!(named.assurance(), variant.assurance(), "assurance for {level:?}");
        }
    }

    /// R-U Phase E pin: the serialized `ProofStrength` carries the DERIVED
    /// grade axes; the legacy two fields round-trip untouched; and an
    /// inbound JSON with a forged `grade` field is INERT — the grade is
    /// recomputed from the legacy fields on read, so serialization can
    /// never smuggle assurance the legacy evidence does not support.
    #[test]
    fn serialized_strength_carries_derived_grade_and_forgery_is_inert() {
        let strength = ProofStrength::smt_unsat_unvalidated();
        let json = serde_json::to_string(&strength).expect("serialize");
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse");
        assert_eq!(
            value["grade"],
            serde_json::to_value(strength.grade()).expect("grade value"),
            "the serialized grade must be exactly the derived record"
        );

        let back: ProofStrength = serde_json::from_str(&json).expect("round-trip");
        assert_eq!(back, strength, "legacy fields round-trip untouched");

        // Old payloads (two fields, no grade) still deserialize.
        let legacy_json =
            serde_json::json!({"reasoning": "Smt", "assurance": "Unchecked"}).to_string();
        let old: ProofStrength = serde_json::from_str(&legacy_json).expect("legacy payload");
        assert_eq!(old, ProofStrength::smt_unsat_unvalidated());

        // A forged inbound grade claiming kernel certification changes
        // NOTHING: grade() derives from the legacy fields it rode in with.
        let forged = serde_json::json!({
            "reasoning": "Smt",
            "assurance": "Unchecked",
            "grade": serde_json::to_value(ProofStrength::smt_unsat_certified().grade())
                .expect("forged grade value"),
        })
        .to_string();
        let victim: ProofStrength = serde_json::from_str(&forged).expect("forged payload");
        assert_eq!(victim.grade(), ProofStrength::smt_unsat_unvalidated().grade());
        assert!(!victim.grade().is_certified(), "forgery must not certify");
        assert!(
            !victim.assurance.meets_reporting_floor(),
            "forgery must not cross the floor"
        );
    }

    #[test]
    fn require_assurance_is_monotone() {
        // T-GATE (docs/PROOF_OF_PERFECTION.md): require_assurance is the primitive
        // that turns a raw VerificationResult into a reported one. Machine-check it
        // is MONOTONE on the assurance lattice — it only ever weakens Proved->Unknown
        // (or is identity), NEVER strengthens (never raises a Proved's assurance,
        // never turns a non-Proved into Proved). AssuranceLevel is a finite domain,
        // so exhaustive enumeration over all variants x all floors is a TOTAL proof.
        use crate::Symbol;

        let levels = [
            AssuranceLevel::Sound,
            AssuranceLevel::BoundedSound { depth: 7 },
            AssuranceLevel::Heuristic,
            AssuranceLevel::Unchecked,
            AssuranceLevel::Trusted,
            AssuranceLevel::SmtBacked,
            AssuranceLevel::Certified,
        ];

        // Compile-time exhaustiveness guard: a new AssuranceLevel variant breaks
        // this no-wildcard match, forcing `levels` to be updated so the proof stays
        // total. (#[non_exhaustive] is crate-internal, so this compiles in-crate.)
        for lvl in &levels {
            match lvl {
                AssuranceLevel::Sound
                | AssuranceLevel::BoundedSound { .. }
                | AssuranceLevel::Heuristic
                | AssuranceLevel::Unchecked
                | AssuranceLevel::Trusted
                | AssuranceLevel::SmtBacked
                | AssuranceLevel::Certified => {}
            }
        }

        for input in &levels {
            for min in &levels {
                let proved = VerificationResult::Proved {
                    solver: Symbol::from("ay"),
                    time_ms: 5,
                    strength: ProofStrength {
                        reasoning: ReasoningKind::Smt,
                        assurance: input.clone(),
                    },
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                };
                let out = proved.require_assurance(min.clone());
                if input.strength_order() < min.strength_order() {
                    // Below the floor -> downgraded to Unknown, never Proved.
                    assert!(
                        !out.is_proved(),
                        "below-floor Proved must be weakened: input={input:?} min={min:?}"
                    );
                    assert_eq!(out.assurance(), None);
                } else {
                    // At/above the floor -> identity: still Proved, assurance UNCHANGED.
                    assert!(
                        out.is_proved(),
                        "at/above-floor Proved must remain Proved: input={input:?} min={min:?}"
                    );
                    assert_eq!(
                        out.assurance().as_ref(),
                        Some(input),
                        "assurance must be unchanged, never strengthened"
                    );
                }
                // Never-strengthen, universally: output order <= input order.
                let out_order = out.assurance().map_or(0, |a| a.strength_order());
                assert!(
                    out_order <= input.strength_order(),
                    "require_assurance must never raise assurance: input={input:?} min={min:?}"
                );
            }
        }

        // Non-Proved inputs are never fabricated into a Proved, for any floor.
        for min in &levels {
            let failed = VerificationResult::Failed {
                solver: Symbol::from("ay"),
                time_ms: 1,
                counterexample: None,
            };
            let unknown = VerificationResult::Unknown {
                solver: Symbol::from("ay"),
                time_ms: 1,
                reason: "x".into(),
            };
            let timeout = VerificationResult::Timeout { solver: Symbol::from("ay"), timeout_ms: 1 };
            assert!(!failed.require_assurance(min.clone()).is_proved());
            assert!(!unknown.require_assurance(min.clone()).is_proved());
            assert!(!timeout.require_assurance(min.clone()).is_proved());
        }
    }

    fn no_runtime_fallback_vc() -> VcKind {
        VcKind::Postcondition
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    #[test]
    fn sanitize_deserialized_regates_and_recomputes_lying_report() {
        // a deserialized report can LIE — claim a proved count
        // and `Verified`/PASS verdict while its only obligation is Proved-but-
        // Unchecked (below the SmtBacked floor). `sanitize_deserialized` must
        // re-gate to the truth: downgrade the weak Proved to Unknown and recompute
        // counts + verdicts so nothing false survives.
        let weak = ObligationReport {
            obligation_id: None,
            description: "x".into(),
            kind: "k".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved {
                strength: ProofStrength::smt_unsat_unvalidated(), // Unchecked, below floor
            },
            solver: "s".into(),
            time_ms: 0,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };
        let mut report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "x".into(),
                trust_version: "x".into(),
                timestamp: "x".into(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "c".into(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 1000, // the lie
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: vec![],
                verdict: CrateVerdict::Verified, // the lie
            },
            functions: vec![FunctionProofReport {
                function: "f".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 1,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 0,
                    max_proof_level: None,
                    verdict: FunctionVerdict::Verified, // the lie
                },
                obligations: vec![weak],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitization.structural_evidence_defects, 1);
        assert!(
            matches!(report.functions[0].obligations[0].outcome, ObligationOutcome::Unknown { .. }),
            "below-floor Proved must be re-gated to Unknown"
        );
        assert_eq!(report.functions[0].summary.proved, 0, "function proved recomputed to truth");
        assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(report.summary.total_proved, 0, "crate total_proved recomputed (lie erased)");
        assert_ne!(
            report.summary.verdict,
            CrateVerdict::Verified,
            "false Verified must not survive"
        );
    }

    #[test]
    fn sanitize_deserialized_requires_structured_publication_evidence_for_proved_rows() {
        let obligation = ObligationReport {
            obligation_id: Some("obl-1".into()),
            description: "ensures result is bounded".into(),
            kind: "postcondition".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved { strength: ProofStrength::deductive() },
            solver: "trust-full-verifier".into(),
            time_ms: 3,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };
        let mut report = report_with_obligation(obligation, CrateVerdict::Verified);

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitization.structural_evidence_defects, 1);
        assert_eq!(report.summary.total_proved, 0);
        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        match &report.functions[0].obligations[0].outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("proof_evidence is missing"), "{reason}");
            }
            other => panic!("missing proof evidence must downgrade to Unknown, got {other:?}"),
        }
    }

    #[test]
    fn sanitize_deserialized_downgrades_even_publication_shaped_structured_proofs() {
        let obligation = publication_grade_saved_obligation();
        let mut report = report_with_obligation(obligation, CrateVerdict::Inconclusive);

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitization.structural_evidence_defects, 0);
        assert_eq!(report.summary.total_proved, 0);
        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert!(matches!(
            report.functions[0].obligations[0].outcome,
            ObligationOutcome::Unknown { .. }
        ));
    }

    #[test]
    fn saved_claim_fallback_fingerprint_binds_exact_typed_vc_parameters() {
        let narrow_kind =
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u8(), Ty::u8()) };
        let wide_kind =
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u64(), Ty::u64()) };
        assert_eq!(narrow_kind.transport_tag(), wide_kind.transport_tag());
        assert_eq!(narrow_kind.description(), wide_kind.description());

        let mut narrow = publication_grade_saved_obligation();
        narrow.kind = narrow_kind.transport_tag();
        narrow.description = narrow_kind.description();
        let transport = narrow.transport_evidence.as_mut().expect("transport evidence");
        transport.claim_digest_sha256 = None;
        transport.typed_kind = Some(Box::new(narrow_kind));

        let mut wide = narrow.clone();
        wide.transport_evidence.as_mut().expect("transport evidence").typed_kind =
            Some(Box::new(wide_kind));

        assert_ne!(
            untrusted_saved_claim_fingerprint(&narrow),
            untrusted_saved_claim_fingerprint(&wide),
            "lossy compact tags must not collapse distinct exact VC claims"
        );
    }

    #[test]
    fn fully_schema_shaped_self_authenticated_saved_report_cannot_restore_proof_authority() {
        let report =
            report_with_obligation(publication_grade_saved_obligation(), CrateVerdict::Verified);
        let json = serde_json::to_string(&report).expect("serialize live report");
        assert!(json.contains("\"proof_evidence\""));
        assert!(json.contains("\"transport_evidence\""));
        assert!(json.contains("\"materialization\""));
        assert!(json.contains("\"digest\""));
        let (mut restored, first_sanitization, untrusted_claims) =
            JsonProofReport::decode_saved_json(json.as_bytes(), None)
                .expect("decode saved report exactly once");

        assert_eq!(first_sanitization.downgraded_proved, 1);
        assert_eq!(first_sanitization.evidence_defects, 1);
        assert_eq!(first_sanitization.structural_evidence_defects, 0);
        assert_eq!(untrusted_claims.obligations().len(), 1);
        assert_eq!(untrusted_claims.obligations()[0].function(), "crate::checked");
        assert_eq!(untrusted_claims.obligations()[0].function_index(), 0);
        assert_eq!(untrusted_claims.obligations()[0].obligation_id(), Some("obl-1"));
        assert_eq!(untrusted_claims.obligations()[0].obligation_index(), 0);
        assert_eq!(untrusted_claims.obligations()[0].outcome(), UntrustedSavedOutcomeClaim::Proved);

        // JsonProofReport's custom Deserialize boundary sanitizes before the
        // caller can observe the value.
        assert_eq!(restored.summary.verdict, CrateVerdict::Inconclusive);
        match &restored.functions[0].obligations[0].outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("no live verifier replay capability"), "{reason}");
                assert!(reason.contains("cannot carry proof authority"), "{reason}");
            }
            other => panic!("serialized evidence must not restore proof authority: {other:?}"),
        }

        // The explicit decode API returns the first receipt. A later defensive
        // sanitization remains safe and idempotent, but cannot recover that
        // provenance; saved-report consumers must inspect the first receipt.
        let sanitization = restored.sanitize_deserialized();
        assert_eq!(sanitization.downgraded_proved, 0);
        assert_eq!(sanitization.evidence_defects, 0);
    }

    #[test]
    fn direct_obligation_outcome_deserialization_cannot_materialize_proved() {
        let json =
            serde_json::to_vec(&ObligationOutcome::Proved { strength: ProofStrength::deductive() })
                .expect("serialize proved outcome");
        let restored: ObligationOutcome =
            serde_json::from_slice(&json).expect("deserialize direct outcome");

        match restored {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("no live verifier replay capability"), "{reason}");
                assert!(reason.contains("cannot carry proof authority"), "{reason}");
            }
            other => panic!("direct serde yielded proof authority: {other:?}"),
        }
    }

    #[test]
    fn direct_obligation_outcome_deserialization_cannot_materialize_runtime_authority() {
        let json = serde_json::to_vec(&ObligationOutcome::RuntimeChecked {
            note: Some("kernel-certified monitor installed".into()),
        })
        .expect("serialize runtime-checked outcome");
        let restored: ObligationOutcome =
            serde_json::from_slice(&json).expect("deserialize direct outcome");

        match restored {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("no live authenticated compiler/monitor capability"));
                assert!(reason.contains("cannot carry runtime-check authority"));
            }
            other => panic!("direct serde yielded runtime-check authority: {other:?}"),
        }
    }

    #[test]
    fn saved_runtime_checked_row_and_gate_fail_closed_without_live_monitor_authority() {
        let typed_kind = VcKind::Postcondition;
        let runtime = ObligationReport {
            obligation_id: Some("runtime-1".into()),
            description: typed_kind.description(),
            kind: typed_kind.transport_tag(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::RuntimeChecked {
                note: Some("kernel-certified monitor installed".into()),
            },
            solver: "trust-monitor".into(),
            time_ms: 3,
            evidence: None,
            proof_evidence: None,
            transport_evidence: Some(ObligationTransportEvidenceReport {
                obligation_id: Some("runtime-1".into()),
                claim_digest_sha256: None,
                typed_kind: Some(Box::new(typed_kind)),
                native_trust_ir: None,
                proof_evidence: None,
                monitor: Some(TransportMonitorEvidence {
                    status: TransportMonitorStatus::Monitored,
                    reason: "equivalence certificate accepted".into(),
                    predicate_digest: format!("sha256:{}", "a".repeat(64)),
                }),
            }),
        };
        let mut report = report_with_obligation(runtime, CrateVerdict::RuntimeChecked);
        report.functions[0].summary.proved = 0;
        report.functions[0].summary.runtime_checked = 1;
        report.functions[0].summary.verdict = FunctionVerdict::RuntimeChecked;
        report.summary.functions_verified = 0;
        report.summary.functions_runtime_checked = 1;
        report.summary.functions_inconclusive = 0;
        report.summary.total_proved = 0;
        report.summary.total_runtime_checked = 1;
        report.summary.verdict = CrateVerdict::RuntimeChecked;
        report.verification_gate = Some(VerificationGateReport {
            lane: "advisory".into(),
            verification_level: Some("L0".into()),
            decision: "conditional-pass".into(),
            exit_code: 0,
            counts: VerificationGateCounts {
                total: 1,
                proved: 0,
                failed: 0,
                unknown: 0,
                runtime_checked: 1,
                assumed: 0,
                mandated: 0,
                contract_panics: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: true,
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
        });

        let json = serde_json::to_vec(&report).expect("serialize runtime report");
        let (mut restored, sanitization, claims) =
            JsonProofReport::decode_saved_json(&json, None).expect("decode saved runtime report");

        assert_eq!(sanitization.downgraded_proved, 0);
        assert_eq!(sanitization.downgraded_runtime_checked, 1);
        assert_eq!(sanitization.evidence_defects, 0);
        assert!(sanitization.has_authority_downgrades());
        assert_eq!(claims.obligations()[0].outcome(), UntrustedSavedOutcomeClaim::RuntimeChecked);
        match &restored.functions[0].obligations[0].outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("cannot carry runtime-check authority"), "{reason}");
            }
            other => panic!("saved runtime claim retained authority: {other:?}"),
        }
        assert!(
            restored.functions[0].obligations[0]
                .transport_evidence
                .as_ref()
                .is_some_and(|transport| transport.monitor.is_none()),
            "saved runtime row retained a forgeable monitor-grade claim"
        );
        assert_eq!(restored.summary.total_runtime_checked, 0);
        assert_eq!(restored.summary.total_unknown, 1);
        assert_eq!(restored.summary.verdict, CrateVerdict::Inconclusive);
        let gate = restored.verification_gate.as_ref().expect("diagnostic gate retained");
        assert_eq!(gate.counts.runtime_checked, 0);
        assert_eq!(gate.counts.unknown, 1);
        assert!(!gate.conditional_on_runtime_checks);
        assert_eq!(gate.decision, "inconclusive");
        assert_eq!(gate.exit_code, 1);

        assert_eq!(restored.sanitize_deserialized(), SavedReportSanitization::default());
    }

    #[test]
    fn deserialized_unknown_row_cannot_materialize_monitor_grade() {
        let typed_kind = VcKind::Postcondition;
        let obligation = ObligationReport {
            obligation_id: Some("unknown-monitor-1".into()),
            description: typed_kind.description(),
            kind: typed_kind.transport_tag(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Unknown { reason: "solver returned unknown".into() },
            solver: "trust-monitor".into(),
            time_ms: 3,
            evidence: None,
            proof_evidence: None,
            transport_evidence: Some(ObligationTransportEvidenceReport {
                obligation_id: Some("unknown-monitor-1".into()),
                claim_digest_sha256: None,
                typed_kind: Some(Box::new(typed_kind)),
                native_trust_ir: None,
                proof_evidence: None,
                monitor: Some(TransportMonitorEvidence {
                    status: TransportMonitorStatus::Monitored,
                    reason: "forged saved monitor claim".into(),
                    predicate_digest: format!("sha256:{}", "b".repeat(64)),
                }),
            }),
        };

        // The direct DTO serde boundary is fail-closed, not only the canonical
        // whole-report decoder.
        let obligation_json = serde_json::to_vec(&obligation).expect("serialize obligation");
        let direct: ObligationReport =
            serde_json::from_slice(&obligation_json).expect("deserialize obligation");
        assert!(matches!(direct.outcome, ObligationOutcome::Unknown { .. }));
        assert!(
            direct.transport_evidence.as_ref().is_some_and(|transport| transport.monitor.is_none()),
            "direct obligation deserialization retained a monitor-grade claim"
        );

        // Unknown is not an authority-bearing outcome, so this also proves
        // monitor scrubbing is independent of the Proved/RuntimeChecked
        // downgrade branches that previously left this side channel intact.
        let report = report_with_obligation(obligation, CrateVerdict::Inconclusive);
        let report_json = serde_json::to_vec(&report).expect("serialize report");
        let (restored, sanitization, _) =
            JsonProofReport::decode_saved_json(&report_json, None).expect("decode saved report");
        assert_eq!(sanitization, SavedReportSanitization::default());
        assert!(matches!(
            restored.functions[0].obligations[0].outcome,
            ObligationOutcome::Unknown { .. }
        ));
        assert!(
            restored.functions[0].obligations[0]
                .transport_evidence
                .as_ref()
                .is_some_and(|transport| transport.monitor.is_none()),
            "whole-report deserialization retained a monitor-grade claim"
        );
    }

    #[test]
    fn direct_obligation_report_deserialization_cannot_materialize_proved() {
        let obligation = publication_grade_saved_obligation();
        let json = serde_json::to_vec(&obligation).expect("serialize obligation report");
        let restored: ObligationReport =
            serde_json::from_slice(&json).expect("deserialize direct obligation report");

        assert_eq!(restored.obligation_id.as_deref(), Some("obl-1"));
        assert!(restored.proof_evidence.is_some(), "evidence remains diagnostic");
        assert!(matches!(restored.outcome, ObligationOutcome::Unknown { .. }));
    }

    #[test]
    fn direct_function_report_deserialization_recomputes_forged_proof_summary() {
        let mut function =
            report_with_obligation(publication_grade_saved_obligation(), CrateVerdict::Verified)
                .functions
                .pop()
                .expect("function report");
        function.summary.proved = 999;
        function.summary.unattributed_proved = 2;
        function.summary.verdict = FunctionVerdict::Verified;

        let json = serde_json::to_vec(&function).expect("serialize function report");
        let restored: FunctionProofReport =
            serde_json::from_slice(&json).expect("deserialize direct function report");

        assert!(matches!(restored.obligations[0].outcome, ObligationOutcome::Unknown { .. }));
        assert_eq!(restored.summary.proved, 0);
        assert_eq!(restored.summary.unknown, 1);
        assert_eq!(restored.summary.unattributed_proved, 0);
        assert_eq!(restored.summary.unattributed_unknown, 2);
        assert_eq!(restored.summary.verdict, FunctionVerdict::Inconclusive);
    }

    #[test]
    fn caller_owned_ndjson_mirror_cannot_bypass_nested_authority_gate() {
        #[derive(Deserialize)]
        struct CallerNdjsonFunctionRecord {
            record_type: String,
            crate_name: String,
            #[serde(flatten)]
            function: FunctionProofReport,
        }

        let function =
            report_with_obligation(publication_grade_saved_obligation(), CrateVerdict::Verified)
                .functions
                .into_iter()
                .next()
                .expect("function report");
        let emitted = NdjsonFunctionRecord {
            record_type: "function".into(),
            crate_name: "c".into(),
            function,
        };
        let json = serde_json::to_vec(&emitted).expect("serialize NDJSON-shaped record");
        let restored: CallerNdjsonFunctionRecord =
            serde_json::from_slice(&json).expect("deserialize caller NDJSON mirror");

        assert_eq!(restored.record_type, "function");
        assert_eq!(restored.crate_name, "c");
        assert_eq!(restored.function.summary.proved, 0);
        assert_eq!(restored.function.summary.verdict, FunctionVerdict::Inconclusive);
        assert!(matches!(
            restored.function.obligations[0].outcome,
            ObligationOutcome::Unknown { .. }
        ));
    }

    #[test]
    fn standalone_legacy_proved_property_deserialization_is_rejected() {
        let property = ProvedProperty {
            description: "legacy proof claim".into(),
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            evidence: Some(ProofStrength::smt_unsat().into()),
        };
        let json = serde_json::to_vec(&property).expect("serialize legacy proved property");
        let error = serde_json::from_slice::<ProvedProperty>(&json)
            .expect_err("standalone legacy proof claim must fail closed");
        assert!(error.to_string().contains("cannot carry live proof authority"), "{error}");
    }

    #[test]
    fn legacy_function_report_deserialization_moves_proved_claims_to_unknown() {
        let function = FunctionReport {
            function: "crate::legacy".into(),
            proved: vec![ProvedProperty {
                description: "legacy proof claim".into(),
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                evidence: Some(ProofStrength::smt_unsat().into()),
            }],
            failed: vec![],
            unknown: vec![],
        };
        let json = serde_json::to_vec(&function).expect("serialize legacy function report");
        let restored: FunctionReport =
            serde_json::from_slice(&json).expect("deserialize legacy function report");

        assert!(restored.proved.is_empty());
        assert_eq!(restored.unknown.len(), 1);
        assert_eq!(restored.unknown[0].description, "legacy proof claim");
        assert!(restored.unknown[0].reason.contains("no live verifier replay capability"));
    }

    #[test]
    fn legacy_proof_report_deserialization_recomputes_claimed_totals_once() {
        let report = ProofReport {
            crate_name: "legacy".into(),
            functions: vec![FunctionReport {
                function: "legacy::checked".into(),
                proved: vec![ProvedProperty {
                    description: "function proof claim".into(),
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    evidence: None,
                }],
                failed: vec![],
                unknown: vec![],
            }],
            // One aggregate copy plus one crate-only residual proof claim.
            total_proved: 2,
            total_failed: 0,
            total_unknown: 1,
        };
        let json = serde_json::to_vec(&report).expect("serialize legacy proof report");
        let restored: ProofReport =
            serde_json::from_slice(&json).expect("deserialize legacy proof report");

        assert_eq!(restored.total_proved, 0);
        assert_eq!(restored.total_failed, 0);
        assert_eq!(restored.total_unknown, 3);
        assert!(restored.functions[0].proved.is_empty());
        assert_eq!(restored.functions[0].unknown.len(), 1);
    }

    #[test]
    fn serde_boundary_downgrades_saved_pass_gate_and_unattributed_proof_side_channels() {
        let mut report =
            report_with_obligation(publication_grade_saved_obligation(), CrateVerdict::Verified);
        report.summary.total_unattributed_proved = 2;
        report.verification_gate = Some(VerificationGateReport {
            lane: "strict".into(),
            verification_level: Some("L1".into()),
            decision: "pass".into(),
            exit_code: 0,
            counts: VerificationGateCounts {
                total: 1,
                proved: 1,
                failed: 0,
                unknown: 0,
                runtime_checked: 0,
                assumed: 0,
                mandated: 0,
                contract_panics: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: false,
            conditional_on_visitation_entries: false,
            coverage: Some(VerificationCoverage::from_counts(1, 1)),
            test_execution: None,
        });

        let restored: JsonProofReport =
            serde_json::from_slice(&serde_json::to_vec(&report).expect("serialize report"))
                .expect("deserialize report");

        assert_eq!(restored.summary.total_unattributed_proved, 0);
        assert_eq!(restored.summary.total_unattributed_unknown, 2);
        let gate = restored.verification_gate.expect("saved gate remains diagnostic");
        assert_eq!(gate.decision, "inconclusive");
        assert_eq!(gate.exit_code, 1);
        assert_eq!(gate.counts.proved, 0);
        assert_eq!(gate.counts.unknown, 1);
    }

    #[test]
    fn recompute_summaries_is_non_authoritative_aggregation_only() {
        let obligation = ObligationReport {
            obligation_id: Some("unvalidated-live-row".into()),
            description: "caller-asserted outcome".into(),
            kind: "postcondition".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved { strength: ProofStrength::deductive() },
            solver: "caller".into(),
            time_ms: 0,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };
        let mut report = report_with_obligation(obligation, CrateVerdict::Inconclusive);
        report.summary.total_proved = 999;
        report.summary.total_unknown = 999;
        report.functions[0].summary.proved = 999;
        report.functions[0].summary.unknown = 999;

        report.recompute_summaries_from_obligation_outcomes();

        assert_eq!(report.functions[0].summary.proved, 1);
        assert_eq!(report.functions[0].summary.unknown, 0);
        assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Verified);
        assert_eq!(report.summary.total_proved, 1);
        assert_eq!(report.summary.total_unknown, 0);
        assert_eq!(report.summary.verdict, CrateVerdict::Verified);
        assert!(matches!(
            report.functions[0].obligations[0].outcome,
            ObligationOutcome::Proved { .. }
        ));
    }

    #[test]
    fn serde_boundary_rejects_semantically_swapped_self_authenticated_evidence() {
        // Both rows deliberately reuse the same public obligation ID. Their
        // independently self-hashed evidence sets are schema-valid, and each
        // proof/transport pair remains internally consistent after swapping.
        // Serialized shape therefore cannot authenticate which semantic claim
        // was actually verified.
        let mut first = publication_grade_saved_obligation_with_identity(
            "duplicate-id",
            "1",
            "2",
            "first semantic claim",
        );
        let mut second = publication_grade_saved_obligation_with_identity(
            "duplicate-id",
            "3",
            "4",
            "different semantic claim",
        );
        std::mem::swap(&mut first.proof_evidence, &mut second.proof_evidence);
        std::mem::swap(&mut first.transport_evidence, &mut second.transport_evidence);

        let mut report = report_with_obligation(first, CrateVerdict::Verified);
        report.functions[0].obligations.push(second);
        report.recompute_summaries_from_obligation_outcomes();
        assert_eq!(report.summary.total_proved, 2);
        assert_eq!(report.summary.verdict, CrateVerdict::Verified);

        let json = serde_json::to_string(&report).expect("serialize swapped saved report");
        let restored: JsonProofReport =
            serde_json::from_str(&json).expect("deserialize swapped saved report");

        assert_eq!(restored.summary.total_proved, 0);
        assert_eq!(restored.summary.total_unknown, 2);
        assert_eq!(restored.summary.verdict, CrateVerdict::Inconclusive);
        assert!(
            restored.functions[0]
                .obligations
                .iter()
                .all(|obligation| matches!(obligation.outcome, ObligationOutcome::Unknown { .. }))
        );
    }

    #[test]
    fn path_backed_materialization_requires_explicit_root_and_live_topology_accepts_it() {
        let temp = tempfile::tempdir().expect("temporary materialization root");
        let root = temp.path().canonicalize().expect("canonical materialization root");
        let mut obligation = publication_grade_saved_obligation();
        let proof = obligation.proof_evidence.as_mut().expect("proof evidence");
        externalize_test_artifact(&root, &mut proof.artifacts[0]);
        let path_backed = proof.artifacts[0].materialization.as_ref().expect("materialization");
        let digest = proof.artifacts[0].digest.as_ref().expect("digest");

        assert!(path_backed.decoded_bytes().is_err());
        assert!(!path_backed.matches_sha256_digest(digest));
        assert!(path_backed.matches_sha256_digest_at_root(digest, &root));
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &proof.artifacts, Some("obl-1"))
                .is_some(),
            "generic/saved-report validation must not open producer paths"
        );
        assert!(
            transport_proof_artifact_topology_defect_at_root(
                "trust-wp",
                &proof.artifacts,
                Some("obl-1"),
                &root,
            )
            .is_none(),
            "live validation with an explicit canonical root should accept the exact store file"
        );
    }

    #[test]
    fn saved_report_path_materialization_fails_closed_without_report_root_policy() {
        let temp = tempfile::tempdir().expect("temporary materialization root");
        let root = temp.path().canonicalize().expect("canonical materialization root");
        let mut obligation = publication_grade_saved_obligation();
        let proof = obligation.proof_evidence.as_mut().expect("proof evidence");
        externalize_test_artifact(&root, &mut proof.artifacts[0]);
        obligation
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof")
            .artifacts = proof.artifacts.clone();
        let mut report = report_with_obligation(obligation, CrateVerdict::Verified);

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.structural_evidence_defects, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    }

    #[test]
    fn explicit_report_root_does_not_restore_saved_proof_authority() {
        let temp = tempfile::tempdir().expect("temporary materialization root");
        let root = temp.path().canonicalize().expect("canonical materialization root");
        let mut obligation = publication_grade_saved_obligation();
        let proof = obligation.proof_evidence.as_mut().expect("proof evidence");
        externalize_test_artifact(&root, &mut proof.artifacts[0]);
        obligation
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof")
            .artifacts = proof.artifacts.clone();
        let mut report = report_with_obligation(obligation, CrateVerdict::Inconclusive);

        let sanitization = report.sanitize_deserialized_at_root(&root);

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitization.structural_evidence_defects, 0);
        assert_eq!(report.summary.total_proved, 0);
        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    }

    #[test]
    fn saved_report_transport_obligation_identity_is_mandatory_and_exact() {
        let mut obligation = publication_grade_saved_obligation();
        obligation.transport_evidence.as_mut().expect("transport evidence").obligation_id = None;

        let defect = saved_obligation_structural_proof_defect(&obligation, None)
            .expect("missing nested transport identity must be a structural defect");
        assert!(defect.contains("obligation_id does not match"), "{defect}");

        let mut report = report_with_obligation(obligation, CrateVerdict::Verified);
        let sanitization = report.sanitize_deserialized();
        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.structural_evidence_defects, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    }

    #[test]
    fn saved_report_redundant_proof_fields_are_exactly_bound() {
        let defect = |obligation: &ObligationReport| {
            saved_obligation_structural_proof_defect(obligation, None)
                .expect("mutated redundant proof field must be a structural defect")
        };

        let mut outcome_mismatch = publication_grade_saved_obligation();
        outcome_mismatch.outcome =
            ObligationOutcome::Proved { strength: ProofStrength::inductive() };
        let mut report = report_with_obligation(outcome_mismatch, CrateVerdict::Verified);
        let sanitization = report.sanitize_deserialized();
        assert_eq!(sanitization.structural_evidence_defects, 1);
        match &report.functions[0].obligations[0].outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("outcome strength does not match"), "{reason}");
            }
            other => panic!("mismatched outcome strength must fail closed, got {other:?}"),
        }

        let mut outer_evidence_mismatch = publication_grade_saved_obligation();
        outer_evidence_mismatch.evidence = Some(ProofEvidence::from(ProofStrength::inductive()));
        assert!(defect(&outer_evidence_mismatch).contains("obligation evidence does not match"));

        let mut normalized_evidence_mismatch = publication_grade_saved_obligation();
        let mismatched_evidence = ProofEvidence::from(ProofStrength::inductive());
        normalized_evidence_mismatch.evidence = Some(mismatched_evidence.clone());
        normalized_evidence_mismatch.proof_evidence.as_mut().expect("proof evidence").evidence =
            mismatched_evidence.clone();
        normalized_evidence_mismatch
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof evidence")
            .evidence = Some(mismatched_evidence);
        assert!(
            defect(&normalized_evidence_mismatch)
                .contains("evidence does not match proof_evidence.strength")
        );

        let mut router_attributed = publication_grade_saved_obligation();
        router_attributed.proof_evidence.as_mut().expect("proof evidence").provenance =
            ObligationEvidenceProvenanceReport::RouterAttributed;
        assert!(defect(&router_attributed).contains("not native-backend attributed"));

        let mut mismatched_verifier = publication_grade_saved_obligation();
        mismatched_verifier.proof_evidence.as_mut().expect("proof evidence").provenance =
            ObligationEvidenceProvenanceReport::NativeBackend {
                verifier: "attacker-backend".into(),
            };
        assert!(defect(&mismatched_verifier).contains("verifier does not match backend"));

        let mut unbound_certificate = publication_grade_saved_obligation();
        unbound_certificate.proof_evidence.as_mut().expect("proof evidence").proof_certificate =
            Some(vec![1, 2, 3]);
        assert!(defect(&unbound_certificate).contains("unbound raw certificate"));
    }

    #[test]
    fn saved_report_native_identity_domains_cannot_be_relabelled_independently() {
        fn downgrade_reason(obligation: ObligationReport) -> String {
            let mut report = report_with_obligation(obligation, CrateVerdict::Verified);
            let sanitization = report.sanitize_deserialized();
            assert_eq!(sanitization.evidence_defects, 1);
            match &report.functions[0].obligations[0].outcome {
                ObligationOutcome::Unknown { reason } => reason.clone(),
                other => panic!("identity mutation must fail closed, got {other:?}"),
            }
        }

        let mut proof_id_relabel = publication_grade_saved_obligation();
        proof_id_relabel.proof_evidence.as_mut().expect("proof").proof_id = Some("999".into());
        proof_id_relabel
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof")
            .proof_id = Some("999".into());
        assert!(downgrade_reason(proof_id_relabel).contains("do not reconstruct native_id"));

        let mut backend_relabel = publication_grade_saved_obligation();
        let proof = backend_relabel.proof_evidence.as_mut().expect("proof");
        proof.backend = "attacker-backend".into();
        proof.provenance = ObligationEvidenceProvenanceReport::NativeBackend {
            verifier: "attacker-backend".into(),
        };
        proof.native_trust_ir.as_mut().expect("proof native").backend = "attacker-backend".into();
        let transport = backend_relabel.transport_evidence.as_mut().expect("transport");
        transport.native_trust_ir.as_mut().expect("transport native").backend =
            "attacker-backend".into();
        transport.proof_evidence.as_mut().expect("transport proof").backend =
            "attacker-backend".into();
        assert!(downgrade_reason(backend_relabel).contains("canonical native TrustIr suite"));

        let mut binding_relabel = publication_grade_saved_obligation();
        let attacker_binding = "trust_ir-native-trust-wp-request-1-proof-999";
        let structural = bound_test_artifact(
            "NormalizedObligation",
            b"attacker-bound normalized input",
            attacker_binding,
            "obl-1",
            vec![],
        );
        let transcript = bound_test_artifact(
            "SolverTranscript",
            b"attacker-bound transcript",
            attacker_binding,
            "obl-1",
            vec![TransportArtifactReference {
                kind: structural.kind.clone(),
                digest: structural.digest.clone().expect("structural digest"),
            }],
        );
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"attacker-bound check",
            attacker_binding,
            "obl-1",
            vec![TransportArtifactReference {
                kind: transcript.kind.clone(),
                digest: transcript.digest.clone().expect("transcript digest"),
            }],
        );
        let native_artifacts = binding_relabel
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.native_trust_ir.as_ref())
            .expect("native evidence")
            .artifacts
            .clone();
        let mut attacker_artifacts = vec![structural, transcript, check];
        attacker_artifacts.extend(native_artifacts);
        binding_relabel.proof_evidence.as_mut().expect("proof").artifacts =
            attacker_artifacts.clone();
        binding_relabel
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof")
            .artifacts = attacker_artifacts;
        assert!(downgrade_reason(binding_relabel).contains("proof_binding_id"));
    }

    #[test]
    fn transport_topology_rejects_whitespace_owner_alias() {
        let artifacts =
            publication_grade_saved_obligation().proof_evidence.expect("proof evidence").artifacts;
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &artifacts, Some(" obl-1 "),)
                .is_some_and(|defect| defect.contains("not canonical"))
        );
    }

    #[test]
    fn path_materialization_rejects_absolute_traversal_tamper_and_duplicate_path() {
        let bytes = b"bounded exact artifact";
        let digest = TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: lowercase_transport_hex(&Sha256::digest(bytes)),
        };
        let materialization =
            TransportArtifactMaterialization::from_exact_bytes(bytes, "binding-1", vec![])
                .expect("inline materialization");
        assert!(materialization.clone().with_materialized_path("/tmp/attacker").is_none());
        assert!(
            materialization
                .clone()
                .with_materialized_path(format!(
                    "{}/sha256/../{}",
                    TRANSPORT_ARTIFACT_STORE_DIRECTORY, digest.value
                ))
                .is_none()
        );

        let temp = tempfile::tempdir().expect("temporary materialization root");
        let root = temp.path().canonicalize().expect("canonical materialization root");
        let store = root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        std::fs::create_dir_all(&store).expect("create store");
        std::fs::write(store.join(&digest.value), bytes).expect("write exact artifact");
        let path = format!("{}/sha256/{}", TRANSPORT_ARTIFACT_STORE_DIRECTORY, digest.value);
        let path_backed = materialization
            .with_materialized_path(path.clone())
            .expect("path-backed materialization");
        assert!(path_backed.matches_sha256_digest_at_root(&digest, &root));

        std::fs::write(store.join(&digest.value), b"same-length-wrong-bytes")
            .expect("tamper artifact");
        assert!(!path_backed.matches_sha256_digest_at_root(&digest, &root));

        let mut proof =
            publication_grade_saved_obligation().proof_evidence.expect("proof evidence").artifacts;
        externalize_test_artifact(&root, &mut proof[0]);
        proof[1].materialization.as_mut().expect("check materialization").encoded_bytes.clear();
        proof[1].materialization.as_mut().expect("check materialization").materialized_path = proof
            [0]
        .materialization
        .as_ref()
        .expect("transcript materialization")
        .materialized_path
        .clone();
        assert!(
            transport_proof_artifact_topology_defect_at_root(
                "trust-wp",
                &proof,
                Some("obl-1"),
                &root,
            )
            .is_some_and(|defect| defect.contains("duplicate materialization path"))
        );
    }

    #[cfg(unix)]
    #[test]
    fn path_materialization_rejects_symlink_leaf_and_store_component() {
        use std::os::unix::fs::symlink;

        let bytes = b"symlink target bytes";
        let digest = TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: lowercase_transport_hex(&Sha256::digest(bytes)),
        };
        let inline = TransportArtifactMaterialization::from_exact_bytes(bytes, "binding-1", vec![])
            .expect("inline materialization");
        let path = format!("{}/sha256/{}", TRANSPORT_ARTIFACT_STORE_DIRECTORY, digest.value);

        let leaf_temp = tempfile::tempdir().expect("leaf symlink root");
        let leaf_root = leaf_temp.path().canonicalize().expect("canonical leaf root");
        let leaf_store = leaf_root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        std::fs::create_dir_all(&leaf_store).expect("create leaf store");
        let outside = leaf_root.join("outside");
        std::fs::write(&outside, bytes).expect("write outside file");
        symlink(&outside, leaf_store.join(&digest.value)).expect("create leaf symlink");
        let leaf_materialization =
            inline.clone().with_materialized_path(path.clone()).expect("leaf descriptor");
        assert!(!leaf_materialization.matches_sha256_digest_at_root(&digest, &leaf_root));

        let dir_temp = tempfile::tempdir().expect("directory symlink root");
        let dir_root = dir_temp.path().canonicalize().expect("canonical directory root");
        let outside_store = dir_root.join("outside-store");
        std::fs::create_dir_all(outside_store.join("sha256")).expect("outside store");
        std::fs::write(outside_store.join("sha256").join(&digest.value), bytes)
            .expect("write outside artifact");
        symlink(&outside_store, dir_root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY))
            .expect("create store symlink");
        let dir_materialization =
            inline.with_materialized_path(path).expect("directory descriptor");
        assert!(!dir_materialization.matches_sha256_digest_at_root(&digest, &dir_root));
    }

    #[test]
    fn saved_report_rejects_stable_digest_on_load_bearing_artifact() {
        let mut obligation = publication_grade_saved_obligation();
        let stable = TransportArtifactDigest {
            algorithm: "trust_ir-stable-v1".into(),
            value: "2222222222222222222222222222222222222222222222222222222222222222".into(),
        };
        obligation
            .proof_evidence
            .as_mut()
            .expect("proof report")
            .artifacts
            .iter_mut()
            .find(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
            .expect("solver transcript")
            .digest = Some(stable.clone());
        obligation
            .transport_evidence
            .as_mut()
            .and_then(|transport| transport.proof_evidence.as_mut())
            .expect("transport proof")
            .artifacts
            .iter_mut()
            .find(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
            .expect("transport solver transcript")
            .digest = Some(stable);
        let mut report = report_with_obligation(obligation, CrateVerdict::Verified);

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    }

    #[test]
    fn native_trust_ir_shape_rejects_wrong_kind_and_wrong_uri() {
        let obligation = publication_grade_saved_obligation();
        let native = obligation
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.native_trust_ir.clone())
            .expect("native evidence");
        assert!(native_trust_ir_artifact_shape_is_publishable(&native));

        let mut wrong_kind = native.clone();
        wrong_kind.artifacts[2].kind = "banana".into();
        assert!(!native_trust_ir_artifact_shape_is_publishable(&wrong_kind));

        let mut wrong_uri = native;
        wrong_uri.artifacts[1].uri = Some("artifact://attacker/request/1".into());
        assert!(!native_trust_ir_artifact_shape_is_publishable(&wrong_uri));
    }

    #[test]
    fn native_trust_ir_shape_accepts_inline_bytes_and_rejects_duplicate_paths() {
        let obligation = publication_grade_saved_obligation();
        let mut native = obligation
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.native_trust_ir.clone())
            .expect("native evidence");

        assert!(native.artifacts.iter().all(|artifact| {
            artifact.materialization.as_ref().is_some_and(|materialization| {
                materialization.materialized_path.is_none()
                    && !materialization.encoded_bytes.is_empty()
            })
        }));
        assert!(
            native_trust_ir_artifact_shape_is_publishable(&native),
            "exact inline materializations are a valid no-root evidence form"
        );

        let temp = tempfile::tempdir().expect("temporary native materialization root");
        let root = temp.path().canonicalize().expect("canonical materialization root");
        for artifact in &mut native.artifacts {
            externalize_test_artifact(&root, artifact);
        }
        assert!(native_trust_ir_artifact_shape_is_publishable_at_root(&native, &root));

        let duplicate_path = native.artifacts[0]
            .materialization
            .as_ref()
            .and_then(|materialization| materialization.materialized_path.clone())
            .expect("first path-backed materialization");
        native.artifacts[1]
            .materialization
            .as_mut()
            .expect("second path-backed materialization")
            .materialized_path = Some(duplicate_path);
        assert!(
            !native_trust_ir_artifact_shape_is_publishable_at_root(&native, &root),
            "two structural artifacts may not alias one materialized path"
        );
    }

    #[test]
    fn proof_topology_rejects_presence_only_mixed_transplanted_and_mutated_sets() {
        let artifacts =
            publication_grade_saved_obligation().proof_evidence.expect("proof evidence").artifacts;
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &artifacts, Some("obl-1"))
                .is_none()
        );

        let mut digest_only = artifacts.clone();
        digest_only[0].materialization = None;
        digest_only[0].metadata = Some(serde_json::json!({"bytes": "not artifact bytes"}));
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &digest_only, Some("obl-1"))
                .is_some(),
            "URI/digest/metadata presence must not replace exact bytes"
        );

        assert!(
            transport_proof_artifact_topology_defect(
                "trust-wp",
                &artifacts,
                Some("different-obligation")
            )
            .is_some(),
            "a complete proof set cannot be transplanted to another owner"
        );

        let mut duplicate = artifacts.clone();
        duplicate.push(duplicate[0].clone());
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &duplicate, Some("obl-1"))
                .is_some_and(|defect| defect.contains("duplicate kind/digest"))
        );

        let mut wrong_reference = artifacts.clone();
        wrong_reference[1]
            .materialization
            .as_mut()
            .expect("transcript materialization")
            .referenced_artifacts
            .clear();
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &wrong_reference, Some("obl-1"))
                .is_some(),
            "descriptor-only reference mutation must not rebind the hashed frame"
        );

        let mut vacuous_lineage = artifacts.clone();
        let vacuous_transcript = bound_test_artifact(
            "SolverTranscript",
            b"transcript that names no structural input",
            "proof-binding-1",
            "obl-1",
            vec![],
        );
        let vacuous_check = bound_test_artifact(
            "ProofCheckReport",
            b"check over structurally vacuous transcript",
            "proof-binding-1",
            "obl-1",
            vec![TransportArtifactReference {
                kind: vacuous_transcript.kind.clone(),
                digest: vacuous_transcript.digest.clone().expect("vacuous transcript digest"),
            }],
        );
        vacuous_lineage[1] = vacuous_transcript;
        vacuous_lineage[2] = vacuous_check;
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &vacuous_lineage, Some("obl-1"))
                .is_some_and(|defect| defect.contains("exact structural proof input")),
            "a proof DAG cannot receive credit from a transcript with vacuous structural lineage"
        );

        let mut role_substitution = artifacts.clone();
        role_substitution[1].kind = "ReplayLog".into();
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &role_substitution, Some("obl-1"))
                .is_some(),
            "an artifact cannot be relabeled into another DAG role"
        );

        let mut mixed = artifacts.clone();
        mixed.push(bound_test_artifact(
            "ProofCertificate",
            b"certificate",
            "proof-binding-1",
            "obl-1",
            vec![],
        ));
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &mixed, Some("obl-1")).is_some(),
            "certificate and transcript routes must remain exclusive"
        );

        let mut extra = artifacts;
        extra.push(bound_test_artifact(
            "Model",
            b"unconsumed model",
            "proof-binding-1",
            "obl-1",
            vec![],
        ));
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &extra, Some("obl-1"))
                .is_some_and(|defect| defect.contains("structural proof inputs")),
            "a Model outside the exact PDR structural lineage must fail closed"
        );
    }

    #[test]
    fn proof_topology_accepts_exact_owner_bound_pdr_invariant_model_dag() {
        let artifacts = pdr_model_proof_artifacts();
        assert!(
            transport_proof_artifact_topology_defect("trust-mc", &artifacts, Some("obl-1"))
                .is_none(),
            "a PDR model consumed from the exact structural input and referenced by replay/check is part of the proof DAG"
        );
    }

    #[test]
    fn proof_topology_rejects_unbound_or_incompletely_consumed_pdr_models() {
        let artifacts = pdr_model_proof_artifacts();
        let model_index = artifacts
            .iter()
            .position(|artifact| normalized_artifact_kind(&artifact.kind) == "model")
            .expect("PDR model artifact");
        let replay_index = artifacts
            .iter()
            .position(|artifact| normalized_artifact_kind(&artifact.kind) == "replay_log")
            .expect("replay artifact");
        let check_index = artifacts
            .iter()
            .position(|artifact| normalized_artifact_kind(&artifact.kind) == "proof_check_report")
            .expect("proof-check artifact");
        let transcript = artifacts
            .iter()
            .find(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
            .expect("solver transcript")
            .clone();
        let model = artifacts[model_index].clone();
        let replay = artifacts[replay_index].clone();
        let binding = transcript
            .materialization
            .as_ref()
            .expect("transcript materialization")
            .proof_binding_id
            .clone();
        let structural_references = transcript
            .materialization
            .as_ref()
            .expect("transcript materialization")
            .referenced_artifacts
            .clone();
        let transcript_reference = TransportArtifactReference {
            kind: transcript.kind.clone(),
            digest: transcript.digest.clone().expect("transcript digest"),
        };
        let model_reference = TransportArtifactReference {
            kind: model.kind.clone(),
            digest: model.digest.clone().expect("model digest"),
        };

        let mut duplicate_model = artifacts.clone();
        duplicate_model.push(bound_test_artifact(
            "Model",
            b"second PDR invariant model",
            &binding,
            "obl-1",
            structural_references.clone(),
        ));
        assert!(
            transport_proof_artifact_topology_defect("trust-mc", &duplicate_model, Some("obl-1"))
                .is_some_and(|defect| defect.contains("at most one model")),
            "two distinct materialized models must not be admitted into one proof DAG"
        );

        let mut no_structural_lineage = artifacts.clone();
        no_structural_lineage[model_index] = bound_test_artifact(
            "Model",
            b"model without structural lineage",
            &binding,
            "obl-1",
            vec![],
        );
        assert!(
            transport_proof_artifact_topology_defect(
                "trust-mc",
                &no_structural_lineage,
                Some("obl-1")
            )
            .is_some_and(|defect| defect.contains("structural proof inputs")),
            "a model must consume exactly the transcript's structural inputs"
        );

        let mut wrong_binding = artifacts.clone();
        wrong_binding[model_index] = bound_test_artifact(
            "Model",
            b"model under another binding",
            "proof-binding-attacker",
            "obl-1",
            structural_references.clone(),
        );
        assert!(
            transport_proof_artifact_topology_defect("trust-mc", &wrong_binding, Some("obl-1"))
                .is_some_and(|defect| defect.contains("structural proof inputs")),
            "a model under another proof binding must fail closed"
        );

        let mut wrong_owner = artifacts.clone();
        wrong_owner[model_index] = bound_test_artifact(
            "Model",
            b"model under another owner",
            &binding,
            "obl-attacker",
            structural_references,
        );
        assert!(
            transport_proof_artifact_topology_defect("trust-mc", &wrong_owner, Some("obl-1"))
                .is_some_and(|defect| defect.contains("structural proof inputs")),
            "a model under another obligation owner must fail closed"
        );

        let mut replay_omits_model = artifacts.clone();
        replay_omits_model[replay_index] = bound_test_artifact(
            "ReplayLog",
            b"replay that omits the PDR model",
            &binding,
            "obl-1",
            vec![transcript_reference.clone()],
        );
        assert!(
            transport_proof_artifact_topology_defect(
                "trust-mc",
                &replay_omits_model,
                Some("obl-1")
            )
            .is_some_and(|defect| defect.contains("replay artifact")),
            "PDR replay must consume the transcript and its invariant model"
        );

        let mut check_omits_replay = artifacts;
        check_omits_replay[check_index] = bound_test_artifact(
            "ProofCheckReport",
            b"check that omits the replay",
            &binding,
            "obl-1",
            vec![transcript_reference, model_reference],
        );
        assert!(
            transport_proof_artifact_topology_defect(
                "trust-mc",
                &check_omits_replay,
                Some("obl-1")
            )
            .is_some_and(|defect| defect.contains("proof-check artifact")),
            "when replay is present the PDR proof check must consume transcript, model, and replay"
        );

        assert!(
            replay
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.referenced_artifacts.len() == 2),
            "fixture control: the accepted replay consumes transcript and model"
        );
    }

    #[test]
    fn proof_topology_accepts_producer_reference_order_but_authenticates_the_sequence() {
        let mut artifacts =
            publication_grade_saved_obligation().proof_evidence.expect("proof evidence").artifacts;
        let transcript = artifacts
            .iter()
            .find(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
            .expect("solver transcript")
            .clone();
        let binding = transcript
            .materialization
            .as_ref()
            .expect("transcript materialization")
            .proof_binding_id
            .clone();
        let transcript_reference = TransportArtifactReference {
            kind: transcript.kind.clone(),
            digest: transcript.digest.clone().expect("transcript digest"),
        };
        let replay = bound_test_artifact(
            "ReplayLog",
            b"exact replay log",
            &binding,
            "obl-1",
            vec![transcript_reference.clone()],
        );
        let replay_reference = TransportArtifactReference {
            kind: replay.kind.clone(),
            digest: replay.digest.clone().expect("replay digest"),
        };
        assert!(
            transcript_reference > replay_reference,
            "the producer's enum order must intentionally differ from lexical role order"
        );
        let producer_order = vec![transcript_reference.clone(), replay_reference.clone()];
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact proof-check report over transcript and replay",
            &binding,
            "obl-1",
            producer_order.clone(),
        );
        assert_eq!(
            check.materialization.as_ref().expect("check materialization").referenced_artifacts,
            producer_order,
            "the transport constructor must preserve the producer-authored sequence"
        );
        let check_index = artifacts
            .iter()
            .position(|artifact| normalized_artifact_kind(&artifact.kind) == "proof_check_report")
            .expect("proof-check artifact");
        artifacts[check_index] = check.clone();
        artifacts.push(replay.clone());
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &artifacts, Some("obl-1"))
                .is_none(),
            "set membership must accept the producer's typed-enum reference order"
        );

        let mut reordered = artifacts.clone();
        let reordered_check = &mut reordered[check_index];
        reordered_check
            .materialization
            .as_mut()
            .expect("check materialization")
            .referenced_artifacts
            .swap(0, 1);
        let reordered_materialization =
            reordered_check.materialization.as_ref().expect("check materialization");
        assert!(
            transport_artifact_references_exactly(reordered_check, &[&transcript, &replay]),
            "topology membership is intentionally order-independent"
        );
        assert!(
            reordered_materialization
                .matches_sha256_digest(reordered_check.digest.as_ref().expect("check digest")),
            "descriptor reordering does not alter the separately hashed payload bytes"
        );
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &reordered, Some("obl-1"))
                .is_some(),
            "the bound envelope must reject a descriptor sequence not encoded in its bytes"
        );

        let duplicate_references =
            vec![transcript_reference.clone(), replay_reference, transcript_reference];
        assert!(
            TransportArtifactMaterialization::from_exact_bytes(
                b"duplicate-reference constructor control",
                &binding,
                duplicate_references,
            )
            .is_none(),
            "non-adjacent duplicate references must fail at construction"
        );
        let check_for_missing_digest = check.clone();
        let mut duplicate_shape = check;
        let check_materialization =
            duplicate_shape.materialization.as_mut().expect("check materialization");
        let duplicate = check_materialization.referenced_artifacts[0].clone();
        check_materialization.referenced_artifacts.push(duplicate);
        assert!(
            check_materialization.decoded_bytes().is_err(),
            "deserialized duplicate references must fail shape validation"
        );

        let mut missing_digest = replay;
        missing_digest.digest = None;
        assert!(
            !transport_artifact_references_exactly(
                &check_for_missing_digest,
                &[&transcript, &missing_digest],
            ),
            "a consumed artifact without an exact digest must fail closed"
        );
    }

    #[test]
    fn transport_evidence_artifact_count_is_bounded_before_policy_evaluation() {
        let artifact = serde_json::json!({"kind": "Report"});
        let proof_json = |count: usize| {
            serde_json::json!({
                "suite": "trust-wp",
                "backend": "unit-test",
                "status": "proved",
                "artifacts": vec![artifact.clone(); count],
            })
        };

        let exact: TransportProofEvidence =
            serde_json::from_value(proof_json(MAX_TRANSPORT_EVIDENCE_ARTIFACTS))
                .expect("the exact artifact-count limit must deserialize");
        assert_eq!(exact.artifacts.len(), MAX_TRANSPORT_EVIDENCE_ARTIFACTS);

        let error = serde_json::from_value::<TransportProofEvidence>(proof_json(
            MAX_TRANSPORT_EVIDENCE_ARTIFACTS + 1,
        ))
        .expect_err("an oversized evidence vector must fail during deserialization");
        assert!(error.to_string().contains("too many transport evidence artifacts"), "{error}");

        let programmatic = vec![
            TransportEvidenceArtifact {
                kind: "Report".into(),
                format: None,
                artifact_id: None,
                digest: None,
                uri: None,
                materialization: None,
                metadata: None,
            };
            MAX_TRANSPORT_EVIDENCE_ARTIFACTS + 1
        ];
        assert!(
            transport_proof_artifact_topology_defect("trust-wp", &programmatic, Some("obl-1"))
                .is_some_and(|defect| defect.contains("artifact safety limit")),
            "programmatically constructed evidence must obey the same work bound"
        );
    }

    #[test]
    fn trust_vc_certificate_uri_policy_has_live_saved_round_trip_parity() {
        let digest = "5555555555555555555555555555555555555555555555555555555555555555";
        let artifact = |uri: String| TransportEvidenceArtifact {
            kind: "ProofCertificate".into(),
            format: None,
            artifact_id: None,
            digest: Some(TransportArtifactDigest {
                algorithm: "sha256".into(),
                value: digest.into(),
            }),
            uri: Some(uri),
            materialization: None,
            metadata: None,
        };
        let exported_id = format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{digest}");
        for uri in [
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{digest}.json"),
            format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}.alethe"),
        ] {
            let live = artifact(uri);
            assert!(is_trust_vc_digest_bound_proof_certificate_artifact(&live));
            let saved: TransportEvidenceArtifact =
                serde_json::from_str(&serde_json::to_string(&live).expect("serialize certificate"))
                    .expect("restore certificate");
            assert!(is_trust_vc_digest_bound_proof_certificate_artifact(&saved));
        }

        for uri in [
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{digest}"),
            format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}"),
            format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}.json"),
            format!("{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{exported_id}.alethe?forged=1"),
        ] {
            let live = artifact(uri);
            assert!(!is_trust_vc_digest_bound_proof_certificate_artifact(&live));
            let saved: TransportEvidenceArtifact = serde_json::from_str(
                &serde_json::to_string(&live).expect("serialize rejected certificate"),
            )
            .expect("restore rejected certificate");
            assert!(!is_trust_vc_digest_bound_proof_certificate_artifact(&saved));
        }
    }

    #[test]
    fn sanitize_deserialized_preserves_summary_only_inconclusive_residuals() {
        let mut report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "x".into(),
                trust_version: "x".into(),
                timestamp: "x".into(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "c".into(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 1,
                total_obligations: 2,
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 2,
                total_timed_out: 1,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: vec![],
                verdict: CrateVerdict::Inconclusive,
            },
            functions: vec![FunctionProofReport {
                function: "crate::summary_only".into(),
                summary: FunctionSummary {
                    total_obligations: 2,
                    proved: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 2,
                    timed_out: 1,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 0,
                    max_proof_level: None,
                    verdict: FunctionVerdict::Inconclusive,
                },
                obligations: vec![],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };

        let sanitization = report.sanitize_deserialized();

        assert_eq!(sanitization.evidence_defects, 0);
        assert_eq!(report.functions[0].summary.total_obligations, 2);
        assert_eq!(report.functions[0].summary.proved, 0);
        assert_eq!(report.functions[0].summary.unknown, 2);
        assert_eq!(report.functions[0].summary.timed_out, 1);
        assert_eq!(report.summary.total_obligations, 2);
        assert_eq!(report.summary.total_unknown, 2);
        assert_eq!(report.summary.total_timed_out, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    }

    #[test]
    fn direct_zero_row_function_deserialization_keeps_unattributed_bad_news() {
        let function = FunctionProofReport {
            function: "crate::summary_only".into(),
            summary: FunctionSummary {
                total_obligations: 0,
                proved: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 2,
                total_time_ms: 0,
                max_proof_level: None,
                verdict: FunctionVerdict::NoObligations,
            },
            obligations: vec![],
        };

        let json = serde_json::to_vec(&function).expect("serialize zero-row function");
        let restored: FunctionProofReport =
            serde_json::from_slice(&json).expect("deserialize zero-row function");

        assert_eq!(restored.summary.total_obligations, 0);
        assert_eq!(restored.summary.unattributed_proved, 0);
        assert_eq!(restored.summary.unattributed_unknown, 2);
        assert_eq!(restored.summary.verdict, FunctionVerdict::Inconclusive);
    }

    #[test]
    fn full_saved_report_preserves_zero_row_unattributed_residuals_once() {
        let mut report = minimal_gate_report(None);
        report.functions.push(FunctionProofReport {
            function: "crate::summary_only".into(),
            summary: FunctionSummary {
                total_obligations: 0,
                proved: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 1,
                unattributed_unknown: 1,
                unattributed_proved: 1,
                total_time_ms: 0,
                max_proof_level: None,
                verdict: FunctionVerdict::NoObligations,
            },
            obligations: vec![],
        });
        // The crate fields conventionally repeat function aggregates, but can
        // also carry crate-only residuals. Each category has one of each here.
        report.summary.total_unattributed_failed = 2;
        report.summary.total_unattributed_unknown = 2;
        report.summary.total_unattributed_proved = 2;
        report.summary.verdict = CrateVerdict::NoObligations;

        let json = serde_json::to_vec(&report).expect("serialize zero-row report");
        let (restored, sanitization, claims) =
            JsonProofReport::decode_saved_json(&json, None).expect("decode zero-row report");

        assert_eq!(sanitization.downgraded_proved, 0);
        assert!(claims.obligations().is_empty());
        let function = &restored.functions[0];
        assert_eq!(function.summary.unattributed_failed, 1);
        assert_eq!(function.summary.unattributed_unknown, 2);
        assert_eq!(function.summary.unattributed_proved, 0);
        assert_eq!(function.summary.verdict, FunctionVerdict::HasViolations);
        assert_eq!(restored.summary.total_obligations, 0);
        assert_eq!(restored.summary.total_unattributed_failed, 2);
        assert_eq!(restored.summary.total_unattributed_unknown, 4);
        assert_eq!(restored.summary.total_unattributed_proved, 0);
        assert_eq!(restored.summary.functions_with_violations, 1);
        assert_eq!(restored.summary.verdict, CrateVerdict::HasViolations);
    }

    fn report_with_obligation(
        obligation: ObligationReport,
        reported_verdict: CrateVerdict,
    ) -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "x".into(),
                trust_version: "x".into(),
                timestamp: "x".into(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "c".into(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: usize::from(matches!(reported_verdict, CrateVerdict::Verified)),
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: usize::from(!matches!(
                    reported_verdict,
                    CrateVerdict::Verified
                )),
                total_obligations: 1,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: vec![],
                verdict: reported_verdict,
            },
            functions: vec![FunctionProofReport {
                function: "crate::checked".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 1,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 0,
                    max_proof_level: None,
                    verdict: FunctionVerdict::Verified,
                },
                obligations: vec![obligation],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        }
    }

    fn publication_grade_saved_obligation() -> ObligationReport {
        publication_grade_saved_obligation_with_identity(
            "obl-1",
            "1",
            "2",
            "ensures result is bounded",
        )
    }

    fn publication_grade_saved_obligation_with_identity(
        obligation_id: &str,
        request_id: &str,
        proof_id: &str,
        description: &str,
    ) -> ObligationReport {
        let strength = ProofStrength::deductive();
        let evidence = ProofEvidence::from(strength.clone());
        let native_id = format!("trust_ir-native-trust-wp-request-{request_id}-proof-{proof_id}");
        let native = TransportNativeTrustIrEvidence {
            suite: "trust-wp".into(),
            backend: "trust-wp".into(),
            request_id: Some(request_id.into()),
            native_id: Some(native_id.clone()),
            present: true,
            artifacts: native_shape_artifacts("trust-wp", request_id, proof_id),
            diagnostics: vec![],
        };
        let structural_input = bound_test_artifact(
            "NormalizedObligation",
            b"exact normalized proof input",
            &native_id,
            obligation_id,
            vec![],
        );
        let input_reference = TransportArtifactReference {
            kind: structural_input.kind.clone(),
            digest: structural_input.digest.clone().expect("structural input digest"),
        };
        let transcript = bound_test_artifact(
            "SolverTranscript",
            b"exact solver transcript",
            &native_id,
            obligation_id,
            vec![input_reference],
        );
        let transcript_reference = TransportArtifactReference {
            kind: transcript.kind.clone(),
            digest: transcript.digest.clone().expect("transcript digest"),
        };
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact proof-check report",
            &native_id,
            obligation_id,
            vec![transcript_reference],
        );
        let mut proof_artifacts = vec![structural_input, transcript, check];
        proof_artifacts.extend(native.artifacts.clone());
        let transport_proof = TransportProofEvidence {
            suite: "trust-wp".into(),
            backend: "trust-wp".into(),
            request_id: Some(request_id.into()),
            proof_id: Some(proof_id.into()),
            native_id: Some(native_id),
            status: TransportProofStatus::Proved,
            strength: Some(strength.clone()),
            evidence: Some(evidence.clone()),
            artifacts: proof_artifacts.clone(),
            diagnostics: vec![],
        };
        let proof_report = ObligationProofEvidenceReport {
            suite: Some(transport_proof.suite.clone()),
            backend: transport_proof.backend.clone(),
            request_id: transport_proof.request_id.clone(),
            proof_id: transport_proof.proof_id.clone(),
            native_id: transport_proof.native_id.clone(),
            status: Some(TransportProofStatus::Proved),
            provenance: ObligationEvidenceProvenanceReport::NativeBackend {
                verifier: transport_proof.backend.clone(),
            },
            strength: strength.clone(),
            evidence: evidence.clone(),
            proof_certificate: None,
            native_trust_ir: Some(native.clone()),
            artifacts: proof_artifacts,
            diagnostics: vec![],
            solver_warnings: None,
        };

        ObligationReport {
            obligation_id: Some(obligation_id.into()),
            description: description.into(),
            kind: "postcondition".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved { strength },
            solver: "trust-full-verifier".into(),
            time_ms: 3,
            evidence: Some(evidence),
            proof_evidence: Some(proof_report),
            transport_evidence: Some(ObligationTransportEvidenceReport {
                obligation_id: Some(obligation_id.into()),
                claim_digest_sha256: None,
                typed_kind: None,
                native_trust_ir: Some(native),
                proof_evidence: Some(transport_proof),
                monitor: None,
            }),
        }
    }

    fn clean_kernel_saved_obligation() -> ObligationReport {
        let obligation_id = "vc:demo__f:arithmetic_safety:0";
        let strength = ProofStrength::deductive();
        let evidence = ProofEvidence::from(strength.clone());
        let digest = "f".repeat(64);
        let proof_id = format!("clean-cic:v2:{digest}");
        let certificate = TransportEvidenceArtifact {
            kind: "clean_cic".into(),
            format: Some("trust-ir-cleancic-v2".into()),
            artifact_id: Some(proof_id.clone()),
            digest: Some(TransportArtifactDigest {
                algorithm: "sha256".into(),
                value: digest.clone(),
            }),
            uri: Some(format!("trust-certify://clean-cic/{digest}")),
            materialization: None,
            metadata: Some(serde_json::json!({ "CleanCic": { "term": [4, 1], "context": [9] } })),
        };
        let kernel_proof = ObligationProofEvidenceReport {
            suite: Some("trust-certify".into()),
            backend: "clean-kernel".into(),
            request_id: None,
            proof_id: Some(proof_id.clone()),
            native_id: None,
            status: Some(TransportProofStatus::Proved),
            provenance: ObligationEvidenceProvenanceReport::NativeBackend {
                verifier: "clean-kernel".into(),
            },
            strength: strength.clone(),
            evidence: evidence.clone(),
            proof_certificate: None,
            native_trust_ir: None,
            artifacts: vec![certificate.clone()],
            diagnostics: vec![],
            solver_warnings: None,
        };
        // The transport envelope's own proof_evidence mirrors the kernel proof;
        // it separately retains the ORIGINAL routed-dispatch bundle (trust-mc)
        // as provenance, which legitimately differs from the kernel authority.
        let transport_proof = TransportProofEvidence {
            suite: "trust-certify".into(),
            backend: "clean-kernel".into(),
            request_id: None,
            proof_id: Some(proof_id.clone()),
            native_id: None,
            status: TransportProofStatus::Proved,
            strength: Some(strength.clone()),
            evidence: Some(evidence.clone()),
            artifacts: vec![certificate],
            diagnostics: vec![],
        };
        let dispatch_bundle = TransportNativeTrustIrEvidence {
            suite: "trust-mc".into(),
            backend: "trust-mc".into(),
            request_id: Some("0".into()),
            native_id: Some("trust_ir-native-trust-mc-request-0-proof-1".into()),
            present: false,
            artifacts: vec![],
            diagnostics: vec![],
        };
        ObligationReport {
            obligation_id: Some(obligation_id.into()),
            description: "postcondition".into(),
            kind: "arithmetic_safety".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved { strength },
            solver: "trust-certify".into(),
            time_ms: 0,
            evidence: Some(evidence),
            proof_evidence: Some(kernel_proof),
            transport_evidence: Some(ObligationTransportEvidenceReport {
                obligation_id: Some(obligation_id.into()),
                claim_digest_sha256: None,
                typed_kind: None,
                native_trust_ir: Some(dispatch_bundle),
                proof_evidence: Some(transport_proof),
                monitor: None,
            }),
        }
    }

    #[test]
    fn clean_kernel_certified_proof_is_publication_grade_without_a_solver_bundle() {
        // A well-formed Clean-kernel certificate (proof_id + bound clean_cic
        // artifact + native-backend provenance) is publication-grade WITHOUT any
        // routed-solver request_id/native_id/native_trust_ir bundle.
        let obligation = clean_kernel_saved_obligation();
        assert_eq!(
            saved_obligation_structural_proof_defect(&obligation, None),
            None,
            "a well-formed clean-kernel certificate must be accepted as publication-grade"
        );

        // A kernel proof that smuggles a solver request_id is rejected, so it
        // cannot masquerade as a routed proof.
        let mut smuggled = clean_kernel_saved_obligation();
        smuggled.proof_evidence.as_mut().expect("proof").request_id = Some("0".into());
        assert!(
            saved_obligation_structural_proof_defect(&smuggled, None).is_some(),
            "a kernel proof carrying a solver request_id must be rejected"
        );

        // A certificate whose digest no longer reconstructs the proof_id/URI is
        // rejected: the content-addressed identity must be self-consistent.
        let mut unbound = clean_kernel_saved_obligation();
        unbound.proof_evidence.as_mut().expect("proof").artifacts[0].digest =
            Some(TransportArtifactDigest { algorithm: "sha256".into(), value: "a".repeat(64) });
        assert!(
            saved_obligation_structural_proof_defect(&unbound, None).is_some(),
            "a certificate digest that does not bind the proof_id must be rejected"
        );

        // A routed solver proof missing its native_trust_ir bundle must STILL
        // fail — the kernel lane must not rescue it (identity is pinned on
        // suite+backend+provenance, which a solver proof does not satisfy).
        let mut solver = publication_grade_saved_obligation();
        solver.proof_evidence.as_mut().expect("proof").native_trust_ir = None;
        assert!(
            saved_obligation_structural_proof_defect(&solver, None).is_some(),
            "a routed solver proof missing its native_trust_ir bundle must still fail"
        );
    }

    fn pdr_model_proof_artifacts() -> Vec<TransportEvidenceArtifact> {
        let mut artifacts =
            publication_grade_saved_obligation().proof_evidence.expect("proof evidence").artifacts;
        let transcript = artifacts
            .iter()
            .find(|artifact| normalized_artifact_kind(&artifact.kind) == "solver_transcript")
            .expect("solver transcript")
            .clone();
        let binding = transcript
            .materialization
            .as_ref()
            .expect("transcript materialization")
            .proof_binding_id
            .clone();
        let structural_references = transcript
            .materialization
            .as_ref()
            .expect("transcript materialization")
            .referenced_artifacts
            .clone();
        let transcript_reference = TransportArtifactReference {
            kind: transcript.kind.clone(),
            digest: transcript.digest.clone().expect("transcript digest"),
        };
        let model = bound_test_artifact(
            "Model",
            b"exact PDR invariant model",
            &binding,
            "obl-1",
            structural_references,
        );
        let model_reference = TransportArtifactReference {
            kind: model.kind.clone(),
            digest: model.digest.clone().expect("model digest"),
        };
        let replay = bound_test_artifact(
            "ReplayLog",
            b"exact replay over transcript and PDR invariant model",
            &binding,
            "obl-1",
            vec![transcript_reference.clone(), model_reference.clone()],
        );
        let replay_reference = TransportArtifactReference {
            kind: replay.kind.clone(),
            digest: replay.digest.clone().expect("replay digest"),
        };
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact check over transcript, PDR invariant model, and replay",
            &binding,
            "obl-1",
            vec![transcript_reference, model_reference, replay_reference],
        );
        let check_index = artifacts
            .iter()
            .position(|artifact| normalized_artifact_kind(&artifact.kind) == "proof_check_report")
            .expect("proof-check artifact");
        artifacts[check_index] = check;
        artifacts.push(model);
        artifacts.push(replay);
        artifacts
    }

    fn bound_test_artifact(
        kind: &str,
        payload: &[u8],
        binding: &str,
        owner: &str,
        references: Vec<TransportArtifactReference>,
    ) -> TransportEvidenceArtifact {
        let mut bytes = EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC.to_vec();
        push_test_binding_field(&mut bytes, kind.as_bytes());
        push_test_binding_field(&mut bytes, owner.as_bytes());
        push_test_binding_field(&mut bytes, binding.as_bytes());
        bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
        for reference in &references {
            push_test_binding_field(&mut bytes, reference.kind.as_bytes());
            push_test_binding_field(&mut bytes, reference.digest.algorithm.as_bytes());
            push_test_binding_field(&mut bytes, reference.digest.value.as_bytes());
        }
        bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
        bytes.extend_from_slice(payload);
        let digest = lowercase_transport_hex(&Sha256::digest(&bytes));
        TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("binary".into()),
            artifact_id: Some(kind.into()),
            digest: Some(TransportArtifactDigest {
                algorithm: "sha256".into(),
                value: digest.clone(),
            }),
            uri: Some(format!("artifact://test/{kind}/{digest}")),
            materialization: Some(
                TransportArtifactMaterialization::from_exact_bytes(&bytes, binding, references)
                    .expect("valid test materialization"),
            ),
            metadata: None,
        }
    }

    fn externalize_test_artifact(root: &Path, artifact: &mut TransportEvidenceArtifact) {
        let digest = artifact.digest.as_ref().expect("artifact digest").clone();
        let materialization = artifact.materialization.take().expect("artifact materialization");
        let bytes = materialization.decoded_bytes().expect("inline artifact bytes");
        let store = root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        std::fs::create_dir_all(&store).expect("create test proof store");
        std::fs::write(store.join(&digest.value), bytes).expect("write test proof artifact");
        artifact.materialization = Some(
            materialization
                .with_materialized_path(format!(
                    "{}/sha256/{}",
                    TRANSPORT_ARTIFACT_STORE_DIRECTORY, digest.value
                ))
                .expect("valid test path materialization"),
        );
    }

    fn push_test_binding_field(bytes: &mut Vec<u8>, value: &[u8]) {
        bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
        bytes.extend_from_slice(value);
    }

    fn native_shape_artifacts(
        suite: &str,
        request_id: &str,
        proof_id: &str,
    ) -> Vec<TransportEvidenceArtifact> {
        let native_id = format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
        let bundle = native_test_materialization(
            "bundle",
            None,
            None,
            None,
            serde_json::json!({"bundle": "exact"}),
            &native_id,
            vec![],
        );
        let bundle_digest = bundle.1.value.clone();
        let bundle_uri = format!("trust_ir-native://verification-bundle/{bundle_digest}");
        let request = native_test_materialization(
            "request",
            Some(suite),
            Some(request_id),
            None,
            serde_json::json!({"request": "exact"}),
            &native_id,
            vec![TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: bundle.1.clone(),
            }],
        );
        let request_digest = request.1.value.clone();
        let normalized = native_test_materialization(
            "normalized_obligation",
            Some(suite),
            Some(request_id),
            Some(proof_id),
            serde_json::json!({"obligation": "exact"}),
            &native_id,
            vec![TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: request.1.clone(),
            }],
        );
        vec![
            native_test_artifact("EngineInput", bundle, bundle_uri.clone()),
            native_test_artifact(
                "EngineInput",
                request,
                format!("{bundle_uri}/{suite}/request/{request_id}/{request_digest}"),
            ),
            native_test_artifact(
                "NormalizedObligation",
                normalized.clone(),
                format!(
                    "{bundle_uri}/{suite}/request/{request_id}/{request_digest}/proof/{proof_id}/{}",
                    normalized.1.value
                ),
            ),
        ]
    }

    fn native_test_materialization(
        role: &str,
        suite: Option<&str>,
        request_id: Option<&str>,
        proof_id: Option<&str>,
        payload: serde_json::Value,
        native_id: &str,
        references: Vec<TransportArtifactReference>,
    ) -> (TransportArtifactMaterialization, TransportArtifactDigest) {
        let mut value = serde_json::json!({
            "schema": NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
            "role": role,
            "suite": suite,
            "request_id": request_id,
            "proof_id": proof_id,
            "payload": payload,
        });
        crate::digest::canonicalize_json_in_place(&mut value);
        let bytes = serde_json::to_vec(&value).expect("serialize native materialization");
        let digest = TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: lowercase_transport_hex(&Sha256::digest(&bytes)),
        };
        (
            TransportArtifactMaterialization::from_exact_bytes(&bytes, native_id, references)
                .expect("valid native materialization"),
            digest,
        )
    }

    fn native_test_artifact(
        kind: &str,
        materialized: (TransportArtifactMaterialization, TransportArtifactDigest),
        uri: String,
    ) -> TransportEvidenceArtifact {
        TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("trust_ir-json".into()),
            artifact_id: None,
            digest: Some(materialized.1),
            uri: Some(uri),
            materialization: Some(materialized.0),
            metadata: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 7, counterexample: None }
    }

    fn unknown_result() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 11,
            reason: "incomplete quantifier reasoning".into(),
        }
    }

    fn timeout_result() -> VerificationResult {
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 250 }
    }

    fn proved_with(strength: ProofStrength) -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength,
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    #[test]
    fn honest_smt_unsat_constructors_carry_distinct_assurance() {
        assert_eq!(ProofStrength::smt_unsat_unvalidated().assurance, AssuranceLevel::Unchecked);
        assert_eq!(ProofStrength::smt_unsat_strict_checked().assurance, AssuranceLevel::SmtBacked);
        assert_eq!(ProofStrength::smt_unsat_certified().assurance, AssuranceLevel::Certified);
        // The honest unchecked verdict ranks strictly below a strict-checked one,
        // which ranks strictly below a kernel-certified (true-proof) one.
        assert!(
            AssuranceLevel::Unchecked.strength_order() < AssuranceLevel::SmtBacked.strength_order()
        );
        assert!(
            AssuranceLevel::SmtBacked.strength_order() < AssuranceLevel::Certified.strength_order()
        );
    }

    #[test]
    fn reporting_floor_predicate_pins_per_level_semantics() {
        // R-U Phase B: the named floor is exactly `>= SmtBacked` in strength order.
        assert!(!AssuranceLevel::Unchecked.meets_reporting_floor());
        assert!(!AssuranceLevel::Heuristic.meets_reporting_floor());
        assert!(!AssuranceLevel::Trusted.meets_reporting_floor());
        assert!(!AssuranceLevel::BoundedSound { depth: 64 }.meets_reporting_floor());
        assert!(AssuranceLevel::SmtBacked.meets_reporting_floor());
        assert!(AssuranceLevel::Sound.meets_reporting_floor());
        assert!(AssuranceLevel::Certified.meets_reporting_floor());
    }

    #[test]
    fn reusable_predicate_is_match_based_not_order_based() {
        // R-U Phase B: fact/summary reusability admits Sound|Certified EXACTLY —
        // SmtBacked meets the reporting floor but must NOT mint reusable facts.
        let sound = ProofStrength::deductive();
        assert!(sound.is_reusable_complete_unbounded());
        let smt = ProofStrength::smt_unsat_strict_checked();
        assert!(smt.assurance.meets_reporting_floor());
        assert!(!smt.is_reusable_complete_unbounded());
        let bounded = ProofStrength::bounded(64);
        assert!(!bounded.is_reusable_complete_unbounded());
    }

    #[test]
    fn require_assurance_downgrades_unchecked_proved_to_unknown() {
        // An unvalidated solver "unsat" (the incremental_ay subprocess path) must
        // NOT survive a boundary that requires a strict-checked proof: a buggy
        // solver-core UNSAT cannot be reported as proof.
        let unchecked = proved_with(ProofStrength::smt_unsat_unvalidated());
        let gated = unchecked.require_assurance(AssuranceLevel::SmtBacked);
        assert!(!gated.is_proved(), "unchecked Proved must be downgraded");
        match gated {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("below required"), "reason: {reason}");
            }
            other => panic!("expected Unknown, got {other:?}"),
        }
    }

    #[test]
    fn require_assurance_keeps_strict_checked_proof() {
        let checked = proved_with(ProofStrength::smt_unsat_strict_checked());
        let gated = checked.require_assurance(AssuranceLevel::SmtBacked);
        assert!(gated.is_proved(), "strict-checked Proved meets the SmtBacked bar");
    }

    #[test]
    fn require_certified_demands_kernel_true_proof() {
        // Requiring Certified (kernel-checked true proof) downgrades everything
        // weaker -- including the legacy Sound and the strict-checked SmtBacked.
        assert!(
            !proved_with(ProofStrength::smt_unsat())
                .require_assurance(AssuranceLevel::Certified)
                .is_proved(),
            "legacy Sound is below kernel-Certified"
        );
        assert!(
            !proved_with(ProofStrength::smt_unsat_strict_checked())
                .require_assurance(AssuranceLevel::Certified)
                .is_proved(),
            "SmtBacked is below kernel-Certified"
        );
        assert!(
            proved_with(ProofStrength::smt_unsat_certified())
                .require_assurance(AssuranceLevel::Certified)
                .is_proved(),
            "kernel-Certified meets the bar"
        );
    }

    #[test]
    fn require_assurance_passes_non_proved_through_unchanged() {
        // The gate only ever weakens a Proved; it never alters Failed/Unknown/Timeout.
        assert!(matches!(
            failed_result().require_assurance(AssuranceLevel::Certified),
            VerificationResult::Failed { .. }
        ));
        assert!(matches!(
            unknown_result().require_assurance(AssuranceLevel::Certified),
            VerificationResult::Unknown { .. }
        ));
        assert!(matches!(
            timeout_result().require_assurance(AssuranceLevel::Certified),
            VerificationResult::Timeout { .. }
        ));
    }

    // Trust: classification mapping for the per-compile Trust Surface. Locks the
    // assurance -> bucket split so a weak `Proved` can never be counted as a
    // certified or smt-backed proof.
    fn surface_obligation(outcome: ObligationOutcome) -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "d".into(),
            kind: "k".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome,
            solver: "ay".into(),
            time_ms: 1,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn proved_outcome(assurance: AssuranceLevel) -> ObligationOutcome {
        ObligationOutcome::Proved {
            strength: ProofStrength { reasoning: ReasoningKind::Smt, assurance },
        }
    }

    #[test]
    fn trust_surface_classifies_by_assurance_not_a_blended_total() {
        let obligations = vec![
            surface_obligation(proved_outcome(AssuranceLevel::Certified)),
            surface_obligation(proved_outcome(AssuranceLevel::SmtBacked)),
            surface_obligation(proved_outcome(AssuranceLevel::Sound)),
            surface_obligation(proved_outcome(AssuranceLevel::Trusted)),
            surface_obligation(proved_outcome(AssuranceLevel::BoundedSound { depth: 8 })),
            surface_obligation(proved_outcome(AssuranceLevel::Unchecked)),
            surface_obligation(proved_outcome(AssuranceLevel::Heuristic)),
            surface_obligation(ObligationOutcome::RuntimeChecked { note: None }),
            surface_obligation(ObligationOutcome::Unknown { reason: "x".into() }),
            surface_obligation(ObligationOutcome::Timeout { timeout_ms: 5 }),
            surface_obligation(ObligationOutcome::Failed { counterexample: None }),
            surface_obligation(ObligationOutcome::DesignRequirement { detail: "x".into() }),
        ];
        let func = FunctionProofReport {
            function: "f".into(),
            summary: FunctionSummary {
                total_obligations: obligations.len(),
                proved: 7,
                runtime_checked: 1,
                failed: 1,
                unknown: 2,
                timed_out: 1,
                design_requirements: 1,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 0,
                max_proof_level: None,
                verdict: FunctionVerdict::HasViolations,
            },
            obligations,
        };
        let surface = TrustSurface::from_functions(std::slice::from_ref(&func));
        assert_eq!(surface.certified, 1);
        assert_eq!(surface.smt_backed, 2, "SmtBacked + legacy Sound");
        assert_eq!(surface.contract_assumed, 2, "Trusted + BoundedSound");
        assert_eq!(surface.fully_trusted, 2, "Unchecked + Heuristic");
        assert_eq!(surface.runtime_checked, 1);
        assert_eq!(surface.unknown, 2, "Unknown + Timeout");
        assert_eq!(surface.failed, 1);
        // A design mandate is not a proof outcome and is counted in no bucket.
        assert_eq!(surface.additionally_proved(), 3, "only certified + smt-backed");
        assert_eq!(surface.assumed_or_trusted(), 4);
        // Every classified row is accounted for; the design mandate is excluded.
        assert_eq!(surface.total_obligations, 11);
    }

    #[test]
    fn test_counterexample_display() {
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let s = cex.to_string();
        assert!(s.contains("a = 18446744073709551615"));
        assert!(s.contains("b = 1"));
    }

    #[test]
    fn test_result_accessors() {
        let proved = VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert!(proved.is_proved());
        assert!(!proved.is_failed());
        assert_eq!(proved.solver_name(), "ay");
        assert_eq!(proved.time_ms(), 5);
    }

    #[test]
    fn memory_guard_unknown_is_classified_as_release_blocking_proof_gap() {
        let result = VerificationResult::Unknown {
            solver: "memory-guard".into(),
            time_ms: 0,
            reason: "memory limit exceeded: 2048MB used, 1024MB limit (peak: 2048MB) - skipping solver dispatch".to_string(),
        };

        assert!(result.is_memory_guard_solver_skip());
        let reason = result
            .release_blocking_proof_gap_reason()
            .expect("memory guard skip should be a release-blocking proof gap");
        assert!(reason.contains("release-blocking proof gap"));
        assert!(reason.contains("memory guard skipped solver dispatch"));
    }

    #[test]
    fn test_classify_runtime_disposition_auto() {
        let overflow_vc = arithmetic_overflow_vc();
        let no_fallback_vc = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &proved_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Proved
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &failed_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: overflow_vc.description() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: overflow_vc.description() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                false,
            ),
            RuntimeDisposition::Unknown { reason: "incomplete quantifier reasoning".into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &overflow_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                false,
            ),
            RuntimeDisposition::Timeout { timeout_ms: 250 }
        );
        assert_eq!(
            classify_runtime_disposition(
                &no_fallback_vc,
                &unknown_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Unknown { reason: "incomplete quantifier reasoning".into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &no_fallback_vc,
                &timeout_result(),
                RuntimeCheckPolicy::Auto,
                true,
            ),
            RuntimeDisposition::Timeout { timeout_ms: 250 }
        );
    }

    #[test]
    fn test_classify_runtime_disposition_force_static() {
        let vc_kind = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &proved_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::Proved
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &failed_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &unknown_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::CompileError {
                reason: "`#[trust(static)]` requires a static proof, but the solver returned unknown: incomplete quantifier reasoning".into(),
            }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &timeout_result(),
                RuntimeCheckPolicy::ForceStatic,
                true,
            ),
            RuntimeDisposition::CompileError {
                reason: "`#[trust(static)]` requires a static proof, but verification timed out after 250ms".into(),
            }
        );
    }

    #[test]
    fn test_classify_runtime_disposition_force_runtime() {
        let vc_kind = no_runtime_fallback_vc();

        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &proved_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &failed_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::Failed
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &unknown_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
        assert_eq!(
            classify_runtime_disposition(
                &vc_kind,
                &timeout_result(),
                RuntimeCheckPolicy::ForceRuntime,
                true,
            ),
            RuntimeDisposition::RuntimeChecked { note: FORCED_RUNTIME_NOTE.into() }
        );
    }

    // -----------------------------------------------------------------------
    // CrateVerificationResult tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_crate_verification_result_empty() {
        let result = CrateVerificationResult::new("empty_crate");
        assert_eq!(result.crate_name, "empty_crate");
        assert_eq!(result.function_count(), 0);
        assert_eq!(result.total_obligations(), 0);
        assert!(result.all_results().is_empty());
        assert_eq!(result.total_from_notes, 0);
        assert_eq!(result.total_with_assumptions, 0);
    }

    #[test]
    fn test_crate_verification_result_add_functions() {
        let mut crate_result = CrateVerificationResult::new("multi_fn");

        let func1 = FunctionVerificationResult {
            function_path: "crate::safe_div".to_string(),
            function_name: "safe_div".to_string(),
            results: vec![(
                crate::VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "safe_div".into(),
                    location: crate::SourceSpan::default(),
                    formula: crate::Formula::Bool(false),
                    contract_metadata: None,
                },
                proved_result(),
            )],
            from_notes: 1,
            with_assumptions: 0,
        };

        let func2 = FunctionVerificationResult {
            function_path: "crate::checked_add".to_string(),
            function_name: "checked_add".to_string(),
            results: vec![
                (
                    crate::VerificationCondition {
                        kind: arithmetic_overflow_vc(),
                        function: "checked_add".into(),
                        location: crate::SourceSpan::default(),
                        formula: crate::Formula::Bool(true),
                        contract_metadata: None,
                    },
                    failed_result(),
                ),
                (
                    crate::VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: "checked_add".into(),
                        location: crate::SourceSpan::default(),
                        formula: crate::Formula::Bool(false),
                        contract_metadata: None,
                    },
                    proved_result(),
                ),
            ],
            from_notes: 0,
            with_assumptions: 2,
        };

        crate_result.add_function(func1);
        crate_result.add_function(func2);

        assert_eq!(crate_result.function_count(), 2);
        assert_eq!(crate_result.total_obligations(), 3);
        assert_eq!(crate_result.total_from_notes, 1);
        assert_eq!(crate_result.total_with_assumptions, 2);

        let all = crate_result.all_results();
        assert_eq!(all.len(), 3);
        assert_eq!(all[0].0.function, "safe_div");
        assert_eq!(all[1].0.function, "checked_add");
        assert_eq!(all[2].0.function, "checked_add");
    }

    #[test]
    fn test_crate_verification_result_serialization_roundtrip() {
        let mut crate_result = CrateVerificationResult::new("roundtrip");
        crate_result.add_function(FunctionVerificationResult {
            function_path: "crate::f".to_string(),
            function_name: "f".to_string(),
            results: vec![(
                crate::VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f".into(),
                    location: crate::SourceSpan::default(),
                    formula: crate::Formula::Bool(false),
                    contract_metadata: None,
                },
                proved_result(),
            )],
            from_notes: 0,
            with_assumptions: 0,
        });

        let json = serde_json::to_string(&crate_result).expect("serialize");
        let deserialized: CrateVerificationResult =
            serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized.crate_name, "roundtrip");
        assert_eq!(deserialized.function_count(), 1);
        assert_eq!(deserialized.total_obligations(), 1);
    }

    #[test]
    fn test_json_proof_report_deserializes_without_hardened_context() {
        let json = r#"{
            "metadata": {
                "schema_version": "trust.report.v1",
                "trust_version": "0.1.0",
                "timestamp": "2026-04-30T00:00:00Z",
                "total_time_ms": 0
            },
            "crate_name": "legacy",
            "summary": {
                "functions_analyzed": 0,
                "functions_verified": 0,
                "functions_with_violations": 0,
                "functions_inconclusive": 0,
                "total_obligations": 0,
                "total_proved": 0,
                "total_failed": 0,
                "total_unknown": 0,
                "verdict": "NoObligations"
            },
            "functions": []
        }"#;

        let report: JsonProofReport =
            serde_json::from_str(json).expect("legacy report should deserialize");
        assert!(report.hardened.is_none());

        let value = serde_json::to_value(&report).expect("serialize legacy report");
        assert!(value.get("hardened").is_none());
    }

    #[test]
    fn test_json_proof_report_hardened_context_roundtrip() {
        let report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "trust.report.v1".to_string(),
                trust_version: "0.1.0".to_string(),
                timestamp: "2026-04-30T00:00:00Z".to_string(),
                total_time_ms: 4,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "hardened".to_string(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: CrateVerdict::Verified,
            },
            functions: Vec::new(),
            hardened: Some(HardenedReportContext {
                profile: Some(HardenedProfileReport {
                    name: Some("unix_hardened".to_string()),
                    version: Some("2026.04".to_string()),
                    enabled_categories: vec!["byte_loss".to_string(), "raw_path_api".to_string()],
                }),
                assurance: Some(HardenedAssuranceReport {
                    level: Some("proof_backed".to_string()),
                    model: Some("unix_fs_process".to_string()),
                    proof_evidence_policy: Some(
                        "proof_evidence role links to obligations".to_string(),
                    ),
                    proof_evidence_required: true,
                }),
                summary: Some(HardenedSummaryReport {
                    hardened_obligations: 1,
                    proved_hardened_obligations: 1,
                    inventory_entries: 1,
                    model_assumptions: 1,
                    proof_evidence_entries: 1,
                }),
                boundary_inventory: vec![
                    HardenedBoundaryInventoryEntry {
                        id: Some("inv-1".to_string()),
                        role: HardenedBoundaryInventoryRole::Inventory,
                        category: "raw_path_api".to_string(),
                        boundary: "std::fs::rename".to_string(),
                        function: Some("crate::mv".to_string()),
                        description: Some("name-based rename boundary".to_string()),
                        location: None,
                        obligation_id: None,
                        proof_evidence_id: None,
                        source: Some("trust_vcgen".to_string()),
                    },
                    HardenedBoundaryInventoryEntry {
                        id: Some("model-1".to_string()),
                        role: HardenedBoundaryInventoryRole::ModelAssumption,
                        category: "path_identity".to_string(),
                        boundary: "same_device_rename".to_string(),
                        function: None,
                        description: Some(
                            "source and destination stay on one filesystem".to_string(),
                        ),
                        location: None,
                        obligation_id: Some("crate::mv#vc0".to_string()),
                        proof_evidence_id: None,
                        source: Some("unix-model".to_string()),
                    },
                    HardenedBoundaryInventoryEntry {
                        id: Some("proof-1".to_string()),
                        role: HardenedBoundaryInventoryRole::ProofEvidence,
                        category: "byte_loss".to_string(),
                        boundary: "Path::as_os_str".to_string(),
                        function: Some("crate::render".to_string()),
                        description: Some("byte-exact path rendering proof".to_string()),
                        location: None,
                        obligation_id: Some("crate::render#vc0".to_string()),
                        proof_evidence_id: Some("proof:render:byte_loss".to_string()),
                        source: Some("ay".to_string()),
                    },
                ],
            }),
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };

        let value = serde_json::to_value(&report).expect("serialize hardened report");
        assert_eq!(value["hardened"]["profile"]["name"], "unix_hardened");
        assert_eq!(value["hardened"]["boundary_inventory"][0]["role"], "inventory");
        assert_eq!(value["hardened"]["boundary_inventory"][1]["role"], "model_assumption");
        assert_eq!(value["hardened"]["boundary_inventory"][2]["role"], "proof_evidence");

        let parsed: JsonProofReport =
            serde_json::from_value(value).expect("deserialize hardened report");
        let hardened = parsed.hardened.expect("hardened context should roundtrip");
        assert_eq!(hardened.boundary_inventory.len(), 2);
        assert_eq!(
            hardened.boundary_inventory[1].role,
            HardenedBoundaryInventoryRole::ModelAssumption
        );
        assert_eq!(
            hardened.assurance.as_ref().and_then(|assurance| assurance.level.as_deref()),
            Some("inventory_only")
        );
        let summary = hardened.summary.expect("hardened summary");
        assert_eq!(summary.proved_hardened_obligations, 0);
        assert_eq!(summary.proof_evidence_entries, 0);
    }

    // -----------------------------------------------------------------------
    // ProofEvidence, ReasoningKind, AssuranceLevel tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_reasoning_kind_is_complete_smt() {
        assert!(ReasoningKind::Smt.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_bounded_model_check_false() {
        assert!(!ReasoningKind::BoundedModelCheck { depth: 50 }.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_exhaustive_finite() {
        assert!(ReasoningKind::ExhaustiveFinite(1024).is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_inductive() {
        assert!(ReasoningKind::Inductive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_deductive() {
        assert!(ReasoningKind::Deductive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_constructive() {
        assert!(ReasoningKind::Constructive.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_pdr() {
        assert!(ReasoningKind::Pdr.is_complete());
    }

    #[test]
    fn test_reasoning_kind_is_complete_abstract_interpretation() {
        assert!(ReasoningKind::AbstractInterpretation.is_complete());
    }

    #[test]
    fn test_assurance_level_strength_order() {
        assert_eq!(AssuranceLevel::Unchecked.strength_order(), 0);
        assert_eq!(AssuranceLevel::Heuristic.strength_order(), 0);
        assert_eq!(AssuranceLevel::Trusted.strength_order(), 1);
        assert_eq!(AssuranceLevel::BoundedSound { depth: 10 }.strength_order(), 1);
        assert_eq!(AssuranceLevel::SmtBacked.strength_order(), 2);
        assert_eq!(AssuranceLevel::Sound.strength_order(), 2);
        assert_eq!(AssuranceLevel::Certified.strength_order(), 3);
    }

    #[test]
    fn test_assurance_level_strength_monotonic() {
        // Certified > SmtBacked/Sound > Trusted/BoundedSound > Unchecked/Heuristic
        assert!(
            AssuranceLevel::Certified.strength_order() > AssuranceLevel::SmtBacked.strength_order()
        );
        assert!(
            AssuranceLevel::SmtBacked.strength_order() > AssuranceLevel::Trusted.strength_order()
        );
        assert!(
            AssuranceLevel::Trusted.strength_order() > AssuranceLevel::Unchecked.strength_order()
        );
    }

    #[test]
    fn test_proof_evidence_new() {
        let ev = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        assert_eq!(ev.reasoning, ReasoningKind::Smt);
        assert_eq!(ev.assurance, AssuranceLevel::Certified);
    }

    #[test]
    fn test_proof_evidence_is_certified() {
        let certified = ProofEvidence::new(ReasoningKind::Constructive, AssuranceLevel::Certified);
        assert!(certified.is_certified());
        let unchecked = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Unchecked);
        assert!(!unchecked.is_certified());
    }

    #[test]
    fn test_proof_evidence_is_bounded() {
        let bmc = ProofEvidence::new(
            ReasoningKind::BoundedModelCheck { depth: 50 },
            AssuranceLevel::Trusted,
        );
        assert!(bmc.is_bounded());
        let smt = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::SmtBacked);
        assert!(!smt.is_bounded());
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_smt_unsat() {
        let ps = ProofStrength::smt_unsat();
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Smt);
        assert_eq!(ev.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_bounded() {
        let ps = ProofStrength::bounded(42);
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::BoundedModelCheck { depth: 42 });
        assert_eq!(ev.assurance, AssuranceLevel::BoundedSound { depth: 42 });
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_inductive() {
        let ps = ProofStrength::inductive();
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Inductive);
        assert_eq!(ev.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_from_proof_strength_heuristic() {
        let ps = ProofStrength {
            reasoning: ReasoningKind::Deductive,
            assurance: AssuranceLevel::Heuristic,
        };
        let ev: ProofEvidence = ps.into();
        assert_eq!(ev.reasoning, ReasoningKind::Deductive);
        assert_eq!(ev.assurance, AssuranceLevel::Unchecked);
    }

    #[test]
    fn test_proof_evidence_serde_roundtrip() {
        let ev =
            ProofEvidence::new(ReasoningKind::ExhaustiveFinite(256), AssuranceLevel::Certified);
        let json = serde_json::to_string(&ev).expect("serialize ProofEvidence");
        let deserialized: ProofEvidence =
            serde_json::from_str(&json).expect("deserialize ProofEvidence");
        assert_eq!(ev, deserialized);
    }

    #[test]
    fn test_proof_evidence_hash_consistency() {
        use crate::fx::FxHashSet;
        let ev1 = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        let ev2 = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        let mut set = FxHashSet::default();
        set.insert(ev1.clone());
        set.insert(ev2);
        assert_eq!(set.len(), 1, "equal ProofEvidence values must hash the same");
    }

    #[test]
    fn test_bounded_model_check_never_certified_invariant() {
        // This is the core soundness property from #190: bounded reasoning
        // must never silently become certified.
        let ev = ProofEvidence::new(
            ReasoningKind::BoundedModelCheck { depth: 100 },
            AssuranceLevel::Certified,
        );
        // The type system allows construction (for flexibility), but
        // `is_bounded()` remains true, enabling callers to enforce the rule.
        assert!(ev.is_bounded());
        assert!(ev.is_certified());
        // The correct check pattern:
        // if evidence.is_bounded() && evidence.is_certified() { reject }
    }

    // -----------------------------------------------------------------------
    // Transport message tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transport_message_function_result_roundtrip() {
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::safe_div".to_string(),
            package_name: Some("pkg".to_string()),
            crate_name: Some("crate".to_string()),
            primary_package: true,
            verification_session: "session-1".to_string(),
            results: vec![TransportObligationResult {
                obligation_id: None,
                claim_digest_sha256: None,
                kind: "divzero".to_string(),
                typed_kind: None,
                description: "division by zero".to_string(),
                location: None,
                outcome: Outcome::Proved,
                solver: "ay-smtlib".into(),
                time_ms: 5,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                native_trust_ir: None,
                proof_evidence: None,
                monitor: None,
            }],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
        let json = serde_json::to_string(&msg).expect("serialize");
        let parsed = parse_transport_payload(&json).expect("deserialize");
        match parsed {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.function, "crate::safe_div");
                assert_eq!(r.results.len(), 1);
                assert_eq!(r.proved, 1);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_transport_message_preserves_exact_typed_temporal_kind() {
        let typed_kind = VcKind::Temporal {
            property: "AG(request -> AF response)".to_string(),
            machine: Some(StateMachineMetadata {
                states: vec!["idle".to_string(), "pending".to_string()],
                init_states: vec![0],
                transitions: vec![(0, "request".to_string(), 1), (1, "response".to_string(), 0)],
                labels: [(0, vec!["idle".to_string()]), (1, vec!["pending".to_string()])]
                    .into_iter()
                    .collect(),
            }),
        };
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::protocol".to_string(),
            package_name: Some("pkg".to_string()),
            crate_name: Some("crate".to_string()),
            primary_package: true,
            verification_session: "session-temporal".to_string(),
            results: vec![TransportObligationResult {
                obligation_id: Some("crate::protocol#vc0".to_string()),
                claim_digest_sha256: None,
                kind: typed_kind.transport_tag().to_string(),
                typed_kind: Some(Box::new(typed_kind.clone())),
                description: typed_kind.description(),
                location: None,
                outcome: Outcome::Unknown,
                solver: "ty".to_string(),
                time_ms: 7,
                counterexample: None,
                counterexample_model: None,
                reason: Some("transport roundtrip".to_string()),
                design_mandate: false,
                native_trust_ir: None,
                proof_evidence: None,
                monitor: None,
            }],
            proved: 0,
            failed: 0,
            unknown: 1,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });

        let json = serde_json::to_string(&msg).expect("serialize exact typed temporal transport");
        let parsed =
            parse_transport_payload(&json).expect("deserialize exact typed temporal transport");
        let TransportMessage::FunctionResult(parsed) = parsed else {
            panic!("expected FunctionResult")
        };
        assert_eq!(parsed.results[0].kind, "temporal");
        assert_eq!(parsed.results[0].typed_kind.as_deref(), Some(&typed_kind));
        assert_eq!(parsed.results[0].description, typed_kind.description());
    }

    #[test]
    fn test_transport_obligation_result_deserializes_old_json_without_evidence() {
        let json = r#"{
            "kind": "divzero",
            "description": "division by zero",
            "outcome": "proved",
            "solver": "ay-smtlib",
            "time_ms": 5
        }"#;

        let parsed: TransportObligationResult =
            serde_json::from_str(json).expect("old transport JSON should deserialize");

        assert_eq!(parsed.kind, "divzero");
        assert_eq!(parsed.description, "division by zero");
        assert_eq!(parsed.outcome, Outcome::Proved);
        assert_eq!(parsed.solver, "ay-smtlib");
        assert_eq!(parsed.time_ms, 5);
        assert_eq!(parsed.obligation_id, None);
        assert_eq!(parsed.claim_digest_sha256, None);
        assert_eq!(parsed.typed_kind, None);
        assert!(!parsed.design_mandate);
        assert_eq!(parsed.native_trust_ir, None);
        assert_eq!(parsed.proof_evidence, None);
        assert_eq!(parsed.monitor, None);
    }

    /// A saved transport row written before the outcome field was typed spells
    /// its outcomes exactly as this producer wrote them, and one of those
    /// spellings (`timed_out`) is the aggregate-bucket name the summary rows use
    /// rather than the row spelling. Reading must accept both; writing must only
    /// ever produce the canonical one, so re-serializing a stored report cannot
    /// mint a third spelling.
    #[test]
    fn transport_rows_read_legacy_outcome_spellings_and_write_the_canonical_one() {
        for (stored, expected) in [
            ("proved", Outcome::Proved),
            ("failed", Outcome::Failed),
            ("unknown", Outcome::Unknown),
            ("timeout", Outcome::Timeout),
            ("timed_out", Outcome::Timeout),
            ("runtime_checked", Outcome::RuntimeChecked),
            ("skipped", Outcome::Skipped),
        ] {
            let json = format!(
                r#"{{"kind":"divzero","description":"d","outcome":"{stored}","solver":"ay","time_ms":1}}"#
            );
            let parsed: TransportObligationResult =
                serde_json::from_str(&json).unwrap_or_else(|error| {
                    panic!("stored spelling `{stored}` must still deserialize: {error}")
                });
            assert_eq!(parsed.outcome, expected, "stored spelling `{stored}`");

            let rewritten = serde_json::to_value(&parsed).expect("serialize transport row");
            assert_eq!(
                rewritten["outcome"].as_str(),
                Some(expected.as_str()),
                "stored spelling `{stored}` must be rewritten canonically"
            );
        }
    }

    /// A spelling neither side of the protocol agreed on is a protocol defect,
    /// not a row to classify. Refusing the whole payload routes the run into
    /// targo's parse-failure path, which publishes nothing favorable.
    #[test]
    fn transport_rows_refuse_an_outcome_no_producer_writes() {
        let json = r#"{"kind":"divzero","description":"d","outcome":"prooved","solver":"ay","time_ms":1}"#;
        assert!(serde_json::from_str::<TransportObligationResult>(json).is_err());
    }

    /// The report DTO and the transport row are two encodings of one decision.
    /// They must agree on the name of that decision, or a reader correlating a
    /// stored report against a transport line silently compares two different
    /// vocabularies.
    #[test]
    fn report_obligations_and_transport_rows_name_outcomes_identically() {
        for obligation in [
            ObligationOutcome::Proved { strength: ProofStrength::deductive() },
            ObligationOutcome::Failed { counterexample: None },
            ObligationOutcome::Unknown { reason: "r".to_string() },
            ObligationOutcome::RuntimeChecked { note: None },
            ObligationOutcome::Timeout { timeout_ms: 1 },
        ] {
            let serialized =
                serde_json::to_value(&obligation).expect("serialize report obligation");
            let tag = serialized["status"].as_str().expect("report obligations carry a status tag");
            assert_eq!(
                tag,
                Outcome::from(&obligation).as_str(),
                "report and transport spellings diverged for {obligation:?}"
            );
        }
    }

    /// The two evidence-status directions must compose to the identity on the
    /// statuses transport can express, or a row that survives a round trip
    /// through the shared vocabulary comes back meaning something else.
    #[test]
    fn transport_proof_status_survives_a_round_trip_through_the_shared_outcome() {
        for status in [
            TransportProofStatus::Proved,
            TransportProofStatus::Failed,
            TransportProofStatus::Unknown,
            TransportProofStatus::Timeout,
            TransportProofStatus::Unsupported,
            TransportProofStatus::Rejected,
        ] {
            assert_eq!(TransportProofStatus::from(Outcome::from(status)), status);
        }
    }

    #[test]
    fn test_transport_obligation_result_structured_evidence_roundtrip() {
        let result = TransportObligationResult {
            obligation_id: Some("crate::safe_div#vc0".to_string()),
            claim_digest_sha256: Some(
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
            ),
            kind: "divzero".to_string(),
            typed_kind: None,
            description: "division by zero".to_string(),
            location: None,
            outcome: Outcome::Proved,
            solver: "trust-wp-native".to_string(),
            time_ms: 12,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: Some(TransportNativeTrustIrEvidence {
                suite: "trust-wp".to_string(),
                backend: "trust-wp-native".to_string(),
                request_id: Some("req-42".to_string()),
                native_id: Some("trust_ir-fn-7:vc0".to_string()),
                present: true,
                artifacts: vec![TransportEvidenceArtifact {
                    kind: "native_trust_ir".to_string(),
                    format: Some("trust_ir-json".to_string()),
                    artifact_id: Some("native-artifact-1".to_string()),
                    digest: Some(TransportArtifactDigest {
                        algorithm: "sha256".to_string(),
                        value: "0123456789abcdef".to_string(),
                    }),
                    uri: Some("file:///tmp/native-trust_ir.json".to_string()),
                    materialization: None,
                    metadata: Some(serde_json::json!({
                        "basic_blocks": 3,
                        "has_assertions": true
                    })),
                }],
                diagnostics: vec![],
            }),
            proof_evidence: Some(TransportProofEvidence {
                suite: "trust-wp".to_string(),
                backend: "trust-wp-native".to_string(),
                request_id: Some("req-42".to_string()),
                proof_id: Some("proof-99".to_string()),
                native_id: Some("trust_ir-fn-7:vc0".to_string()),
                status: TransportProofStatus::Proved,
                strength: Some(ProofStrength::deductive()),
                evidence: Some(ProofEvidence::new(
                    ReasoningKind::Deductive,
                    AssuranceLevel::Certified,
                )),
                artifacts: vec![TransportEvidenceArtifact {
                    kind: "certificate".to_string(),
                    format: Some("lfsc".to_string()),
                    artifact_id: Some("cert-99".to_string()),
                    digest: Some(TransportArtifactDigest {
                        algorithm: "sha256".to_string(),
                        value: "fedcba9876543210".to_string(),
                    }),
                    uri: Some("artifact://proofs/proof-99.lfsc".to_string()),
                    materialization: None,
                    metadata: Some(serde_json::json!({
                        "checker": "trust-wp-cert-check",
                        "checked": true
                    })),
                }],
                diagnostics: vec![TransportEvidenceDiagnostic {
                    code: "unsupported.witness.minimized".to_string(),
                    severity: TransportEvidenceDiagnosticSeverity::Warning,
                    message: "backend did not emit minimized witness".to_string(),
                    detail: Some("full replay log is available as artifact".to_string()),
                }],
            }),
            monitor: Some(TransportMonitorEvidence {
                status: TransportMonitorStatus::Monitored,
                reason: "Clean kernel checked monitor=true iff proposition".to_string(),
                predicate_digest: format!("sha256:{}", "a".repeat(64)),
            }),
        };

        let json = serde_json::to_string(&result).expect("serialize structured evidence");
        assert!(json.contains("\"obligation_id\""));
        assert!(json.contains("\"claim_digest_sha256\""));
        assert!(json.contains("\"native_trust_ir\""));
        assert!(json.contains("\"proof_evidence\""));
        assert!(json.contains("\"monitor\""));
        assert!(json.contains("\"status\":\"monitored\""));
        assert!(json.contains("\"status\":\"proved\""));

        let round: TransportObligationResult =
            serde_json::from_str(&json).expect("deserialize structured evidence");
        assert_eq!(round, result);
        assert_eq!(
            round
                .proof_evidence
                .as_ref()
                .and_then(|evidence| evidence.artifacts.first())
                .and_then(|artifact| artifact.digest.as_ref())
                .map(|digest| (digest.algorithm.as_str(), digest.value.as_str())),
            Some(("sha256", "fedcba9876543210"))
        );
    }

    #[test]
    fn test_transport_monitor_measured_unmonitored_roundtrip_and_unknown_status_rejected() {
        for (status, wire, reason, fill) in [
            (
                TransportMonitorStatus::Measured,
                "measured",
                "kernel-bound E5 scalar with authenticated transition placement",
                'c',
            ),
            (
                TransportMonitorStatus::Unmonitored,
                "unmonitored",
                "quantified propositions have no finite runtime monitor",
                'b',
            ),
        ] {
            let evidence = TransportMonitorEvidence {
                status,
                reason: reason.to_string(),
                predicate_digest: format!("sha256:{}", fill.to_string().repeat(64)),
            };
            let json = serde_json::to_string(&evidence).expect("serialize monitor evidence");
            assert!(json.contains(&format!("\"status\":\"{wire}\"")));
            assert_eq!(
                serde_json::from_str::<TransportMonitorEvidence>(&json)
                    .expect("deserialize monitor evidence"),
                evidence,
            );
        }

        let unknown = format!(
            r#"{{"status":"assumed","reason":"forged","predicate_digest":"sha256:{}"}}"#,
            "c".repeat(64),
        );
        assert!(
            serde_json::from_str::<TransportMonitorEvidence>(&unknown).is_err(),
            "unknown monitor statuses must fail closed at the typed wire boundary",
        );
    }

    #[test]
    fn test_transport_message_crate_summary_roundtrip() {
        let msg = TransportMessage::CrateSummary(CrateTransportSummary {
            crate_name: "my_crate".to_string(),
            package_name: Some("my-package".to_string()),
            primary_package: true,
            verification_session: "session-1".to_string(),
            functions_analyzed: 7,
            functions_verified: 5,
            total_proved: 10,
            total_failed: 1,
            total_unknown: 2,
            total_timed_out: 1,
            total_skipped: 0,
            total_runtime_checked: 0,
            total_obligations: 13,
        });
        let json = serde_json::to_string(&msg).expect("serialize");
        let parsed = parse_transport_payload(&json).expect("deserialize");
        match parsed {
            TransportMessage::CrateSummary(s) => {
                assert_eq!(s.crate_name, "my_crate");
                assert_eq!(s.functions_analyzed, 7);
                assert_eq!(s.total_obligations, 13);
                assert_eq!(s.total_timed_out, 1);
                assert_eq!(s.total_skipped, 0);
            }
            _ => panic!("expected CrateSummary"),
        }
    }

    #[test]
    fn test_transport_message_coverage_summary_roundtrip() {
        // Trust (assertion-grade coverage): pins the wire shape the compiler
        // emits — `{"type":"coverage_summary","crate_name":...,"eligible":N,
        // "processed":N}` — and that the canonical parser recovers it.
        let eligible_functions =
            (0..12).map(|index| format!("my_crate::f{index:02}")).collect::<Vec<_>>();
        let processed_functions = eligible_functions[..9].to_vec();
        let msg = TransportMessage::CoverageSummary(CoverageTransportSummary {
            crate_name: "my_crate".to_string(),
            package_name: "my-package".to_string(),
            primary_package: true,
            verification_session: "verification-session-42".to_string(),
            eligible: 12,
            processed: 9,
            function_identities: Some(CoverageFunctionIdentityInventory {
                schema: COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1.to_string(),
                eligible_functions: eligible_functions.clone(),
                processed_functions: processed_functions.clone(),
            }),
        });
        let json = serde_json::to_string(&msg).expect("serialize");
        assert!(json.contains("\"type\":\"coverage_summary\""), "{json}");
        assert!(json.contains("\"eligible\":12"), "{json}");
        assert!(json.contains("\"processed\":9"), "{json}");
        assert!(json.contains("\"package_name\":\"my-package\""), "{json}");
        assert!(json.contains("\"primary_package\":true"), "{json}");
        assert!(json.contains("\"verification_session\":\"verification-session-42\""), "{json}");
        assert!(json.contains(COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1), "{json}");

        let line = format!("{TRANSPORT_PREFIX}{json}");
        let parsed = parse_transport_line(&line).expect("coverage_summary line must parse");
        match parsed {
            TransportMessage::CoverageSummary(s) => {
                assert_eq!(s.crate_name, "my_crate");
                assert_eq!(s.package_name, "my-package");
                assert!(s.primary_package);
                assert_eq!(s.verification_session, "verification-session-42");
                assert_eq!(s.eligible, 12);
                assert_eq!(s.processed, 9);
                assert!(!s.is_complete());
                assert_eq!(s.shortfall(), 3);
                let identities = s.function_identities.expect("current exact identity inventory");
                assert_eq!(identities.eligible_functions, eligible_functions);
                assert_eq!(identities.processed_functions, processed_functions);
            }
            _ => panic!("expected CoverageSummary"),
        }
    }

    #[test]
    fn test_coverage_summary_complete_requires_exact_equality() {
        let complete = CoverageTransportSummary {
            crate_name: "c".to_string(),
            package_name: "pkg".to_string(),
            primary_package: true,
            verification_session: "session".to_string(),
            eligible: 4,
            processed: 4,
            function_identities: None,
        };
        assert!(complete.is_complete());
        assert_eq!(complete.shortfall(), 0);
        // An over-count is not proof of completeness: it signals duplicate or
        // cross-unit accounting contamination and must fail closed.
        let over = CoverageTransportSummary { processed: 5, ..complete.clone() };
        assert!(!over.is_complete());
        assert_eq!(over.shortfall(), 0);
        assert!(!VerificationCoverage::from_counts(4, 5).coverage_complete);
    }

    #[test]
    fn test_coverage_summary_old_wire_shape_defaults_new_identity_fields() {
        let line = format!(
            "{TRANSPORT_PREFIX}{{\"type\":\"coverage_summary\",\"crate_name\":\"legacy\",\"eligible\":2,\"processed\":2}}"
        );
        let parsed = parse_transport_line(&line).expect("legacy coverage row must parse");
        let TransportMessage::CoverageSummary(summary) = parsed else {
            panic!("expected CoverageSummary");
        };
        assert_eq!(summary.crate_name, "legacy");
        assert_eq!(summary.package_name, "");
        assert!(!summary.primary_package);
        assert_eq!(summary.verification_session, "");
        assert_eq!(summary.function_identities, None);
        assert!(summary.is_complete());
    }

    #[test]
    fn test_verification_gate_report_deserializes_without_coverage() {
        // Back-compat: pre-coverage gate JSON (older toolchain / older report)
        // must still deserialize, with coverage absent = coverage-unknown.
        let json = r#"{"lane":"default","decision":"pass","exit_code":0,"counts":{"total":1,"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"assumed":0,"mandated":0}}"#;
        let gate: VerificationGateReport = serde_json::from_str(json).expect("old gate JSON");
        assert_eq!(gate.coverage, None);
        // And a coverage-carrying gate round-trips.
        let with = VerificationGateReport {
            coverage: Some(VerificationCoverage::from_counts(7, 5)),
            ..gate
        };
        let json = serde_json::to_string(&with).expect("serialize");
        assert!(json.contains("\"coverage_complete\":false"), "{json}");
        let round: VerificationGateReport = serde_json::from_str(&json).expect("round-trip");
        assert_eq!(
            round.coverage,
            Some(VerificationCoverage { eligible: 7, processed: 5, coverage_complete: false })
        );
    }

    #[test]
    fn test_parse_transport_line_valid() {
        let json = r#"{"type":"function_result","function":"f","results":[],"proved":0,"failed":0,"unknown":0,"runtime_checked":0,"total":0}"#;
        let line = format!("{TRANSPORT_PREFIX}{json}");
        let msg = parse_transport_line(&line).expect("should parse");
        match msg {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.function, "f");
                assert_eq!(r.timed_out, 0);
                assert_eq!(r.skipped, 0);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_parse_transport_line_with_i128_counterexample_preserves_proof() {
        // Regression (Trust leak-verification transport): a `failed` obligation's
        // counterexample carries a bare-number i128 value. serde_json without
        // `arbitrary_precision` used to error "i128 is not supported", failing the
        // WHOLE line's strict parse and silently downgrading the co-located
        // `proved` obligation to `unknown` — losing a real proof (e.g. a bounded
        // `Vec::with_capacity`). The flexible deserializer must keep both rows.
        let json = r#"{"type":"function_result","function":"m::f","results":[{"kind":"overflow:add","description":"arithmetic overflow (Add)","outcome":"failed","solver":"ay-in-process","time_ms":0,"counterexample_model":{"assignments":[["n",{"Int":268435456}],["m",{"Uint":18446744073709551615}]]}},{"kind":"unbounded_allocation","description":"bounded","outcome":"proved","solver":"interval","time_ms":0}],"proved":1,"failed":1,"unknown":0,"runtime_checked":0,"total":2}"#;
        let line = format!("{TRANSPORT_PREFIX}{json}");
        let msg = parse_transport_line(&line).expect("i128 counterexample line must parse");
        let TransportMessage::FunctionResult(r) = msg else { panic!("expected FunctionResult") };
        assert_eq!(
            r.proved, 1,
            "the proved obligation must survive, not be lost to the failed row"
        );
        assert_eq!(r.failed, 1);
        let cex = r.results[0].counterexample_model.as_ref().expect("counterexample present");
        assert_eq!(cex.assignments[0].1, CounterexampleValue::Int(268_435_456));
        assert_eq!(cex.assignments[1].1, CounterexampleValue::Uint(18_446_744_073_709_551_615));
    }

    #[test]
    fn test_counterexample_value_i128_number_and_string_both_deserialize() {
        // The emitter writes a bare number; a string is accepted for forward-compat.
        let from_num: CounterexampleValue =
            serde_json::from_str(r#"{"Int":-42}"#).expect("number form");
        assert_eq!(from_num, CounterexampleValue::Int(-42));
        let from_str: CounterexampleValue =
            serde_json::from_str(r#"{"Int":"-42"}"#).expect("string form");
        assert_eq!(from_str, CounterexampleValue::Int(-42));
        // u64::MAX round-trips through visit_u64; values beyond u64 cannot be a
        // bare JSON number without `arbitrary_precision`, so a string carries them.
        let big_uint: CounterexampleValue =
            serde_json::from_str(r#"{"Uint":18446744073709551615}"#).expect("u64::MAX as number");
        assert_eq!(big_uint, CounterexampleValue::Uint(18_446_744_073_709_551_615));
        let beyond_u64: CounterexampleValue =
            serde_json::from_str(r#"{"Uint":"18446744073709551616"}"#)
                .expect("u64::MAX+1 as string");
        assert_eq!(beyond_u64, CounterexampleValue::Uint(18_446_744_073_709_551_616));

        // The serializer must never emit a bare number that serde_json cannot
        // parse back. Preserve numeric JSON in range and use the accepted
        // decimal-string representation outside its 64-bit number domain.
        for value in [
            CounterexampleValue::Int(i128::from(i64::MIN) - 1),
            CounterexampleValue::Int(i128::from(u64::MAX) + 1),
            CounterexampleValue::Uint(u128::from(u64::MAX) + 1),
        ] {
            let json = serde_json::to_string(&value).expect("serialize wide counterexample value");
            assert!(json.contains(":\""), "wide integer must use decimal-string JSON: {json}");
            let round_trip: CounterexampleValue =
                serde_json::from_str(&json).expect("deserialize serialized wide counterexample");
            assert_eq!(round_trip, value);
        }
    }

    #[test]
    fn test_transport_message_function_result_split_counters_roundtrip() {
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::proof_gap".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            results: vec![],
            proved: 0,
            failed: 0,
            unknown: 2,
            timed_out: 1,
            skipped: 1,
            runtime_checked: 0,
            cached: 0,
            total: 2,
        });

        let json = serde_json::to_string(&msg).expect("serialize split counters");
        assert!(json.contains("\"timed_out\":1"));
        assert!(json.contains("\"skipped\":1"));

        let parsed = parse_transport_payload(&json).expect("deserialize");
        match parsed {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.unknown, 2);
                assert_eq!(r.timed_out, 1);
                assert_eq!(r.skipped, 1);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_function_transport_result_cached_field_roundtrip_and_default() {
        // Trust (verify-cache): the `cached` count surfaces cache-replayed
        // obligations in the machine-readable transport so `targo trust` can
        // aggregate hit-rate without relabeling the conservative `unknown` rows.
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::replayed".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            results: vec![],
            proved: 0,
            failed: 0,
            unknown: 3,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 3,
            total: 3,
        });
        let json = serde_json::to_string(&msg).expect("serialize cached");
        assert!(json.contains("\"cached\":3"), "cached count must serialize: {json}");
        match parse_transport_payload(&json).expect("deserialize") {
            TransportMessage::FunctionResult(r) => assert_eq!(r.cached, 3),
            _ => panic!("expected FunctionResult"),
        }

        // Backward compatibility: older JSON without `cached` must still
        // deserialize, defaulting the field to 0 (serde `default`).
        let legacy = r#"{
            "type":"function_result",
            "function":"crate::legacy",
            "results":[],
            "proved":1,"failed":0,"unknown":0,
            "runtime_checked":0,"total":1
        }"#;
        match parse_transport_payload(legacy).expect("deserialize legacy") {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.cached, 0, "legacy JSON without cached defaults to 0");
                assert_eq!(r.proved, 1);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    #[test]
    fn test_transport_message_crate_summary_split_counter_defaults() {
        let json = r#"{
            "type":"crate_summary",
            "crate_name":"demo",
            "functions_analyzed":1,
            "functions_verified":1,
            "total_proved":0,
            "total_failed":0,
            "total_unknown":1,
            "total_runtime_checked":0,
            "total_obligations":1
        }"#;

        let parsed = parse_transport_payload(json).expect("deserialize");

        match parsed {
            TransportMessage::CrateSummary(summary) => {
                assert_eq!(summary.total_unknown, 1);
                assert_eq!(summary.total_timed_out, 0);
                assert_eq!(summary.total_skipped, 0);
            }
            _ => panic!("expected CrateSummary"),
        }
    }

    #[test]
    fn test_transport_message_crate_summary_requires_analyzed_count() {
        let legacy = r#"{
            "type":"crate_summary",
            "crate_name":"demo",
            "functions_verified":1,
            "total_proved":1,
            "total_failed":0,
            "total_unknown":0,
            "total_runtime_checked":0,
            "total_obligations":1
        }"#;

        let error = parse_transport_payload(legacy)
            .expect_err("missing functions_analyzed must fail closed");
        assert!(error.to_string().contains("functions_analyzed"), "{error}");
    }

    #[test]
    fn test_parse_transport_line_no_prefix() {
        assert!(parse_transport_line("note: Trust [overflow:add]: ...").is_none());
    }

    #[test]
    fn test_parse_transport_line_invalid_json() {
        assert!(parse_transport_line("TRUST_JSON:{invalid}").is_none());
    }

    // Trust (R1 corpus, transport-parse cascade): a function line carrying a
    // structured counterexample_model must parse CANONICALLY. The derived
    // internally-tagged deserializer buffered rows through serde's private
    // `Content`, whose `deserialize_i128` is unsupported — so ONE failed row
    // with a counterexample poisoned the WHOLE line and every sibling `proved`
    // row was lossy-downgraded to Unknown ("lossy transport cannot prove
    // obligations"). Round-trip the exact emit path (`serde_json::to_string`
    // of the tagged enum, the compiler's `emit_transport_json` shape) and
    // require canonical parsing to preserve outcomes + the counterexample.
    #[test]
    fn test_parse_transport_payload_with_i128_u128_counterexample_model() {
        let msg = TransportMessage::FunctionResult(FunctionTransportResult {
            function: "crate::mixed".to_string(),
            package_name: None,
            crate_name: None,
            primary_package: false,
            verification_session: String::new(),
            results: vec![
                TransportObligationResult {
                    obligation_id: None,
                    claim_digest_sha256: None,
                    kind: "bounds".to_string(),
                    typed_kind: None,
                    description: "index out of bounds".to_string(),
                    location: None,
                    outcome: Outcome::Failed,
                    solver: "ay-in-process".to_string(),
                    time_ms: 1,
                    counterexample: Some("i = 3".to_string()),
                    counterexample_model: Some(Counterexample::new(vec![
                        ("i".to_string(), CounterexampleValue::Int(i128::from(i64::MIN) - 1)),
                        ("len".to_string(), CounterexampleValue::Uint(u128::from(u64::MAX) + 1)),
                    ])),
                    reason: None,
                    native_trust_ir: None,
                    proof_evidence: None,
                    design_mandate: false,
                    monitor: None,
                },
                TransportObligationResult {
                    obligation_id: None,
                    claim_digest_sha256: None,
                    kind: "overflow:add".to_string(),
                    typed_kind: None,
                    description: "a + b".to_string(),
                    location: None,
                    outcome: Outcome::Proved,
                    solver: "ay-in-process".to_string(),
                    time_ms: 1,
                    counterexample: None,
                    counterexample_model: None,
                    reason: None,
                    native_trust_ir: None,
                    proof_evidence: None,
                    design_mandate: false,
                    monitor: None,
                },
            ],
            proved: 1,
            failed: 1,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 2,
        });
        let payload = serde_json::to_string(&msg).expect("emit");

        let parsed = parse_transport_payload(&payload)
            .expect("canonical parse must survive an i128/u128 counterexample_model");
        match parsed {
            TransportMessage::FunctionResult(r) => {
                assert_eq!(r.results.len(), 2);
                assert_eq!(r.results[0].outcome, Outcome::Failed);
                assert_eq!(
                    r.results[0]
                        .counterexample_model
                        .as_ref()
                        .expect("counterexample preserved")
                        .assignments[0]
                        .1,
                    CounterexampleValue::Int(i128::from(i64::MIN) - 1),
                );
                assert_eq!(
                    r.results[0]
                        .counterexample_model
                        .as_ref()
                        .expect("counterexample preserved")
                        .assignments[1]
                        .1,
                    CounterexampleValue::Uint(u128::from(u64::MAX) + 1),
                );
                // The load-bearing bit: the sibling PROVED row parses canonically
                // (no lossy downgrade to Unknown).
                assert_eq!(r.results[1].outcome, Outcome::Proved);
            }
            _ => panic!("expected FunctionResult"),
        }
    }

    // Tag dispatch must reject unknown or future message types: payload parsing
    // returns an error and the optional line scanner returns None, never a
    // mis-tagged variant.
    #[test]
    fn test_parse_transport_line_unknown_type_tag_is_none() {
        let payload = r#"{"type":"future_variant","payload":1}"#;
        assert!(parse_transport_payload(payload).is_err());
        assert!(parse_transport_line(&format!("{TRANSPORT_PREFIX}{payload}")).is_none());
    }

    // -----------------------------------------------------------------------
    // NativeProofEnvelope battery (S2 carrier primitive).
    // -----------------------------------------------------------------------

    fn sample_envelope() -> NativeProofEnvelope {
        NativeProofEnvelope {
            schema: NATIVE_PROOF_ENVELOPE_SCHEMA.to_string(),
            kind: NativeProofEnvelopeKind::ChcInductiveInvariant,
            claim_payload:
                r#"{"schema":"trustc.transport-exact-vc-claim.v2","semantics":{},"vc":{}}"#
                    .to_string(),
            claim_digest_sha256: "ab".repeat(32),
            normalized_input_sha256: "cd".repeat(32),
            transport_identity: NativeProofTransportIdentity {
                suite: "trust-mc-native".to_string(),
                request_id: 7,
                proof_id: 3,
                native_id: "chc-row-0".to_string(),
            },
            artifacts: vec![
                NativeProofArtifact {
                    kind: "pdr-invariant-model".to_string(),
                    sha256: "ef".repeat(32),
                    bytes: vec![1, 2, 3, 4],
                },
                NativeProofArtifact {
                    kind: "solver-transcript".to_string(),
                    sha256: "01".repeat(32),
                    bytes: b"(check-sat) unsat".to_vec(),
                },
            ],
        }
    }

    fn sample_proved_with_envelope() -> VerificationResult {
        VerificationResult::Proved {
            solver: Symbol::from("trust-mc"),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: Some(vec![9, 9, 9]),
            solver_warnings: Some(vec!["warn".to_string()]),
            native_proof_envelope: Some(sample_envelope()),
        }
    }

    /// Serde round-trip of an envelope-bearing Proved preserves every field
    /// of the envelope bit-for-bit.
    #[test]
    fn test_native_proof_envelope_serde_round_trip_preserves_everything() {
        let proved = sample_proved_with_envelope();
        let json = serde_json::to_string(&proved).expect("serialize");
        let back: VerificationResult = serde_json::from_str(&json).expect("deserialize");
        match back {
            VerificationResult::Proved {
                solver,
                time_ms,
                strength,
                proof_certificate,
                solver_warnings,
                native_proof_envelope,
            } => {
                assert_eq!(solver.as_str(), "trust-mc");
                assert_eq!(time_ms, 42);
                assert_eq!(strength, ProofStrength::smt_unsat());
                assert_eq!(proof_certificate, Some(vec![9, 9, 9]));
                assert_eq!(solver_warnings, Some(vec!["warn".to_string()]));
                let env = native_proof_envelope.expect("envelope survives round trip");
                assert_eq!(env, sample_envelope());
                assert!(env.accepted());
            }
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    /// Wire compat: an old-format Proved JSON (serialized before the field
    /// existed) deserializes with `native_proof_envelope: None`, and an
    /// envelope-less Proved serializes WITHOUT the field (byte-identical
    /// old wire shape).
    #[test]
    fn test_native_proof_envelope_old_format_proved_deserializes_to_none() {
        // Exactly what pre-envelope trust-types serialized (external tagging,
        // optional fields skipped).
        let old = r#"{"Proved":{"solver":"ay","time_ms":5,"strength":{"reasoning":"Smt","assurance":"SmtBacked"}}}"#;
        let back: VerificationResult = serde_json::from_str(old).expect("old wire format parses");
        match back {
            VerificationResult::Proved { native_proof_envelope, proof_certificate, .. } => {
                assert!(native_proof_envelope.is_none());
                assert!(proof_certificate.is_none());
            }
            other => panic!("expected Proved, got {other:?}"),
        }

        // And the reverse direction: no envelope => no field on the wire.
        let proved = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let json = serde_json::to_string(&proved).expect("serialize");
        assert!(
            !json.contains("native_proof_envelope"),
            "envelope-less Proved must keep the old wire shape: {json}"
        );
    }

    /// Oversize artifact payload (> 16 MiB total) fails `accepted()`;
    /// consumers must treat the envelope as absent.
    #[test]
    fn test_native_proof_envelope_oversize_artifacts_fail_accepted() {
        let mut env = sample_envelope();
        assert!(env.accepted(), "control: sample envelope accepted");

        // Split the budget across two artifacts to pin that the bound is on
        // the TOTAL, not per-artifact.
        let half = (NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES / 2) as usize;
        env.artifacts = vec![
            NativeProofArtifact {
                kind: "a".to_string(),
                sha256: "00".repeat(32),
                bytes: vec![0u8; half],
            },
            NativeProofArtifact {
                kind: "b".to_string(),
                sha256: "11".repeat(32),
                bytes: vec![0u8; half + 1],
            },
        ];
        assert!(env.total_carried_bytes() > NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES);
        assert!(!env.accepted(), "oversize total must fail acceptance");

        // Exactly at the bound is still accepted (bound is inclusive): trim
        // the second artifact so the WHOLE envelope — strings included —
        // lands exactly on the bound.
        let last = env.artifacts.len() - 1;
        env.artifacts[last].bytes.clear();
        let remaining =
            (NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES - env.total_carried_bytes()) as usize;
        env.artifacts[last].bytes = vec![0u8; remaining];
        assert_eq!(env.total_carried_bytes(), NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES);
        assert!(env.accepted());

        // One byte over the bound flips to rejected.
        env.artifacts[last].bytes.push(0);
        assert!(!env.accepted());
    }

    /// The byte bound covers EVERY variable-length field — not just artifact
    /// bytes — and the artifact COUNT is capped: `accepted()` leaves no
    /// unbounded field for a producer to inflate report/replay memory with.
    #[test]
    fn test_native_proof_envelope_unbounded_strings_and_artifact_flood_fail_accepted() {
        // Oversize claim_payload alone (tiny artifacts) must fail.
        let mut env = sample_envelope();
        env.claim_payload = "x".repeat(NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize + 1);
        assert!(!env.accepted(), "oversize claim_payload must fail acceptance");

        // Oversize artifact LABEL (kind) alone must fail — labels count too.
        let mut env = sample_envelope();
        env.artifacts[0].kind = "k".repeat(NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize + 1);
        assert!(!env.accepted(), "oversize artifact kind label must fail acceptance");

        // Oversize transport-identity string alone must fail.
        let mut env = sample_envelope();
        env.transport_identity.native_id =
            "n".repeat(NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize + 1);
        assert!(!env.accepted(), "oversize transport identity string must fail acceptance");

        // A flood of zero-byte artifacts (well under the byte budget) must
        // fail on the COUNT cap.
        let mut env = sample_envelope();
        env.artifacts = (0..=NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS)
            .map(|_| NativeProofArtifact {
                kind: String::new(),
                sha256: String::new(),
                bytes: Vec::new(),
            })
            .collect();
        assert!(env.total_carried_bytes() <= NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES);
        assert!(!env.accepted(), "artifact flood must fail on the count cap");
        // Exactly at the cap passes (cap is inclusive).
        env.artifacts.truncate(NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS);
        assert!(env.accepted());
    }

    /// The WIRE decoder enforces the byte budget while visiting the JSON byte
    /// sequence. In particular, it must not first build an unbounded
    /// `serde_json::Value` / `Vec<u8>` and only then call `accepted()`.
    #[test]
    fn test_native_proof_envelope_wire_oversize_byte_sequence_lands_absent() {
        let (json, envelope_json) = {
            let mut env = sample_envelope();
            env.artifacts = vec![NativeProofArtifact {
                kind: "oversize-model".to_string(),
                sha256: "00".repeat(32),
                bytes: vec![0; NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize + 1],
            }];
            assert!(!env.accepted(), "control: oversized envelope is not accepted");
            let envelope_json =
                serde_json::to_string(&env).expect("serialize adversarial envelope");
            let proved = VerificationResult::Proved {
                solver: Symbol::from("trust-mc"),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: Some(env),
            };
            (
                serde_json::to_string(&proved).expect("serialize adversarial byte sequence"),
                envelope_json,
            )
        };
        assert!(json.len() > NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize);
        assert!(
            serde_json::from_str::<NativeProofEnvelope>(&envelope_json).is_err(),
            "direct envelope parsing must enforce the same streaming byte budget",
        );
        match serde_json::from_str::<VerificationResult>(&json) {
            Ok(VerificationResult::Proved { native_proof_envelope, .. }) => {
                assert!(native_proof_envelope.is_none(), "oversize bytes must land absent");
            }
            other => panic!("oversize optional envelope must not poison its row: {other:?}"),
        }
    }

    /// Wire accounting exactly matches `total_carried_bytes()`: the closed
    /// root enum spelling is fixed overhead, not payload, so an accepted
    /// envelope at the inclusive 16 MiB boundary still round-trips.
    #[test]
    fn test_native_proof_envelope_wire_exact_total_budget_round_trips() {
        let mut env = sample_envelope();
        env.claim_payload.clear();
        let remaining =
            (NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES - env.total_carried_bytes()) as usize;
        assert!(remaining > 0);
        env.claim_payload = "x".repeat(remaining);
        assert_eq!(env.total_carried_bytes(), NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES);
        assert!(env.accepted());

        let direct_json = serde_json::to_string(&env).expect("serialize exact-boundary envelope");
        let direct: NativeProofEnvelope =
            serde_json::from_str(&direct_json).expect("direct exact-boundary parse");
        assert_eq!(direct, env);

        let proved = VerificationResult::Proved {
            solver: Symbol::from("trust-mc"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: Some(env),
        };
        let json = serde_json::to_string(&proved).expect("serialize exact-boundary envelope");
        match serde_json::from_str::<VerificationResult>(&json) {
            Ok(VerificationResult::Proved { native_proof_envelope: Some(env), .. }) => {
                assert_eq!(env.total_carried_bytes(), NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES);
                assert!(env.accepted());
            }
            other => panic!("exact-boundary accepted envelope must round-trip: {other:?}"),
        }
    }

    /// Artifact count is checked before decoding a 65th artifact object, even
    /// when every artifact is otherwise tiny and the byte budget is untouched.
    #[test]
    fn test_native_proof_envelope_wire_artifact_flood_lands_absent() {
        let mut env = sample_envelope();
        env.artifacts = (0..=NATIVE_PROOF_ENVELOPE_MAX_ARTIFACTS)
            .map(|index| NativeProofArtifact {
                kind: format!("artifact-{index}"),
                sha256: String::new(),
                bytes: Vec::new(),
            })
            .collect();
        assert!(!env.accepted(), "control: 65 artifacts exceed the cap");
        let proved = VerificationResult::Proved {
            solver: Symbol::from("trust-mc"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: Some(env),
        };
        let json = serde_json::to_string(&proved).expect("serialize artifact flood");
        match serde_json::from_str::<VerificationResult>(&json) {
            Ok(VerificationResult::Proved { native_proof_envelope, .. }) => {
                assert!(native_proof_envelope.is_none(), "artifact flood must land absent");
            }
            other => panic!("artifact-flood envelope must not poison its row: {other:?}"),
        }
    }

    /// Unknown and duplicate fields fail the strict v1 shape. Their values are
    /// consumed through `IgnoredAny`, so an unknown multi-MiB padding field is
    /// not retained in an intermediate JSON tree.
    #[test]
    fn test_native_proof_envelope_wire_unknown_padding_and_duplicates_land_absent() {
        let good = serde_json::to_string(&sample_envelope()).expect("serialize envelope");
        let padded = {
            let padding = "x".repeat(NATIVE_PROOF_ENVELOPE_MAX_TOTAL_BYTES as usize + 1);
            good.replacen('{', &format!(r#"{{"padding":"{padding}","#), 1)
        };
        let duplicate =
            good.replacen('{', &format!(r#"{{"schema":"{NATIVE_PROOF_ENVELOPE_SCHEMA}","#), 1);

        let strength = r#"{"reasoning":"Smt","assurance":"SmtBacked"}"#;
        for (label, envelope) in [("unknown padding", padded), ("duplicate schema", duplicate)] {
            assert!(
                serde_json::from_str::<NativeProofEnvelope>(&envelope).is_err(),
                "{label} must fail the strict direct envelope parse",
            );
            let json = format!(
                r#"{{"Proved":{{"solver":"ay","time_ms":5,"strength":{strength},"native_proof_envelope":{envelope}}}}}"#
            );
            match serde_json::from_str::<VerificationResult>(&json) {
                Ok(VerificationResult::Proved { native_proof_envelope, .. }) => assert!(
                    native_proof_envelope.is_none(),
                    "{label} must invalidate the optional envelope"
                ),
                other => panic!("{label} must not poison the containing row: {other:?}"),
            }
        }
    }

    /// The remaining `accepted()` arms: wrong/future schema label, empty
    /// claim payload, and zero artifacts are all treated as absent.
    #[test]
    fn test_native_proof_envelope_schema_and_payload_acceptance_arms() {
        let mut env = sample_envelope();
        env.schema = "trust.native-proof-envelope.v2".to_string();
        assert!(!env.accepted(), "unknown/future schema version must fail acceptance");
        let future_json = serde_json::to_string(&env).expect("serialize future envelope");
        assert!(
            serde_json::from_str::<NativeProofEnvelope>(&future_json).is_err(),
            "direct parsing must reject an unknown schema rather than bypass acceptance",
        );

        let mut env = sample_envelope();
        env.claim_payload = String::new();
        assert!(!env.accepted(), "empty claim payload must fail acceptance");

        let mut env = sample_envelope();
        env.artifacts.clear();
        assert!(!env.accepted(), "zero-artifact envelope must fail acceptance");
    }

    /// The kind enum is CLOSED — the strict envelope parse rejects a bogus
    /// kind string outright (`Bmc`/`FiniteAcyclicBmc` cannot ride in) — while
    /// the Proved CARRIER is NOT a parse bomb: through the lenient field
    /// parse an unknown-kind envelope lands ABSENT and the row (and any
    /// report/cache document embedding it) still parses.
    #[test]
    fn test_native_proof_envelope_bogus_kind_strict_raw_but_absent_in_carrier() {
        let good = serde_json::to_string(&sample_envelope()).expect("serialize");
        assert!(good.contains("ChcInductiveInvariant"));
        for bogus in ["Bmc", "FiniteAcyclicBmc", "TotallyLegitProof"] {
            let forged = good.replace("ChcInductiveInvariant", bogus);
            let parsed: Result<NativeProofEnvelope, _> = serde_json::from_str(&forged);
            assert!(
                parsed.is_err(),
                "kind {bogus:?} must fail the strict envelope parse (closed enum)"
            );
            // Through the Proved carrier: strict versioned parse means
            // unknown kind => treated absent, and the containing document
            // parses on — one hostile envelope must never poison a whole
            // report/cache file.
            let carrier = serde_json::to_string(&sample_proved_with_envelope())
                .expect("serialize")
                .replace("ChcInductiveInvariant", bogus);
            match serde_json::from_str::<VerificationResult>(&carrier) {
                Ok(VerificationResult::Proved { native_proof_envelope, .. }) => assert!(
                    native_proof_envelope.is_none(),
                    "unknown kind {bogus:?} must land absent, not smuggle in"
                ),
                other => panic!(
                    "carrier with kind {bogus:?} must still parse as Proved (no parse bomb), \
                     got {other:?}"
                ),
            }
        }
    }

    /// Strict versioned parse at the wire, remaining shapes: future-version,
    /// structurally malformed / incomplete, non-object garbage, and
    /// parseable-but-non-accepted envelopes all land ABSENT without
    /// poisoning the containing result document.
    #[test]
    fn test_native_proof_envelope_unknown_version_and_malformed_land_absent() {
        // Future schema version: serializes (Serialize is not gated), but
        // the lenient parse drops it on read.
        let mut future = sample_envelope();
        future.schema = "trust.native-proof-envelope.v2".to_string();
        // Parseable but non-accepted (zero artifacts): dropped at the wire.
        let mut empty_artifacts = sample_envelope();
        empty_artifacts.artifacts.clear();
        for env in [future, empty_artifacts] {
            let proved = VerificationResult::Proved {
                solver: Symbol::from("trust-mc"),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: Some(env),
            };
            let json = serde_json::to_string(&proved).expect("serialize");
            match serde_json::from_str::<VerificationResult>(&json) {
                Ok(VerificationResult::Proved { native_proof_envelope, .. }) => assert!(
                    native_proof_envelope.is_none(),
                    "non-accepted envelope must land absent on the wire"
                ),
                other => panic!("expected Proved, got {other:?}"),
            }
        }

        // Structurally malformed envelope values and non-object garbage.
        let strength = r#"{"reasoning":"Smt","assurance":"SmtBacked"}"#;
        for bad_env in [
            // Incomplete: schema+kind only, remaining required fields missing.
            r#"{"schema":"trust.native-proof-envelope.v1","kind":"ChcInductiveInvariant"}"#,
            "42",
            "null",
            "[]",
            r#""not an envelope""#,
        ] {
            let json = format!(
                r#"{{"Proved":{{"solver":"ay","time_ms":5,"strength":{strength},"native_proof_envelope":{bad_env}}}}}"#
            );
            match serde_json::from_str::<VerificationResult>(&json) {
                Ok(VerificationResult::Proved { native_proof_envelope, .. }) => assert!(
                    native_proof_envelope.is_none(),
                    "malformed envelope {bad_env} must land absent"
                ),
                other => {
                    panic!("malformed envelope {bad_env} must not poison the row, got {other:?}")
                }
            }
        }
    }

    /// Blueprint S2 battery: an envelope-bearing "proved" outcome pushed
    /// through the ObligationOutcome WIRE (the saved-report boundary)
    /// force-downgrades to Unknown with the deserialized-Proved downgrade
    /// reason — an envelope, even smuggled as an extra field, cannot
    /// preserve proof status across serialization.
    #[test]
    fn test_envelope_bearing_proved_through_obligation_outcome_wire_downgrades() {
        let envelope_json = serde_json::to_string(&sample_envelope()).expect("serialize");
        let wire = format!(
            r#"{{"status":"proved","strength":{{"reasoning":"Smt","assurance":"SmtBacked"}},"native_proof_envelope":{envelope_json}}}"#
        );
        match serde_json::from_str::<ObligationOutcome>(&wire) {
            Ok(ObligationOutcome::Unknown { reason }) => {
                assert_eq!(reason, DIRECT_DESERIALIZED_PROVED_DOWNGRADE_REASON);
            }
            other => panic!(
                "deserialized proved outcome (with or without envelope) must downgrade to \
                 Unknown, got {other:?}"
            ),
        }
    }

    /// Blueprint S2 battery: a forged envelope changes NO verdict anywhere —
    /// a Proved row with a fabricated envelope behaves identically to the
    /// same row without one at every decision surface trust-types owns.
    #[test]
    fn test_forged_native_proof_envelope_changes_no_verdict() {
        let bare = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let mut forged_env = sample_envelope();
        forged_env.claim_payload = "FORGED: claims to prove everything".to_string();
        let forged = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: Some(forged_env),
        };

        // Identical classification.
        assert_eq!(bare.is_proved(), forged.is_proved());
        assert_eq!(bare.is_failed(), forged.is_failed());

        // Identical assurance gating: the envelope buys no assurance level —
        // an SmtBacked row stays below Certified with or without it.
        for min in [AssuranceLevel::SmtBacked, AssuranceLevel::Certified] {
            let a = bare.clone().require_assurance(min.clone());
            let b = forged.clone().require_assurance(min);
            assert_eq!(
                a.is_proved(),
                b.is_proved(),
                "a forged envelope must not change require_assurance"
            );
        }
    }

    /// Proved clone (and envelope equality) still behave: the clone is
    /// field-for-field identical, envelope included, and mutating the clone's
    /// envelope does not alias the original.
    #[test]
    fn test_native_proof_envelope_proved_clone_eq_still_fine() {
        let proved = sample_proved_with_envelope();
        let cloned = proved.clone();
        // VerificationResult itself does not derive PartialEq; compare via
        // canonical serialization plus direct envelope equality.
        assert_eq!(
            serde_json::to_string(&proved).unwrap(),
            serde_json::to_string(&cloned).unwrap()
        );
        match (proved, cloned) {
            (
                VerificationResult::Proved { native_proof_envelope: Some(a), .. },
                VerificationResult::Proved { native_proof_envelope: Some(mut b), .. },
            ) => {
                assert_eq!(a, b);
                b.claim_payload.push('x');
                assert_ne!(a, b, "clone must be independent of the original");
            }
            _ => panic!("expected two Proved with envelopes"),
        }
    }
}

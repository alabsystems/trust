// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I7, crate-side half — **the verdict digest and re-admission on import**.
//!
//! The decision doc's I7 row, verbatim:
//!
//! > Cross-crate: Clean-origin MIR encoding + **re-admission on import**. The
//! > wire unit is a verdict digest (kernel version, environment digest, axiom
//! > closure, carrier decision, defeq certificate) — **never a source hash,
//! > which binds nothing about a kernel verdict.**
//!
//! And its acceptance control:
//!
//! > an imported certificate minted under a different kernel version must be
//! > re-checked or refused, never accepted on a matching source hash.
//!
//! # Why a source hash binds nothing
//!
//! Two crates can hold byte-identical `clean { … }` text and still disagree
//! about what a verdict means: a different kernel decides defeq differently, a
//! different environment gives the same name a different definition, a
//! different carrier map admits the same signature at a different Rust type.
//! A source hash matches in all three cases, which is precisely how a stale or
//! foreign verdict would be laundered into a local `Certified`. The digest
//! therefore carries the five things a kernel verdict actually depends on, and
//! **no API in this module accepts source text** — the wrong thing is
//! unrepresentable, not discouraged.
//!
//! # The five fields, and what each one binds
//!
//! | Field | Binds | Skew consequence |
//! |---|---|---|
//! | kernel version | *which checker* produced the verdict | refuse ([`ReadmissionRefusal::KernelVersionSkew`]) |
//! | environment digest | *what the checked term depended on* | refuse ([`ReadmissionRefusal::EnvironmentSkew`]) |
//! | axiom closure | *what the verdict rests on*, by name | refuse for CALL ([`ReadmissionRefusal::AssumptionBearing`]) |
//! | carrier decision | *the Rust type each signature position was admitted at* | refuse ([`ReadmissionRefusal::CarrierSkew`]) |
//! | defeq evidence | *that the faithfulness gate ran, and at which carrier* | refuse ([`ReadmissionRefusal::DefeqSkew`]) |
//!
//! # Sealing — the same discipline as the gate and the mint
//!
//! [`Readmitted`] is constructible only by [`readmit`], exactly as
//! [`crate::gate::Faithful`] is constructible only by
//! [`crate::gate::check_faithful`]. A consumer holding a `Readmitted` holds
//! evidence that every field of the digest was compared against the local
//! facts. On the mint side, [`mint_verdict_digest`] demands a
//! [`crate::gate::Faithful`] — so a digest cannot claim defeq evidence that was
//! never produced — and reads the axiom closure out of a sealed
//! [`KernelStatus`], never from a caller-supplied list.
//!
//! A [`VerdictDigest`] itself is deliberately **not** authority: [`VerdictDigest::decode`]
//! reconstructs one from wire bytes anyone could have written. That is safe
//! because a digest is a *claim*; the authority is [`readmit`]'s comparison of
//! that claim against locally recomputed facts, plus the local
//! `axiom_deps` cross-audit that catches a digest lying about an empty closure.
//!
//! # The kernel-version seam (finding, recorded)
//!
//! `clean-kernel` DOES expose a version:
//! `clean_kernel::VERSION` (`first-party/clean/crates/clean-kernel/src/lib.rs:49`),
//! documented there as "exposed so downstream tools can record the exact kernel
//! revision a verdict was produced under". [`local_kernel_version`] is that
//! constant, read from the kernel this crate actually links — the same kernel
//! whose `TypeChecker` produced the [`crate::gate::Faithful`] the mint demands.
//! No placeholder seam was needed. If the constant ever disappears, this module
//! stops compiling, which is the fail-closed outcome (no version ⇒ no import).
//!
//! # The re-check seam, documented rather than built
//!
//! A kernel-version skew has two sound resolutions: refuse, or re-check the
//! imported declaration under the LOCAL kernel. This module implements
//! **refusal**. The re-check lane would live beside [`readmit`] — take the
//! local `Environment` that already holds the imported declarations, run the
//! full kernel check and certification audit locally, and mint a *fresh local*
//! verdict rather than laundering the foreign one. It is not built here because
//! the rustc-side half (metadata transport of the declarations themselves) is
//! what feeds it; until then a refusal with options is the honest verdict, and
//! [`ReadmissionRefusal::KernelVersionSkew`]'s note names both resolutions.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use clean_kernel::{Environment, ExprVisitor, LevelVec, Name};
use trust_clean_carrier::{CarrierRefused, CarrierSignature, carrier_signature_for};
use trust_symbols::{Assumption, AssumptionKind, CarrierWidth, KernelStatus};
use trust_types::VerifiableFunction;

use crate::emit::{EmitRefusal, admit_lowering, plan_clean_origin_body};
use crate::gate::Faithful;

// ---------------------------------------------------------------------------
// Kernel version
// ---------------------------------------------------------------------------

/// The version of the Clean kernel THIS build links — the kernel whose
/// `TypeChecker` decides every [`crate::gate::check_faithful`] verdict in this
/// process.
///
/// This is `clean_kernel::VERSION` (the kernel crate's `CARGO_PKG_VERSION`),
/// which the kernel documents as the revision-recording surface for downstream
/// tools. It is read from the linked crate rather than taken as a parameter on
/// the mint side, and that asymmetry is deliberate: a mint that accepted a
/// version string would let a caller stamp a verdict with a kernel it was not
/// produced under, which is exactly the substitution the digest exists to make
/// unrepresentable. (The *re-admission* side takes the local version as a
/// parameter — see [`readmit`] — because there the value is a comparison input,
/// not a claim.)
#[must_use]
pub fn local_kernel_version() -> &'static str {
    clean_kernel::VERSION
}

// ---------------------------------------------------------------------------
// Environment digest
// ---------------------------------------------------------------------------

/// Wire tag for the one environment-digest mode this module computes.
///
/// The mode is part of the format on purpose: if a coarser whole-environment
/// mode ever ships it gets a different tag, and a reader that only knows this
/// one REFUSES the other rather than comparing hashes computed over different
/// things and calling the mismatch a skew (or worse, a match).
pub const ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE: u8 = 1;

/// Content hash over the declarations a verdict depended on.
///
/// # What exactly is hashed, and why (the decision of record for this field)
///
/// **The transitive dependency closure of the subject declaration — the
/// precise option — not a hash of the whole environment.** Both were
/// considered:
///
/// * a whole-environment hash is honest but coarse: adding an unrelated `def`
///   anywhere in the dependency's prelude would invalidate every certificate
///   in the crate, so re-admission would almost never succeed in practice and
///   the lane would rot into "always re-check", making the digest decoration;
/// * the per-declaration closure binds exactly what the kernel verdict could
///   have depended on. The kernel exposes enough to compute it: the public
///   [`clean_kernel::ExprVisitor`] traversal (whose dispatch the kernel itself
///   keeps exhaustive over every `ExprKind`, including the cubical and
///   set-theoretic extensions) collects `Const` references, and
///   `Environment::get_const` resolves each one.
///
/// The walk starts at the subject's own type and value, collects every
/// referenced constant name, and recurses through each referenced constant's
/// type and value to a fixpoint. For every closure member, in canonical
/// (name-sorted) order, the hashed material includes: the name, the
/// `ConstantKind`, the universe level parameters, the reducibility (which is
/// semantically load-bearing — it decides what defeq may unfold), the type,
/// and the value (or an explicit no-value marker).
///
/// **A referenced name that is absent from the environment is hashed as an
/// explicit `absent` record, not skipped and not an error.** Absence is
/// environment content: the kernel decided the verdict in an environment where
/// that name did not resolve, and a local environment where it *does* resolve
/// is a different environment — which the digest then detects. (The subject
/// itself missing IS an error: there is nothing to digest.)
///
/// # The term rendering, and its named hazard
///
/// Types and values are rendered through the kernel's `Display` and hashed via
/// `trust_types::digest` — the same construction the tree's existing
/// `TermDigest` producer uses (`trust_certify::clean_island`), kept
/// deliberately identical so two subsystems cannot disagree about the bytes of
/// the same term. Every field is length-framed before hashing, so no field
/// content can imitate a record boundary. The residual hazard, named: this
/// binds the rendering, not the abstract term, so it is only as injective as
/// `Display`. Within ONE kernel version that is the same rendering the kernel
/// itself debugs with; ACROSS kernel versions it does not need to be stable at
/// all, because [`readmit`] refuses on kernel-version skew before the
/// environment digest is ever consulted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvironmentDigest {
    hex: String,
}

impl EnvironmentDigest {
    /// The canonical lowercase-hex SHA-256.
    #[must_use]
    pub fn as_hex(&self) -> &str {
        &self.hex
    }

    /// Adopt an already-validated hex string. Private on purpose: outside this
    /// module an `EnvironmentDigest` is either COMPUTED from an environment
    /// ([`environment_digest_for`]) or decoded from a digest whose parse
    /// validated the shape — never assembled from a string a caller made up.
    fn from_validated_hex(hex: String) -> Self {
        Self { hex }
    }
}

/// Why no environment digest could be computed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum EnvironmentDigestRefusal {
    /// The subject declaration is not in the environment at all.
    NoSuchDeclaration {
        /// The name that did not resolve.
        name: String,
    },
}

impl EnvironmentDigestRefusal {
    /// The v7/D3 note: why, and what to do, with options.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::NoSuchDeclaration { name } => format!(
                "no environment digest can be computed for `{name}`: the declaration is \
                 not in the Clean environment, so there is no dependency closure to \
                 bind.\n\
                 options:\n\
                 - load the imported declarations into the environment first — the \
                   digest is computed over the environment that will actually be \
                   used;\n\
                 - check the name's spelling against the exporting crate (`crate::m::f` \
                   and `Crate.m.f` are the same path; a digest carries the Clean \
                   rendering);\n\
                 - if the declaration was deliberately removed, the import is stale: \
                   rebuild the dependency rather than digesting around the hole."
            ),
        }
    }
}

/// Collects every `Const` name referenced by an expression, via the kernel's
/// own exhaustive traversal.
///
/// Using [`clean_kernel::ExprVisitor`] rather than a hand-written match is the
/// fail-closed choice: the visitor's dispatch lives in the kernel next to
/// `ExprKind`, so a new expression variant gets a traversal arm in the same
/// change, whereas a local match with a wildcard arm would silently drop the
/// sub-expressions of any variant this crate had not heard of — and a dropped
/// sub-expression is a dependency missing from the digest, which is a false
/// re-admission waiting to happen.
struct ConstNames {
    found: BTreeSet<String>,
}

impl ExprVisitor for ConstNames {
    type Result = ();

    fn combine(&self, (): (), (): ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.found.insert(name.to_string());
    }
}

/// Append one length-framed field to the hash material.
///
/// `{label} {byte-length}:{content}\n` — the explicit length is what makes the
/// framing injective: no field content can imitate a record boundary, so two
/// different closures cannot render to identical material (see the
/// concatenation-injectivity note on `trust_types::digest`).
fn frame(material: &mut String, label: &str, content: &str) {
    let _ = write!(material, "{label} {}:", content.len());
    material.push_str(content);
    material.push('\n');
}

/// Compute the [`EnvironmentDigest`] for `name` over `env`.
///
/// This is the ONLY public constructor of an [`EnvironmentDigest`]: it can be
/// computed from an environment, never asserted. See the type's docs for the
/// full hashing decision.
///
/// # Errors
///
/// [`EnvironmentDigestRefusal::NoSuchDeclaration`] when `name` itself does not
/// resolve — there is nothing to digest. (A *transitively referenced* name
/// that does not resolve is content, not an error; it is hashed as `absent`.)
pub fn environment_digest_for(
    env: &Environment,
    name: &str,
) -> Result<EnvironmentDigest, EnvironmentDigestRefusal> {
    if env.get_const(&Name::from_string(name)).is_none() {
        return Err(EnvironmentDigestRefusal::NoSuchDeclaration { name: name.to_owned() });
    }

    // Fixpoint over the closure. `BTreeMap` keyed on the rendered name gives
    // the canonical member order, so insertion order — and therefore the order
    // declarations happened to enter the environment — cannot leak into the
    // digest.
    let mut members: BTreeMap<String, String> = BTreeMap::new();
    let mut worklist: Vec<String> = vec![name.to_owned()];

    while let Some(current) = worklist.pop() {
        if members.contains_key(&current) {
            continue;
        }

        let mut record = String::new();
        match env.get_const(&Name::from_string(&current)) {
            None => {
                // Absence is environment content — see the type docs. An
                // explicit record, so an environment where this name resolves
                // hashes differently.
                frame(&mut record, "decl", &current);
                frame(&mut record, "absent", "");
            }
            Some(info) => {
                frame(&mut record, "decl", &current);
                frame(&mut record, "kind", &format!("{:?}", info.kind));
                let levels = info
                    .level_params
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(",");
                frame(&mut record, "levels", &levels);
                // Reducibility decides what defeq may unfold, so two
                // environments differing only here can decide the same defeq
                // question differently. It is verdict-relevant content.
                frame(&mut record, "reducibility", &format!("{:?}", info.reducibility));
                frame(&mut record, "type", &info.type_.to_string());
                match info.value.as_ref() {
                    Some(value) => frame(&mut record, "value", &value.to_string()),
                    None => frame(&mut record, "no-value", ""),
                }

                let mut refs = ConstNames { found: BTreeSet::new() };
                refs.visit_expr(&info.type_);
                if let Some(value) = info.value.as_ref() {
                    refs.visit_expr(value);
                }
                for reference in refs.found {
                    if !members.contains_key(&reference) {
                        worklist.push(reference);
                    }
                }
            }
        }
        members.insert(current, record);
    }

    let mut material = String::new();
    frame(
        &mut material,
        "trust-clean-origin-environment-digest-mode",
        &ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE.to_string(),
    );
    frame(&mut material, "subject", name);
    frame(&mut material, "members", &members.len().to_string());
    for record in members.values() {
        material.push_str(record);
    }

    Ok(EnvironmentDigest::from_validated_hex(trust_types::digest::stable_sha256_hex(
        material.as_bytes(),
    )))
}

// ---------------------------------------------------------------------------
// Carrier decision and defeq evidence
// ---------------------------------------------------------------------------

/// One signature position of the carrier decision: which Clean type was
/// carried, at which Rust type, at which exact width.
///
/// The strings are the [`trust_symbols::CarrierWitness`] renderings — the
/// discharged obligation's own record of the pairing — so the wire carries
/// what was PROVED, not a re-derivation.
///
/// `bits` is an EXACT FIXED width — [`CarrierWidth::Bits`] — which is the only
/// width wire format v1 represents. An unbounded-exact carrier
/// ([`CarrierWidth::UnboundedExact`], exact by trusted runtime) has no position
/// here by construction: [`CarrierDecision::of_signature`] refuses it rather
/// than collapsing it onto a number (see [`UnencodableCarrierWidth`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierPosition {
    clean_type: String,
    rust_carrier: String,
    bits: u32,
}

impl CarrierPosition {
    /// The Clean type carried.
    #[must_use]
    pub fn clean_type(&self) -> &str {
        &self.clean_type
    }

    /// The Rust type the position was admitted at.
    #[must_use]
    pub fn rust_carrier(&self) -> &str {
        &self.rust_carrier
    }

    /// The common exact width, in bits.
    #[must_use]
    pub fn bits(&self) -> u32 {
        self.bits
    }

    fn describe(&self) -> String {
        format!("{} carried by {} ({} bits)", self.clean_type, self.rust_carrier, self.bits)
    }
}

/// The carrier decision: the Rust type EVERY signature position was admitted
/// at — arguments and result, no position optional.
///
/// Built only from a [`CarrierSignature`] (which I4 seals so it cannot exist
/// with a partial position) or by [`VerdictDigest::decode`]. There is no
/// constructor from loose strings, for the same reason the signature type has
/// none: "the interesting positions are fine" must stay unspellable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierDecision {
    arguments: Vec<CarrierPosition>,
    result: CarrierPosition,
}

impl CarrierDecision {
    /// Project a sealed I4 signature onto its wire record.
    ///
    /// # Errors
    ///
    /// [`UnencodableCarrierWidth`], naming the first signature position whose
    /// discharged width is not an exact fixed width. Wire format v1 carries
    /// `bits: u32` per position; an unbounded-exact carrier
    /// ([`CarrierWidth::UnboundedExact`]) has no honest v1 encoding, and
    /// inventing a number would make the importer compare a fiction — worse,
    /// unbounded-exact rests on a TRUSTED RUNTIME (a TCB row, not a proof),
    /// which is exactly the kind of undisclosed rest-on the digest exists to
    /// surface. Carrying it is a format-v2 decision, never a default.
    /// (`CarrierWidth` is deliberately exhaustive, so a new width variant
    /// breaks this match at compile time rather than falling through.)
    pub fn of_signature(
        signature: &CarrierSignature,
    ) -> Result<Self, UnencodableCarrierWidth> {
        fn position(
            label: &str,
            carrier: &trust_clean_carrier::Carrier,
        ) -> Result<CarrierPosition, UnencodableCarrierWidth> {
            let witness = carrier.witness();
            match witness.width() {
                CarrierWidth::Bits(bits) => Ok(CarrierPosition {
                    clean_type: witness.clean_type().to_owned(),
                    rust_carrier: witness.rust_carrier().to_owned(),
                    bits,
                }),
                CarrierWidth::UnboundedExact => Err(UnencodableCarrierWidth {
                    position: label.to_owned(),
                    witness: witness.to_string(),
                }),
            }
        }
        let mut arguments = Vec::with_capacity(signature.arguments().len());
        for (index, carrier) in signature.arguments().iter().enumerate() {
            arguments.push(position(&format!("argument {index}"), carrier)?);
        }
        let result = position("the result", signature.result())?;
        Ok(Self { arguments, result })
    }

    /// The argument positions, left to right.
    #[must_use]
    pub fn arguments(&self) -> &[CarrierPosition] {
        &self.arguments
    }

    /// The result position.
    #[must_use]
    pub fn result(&self) -> &CarrierPosition {
        &self.result
    }
}

/// A signature position whose discharged carrier width has no representation
/// in wire format v1.
///
/// Produced only by [`CarrierDecision::of_signature`], when a position's
/// [`CarrierWidth`] is not an exact fixed width. Both the mint
/// ([`DigestMintRefusal::UnencodableCarrierWidth`]) and re-admission's local
/// recomputation ([`ReadmissionRefusal::LocalCarrierWidthUnencodable`]) turn
/// this into their own fail-closed refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnencodableCarrierWidth {
    position: String,
    witness: String,
}

impl UnencodableCarrierWidth {
    /// Which signature position (`argument N` or `the result`).
    #[must_use]
    pub fn position(&self) -> &str {
        &self.position
    }

    /// The witness rendering of the offending carrier, verbatim.
    #[must_use]
    pub fn witness(&self) -> &str {
        &self.witness
    }
}

/// Wire tag for the one defeq-evidence form that exists: the faithfulness gate
/// ran, decided by kernel definitional equality, admitted at the carrier type.
const DEFEQ_MARKER_KERNEL_AT_CARRIER: u8 = 1;

/// The defeq evidence marker: the faithfulness gate ran for this declaration
/// and admitted the lowering at the named Rust carrier type.
///
/// On the mint side this is constructible only from a [`crate::gate::Faithful`]
/// (via [`mint_verdict_digest`]), so a freshly minted digest cannot claim
/// defeq evidence that was never produced. A DECODED marker is a claim like
/// the rest of the wire unit; [`readmit`] checks it against the locally
/// recomputed carrier decision, and the rustc-side metadata channel is what
/// authenticates the producer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefeqEvidence {
    admitted_at_rust: String,
}

impl DefeqEvidence {
    /// The Rust carrier type the kernel-defeq agreement was admitted at.
    ///
    /// The CARRIER type, never the Clean type — the distinction I4 exists for.
    #[must_use]
    pub fn admitted_at_rust(&self) -> &str {
        &self.admitted_at_rust
    }
}

// ---------------------------------------------------------------------------
// The verdict digest
// ---------------------------------------------------------------------------

/// Magic prefix of the wire encoding. Four bytes so a digest handed the wrong
/// kind of blob refuses immediately with a shape error, not a field error.
pub const VERDICT_DIGEST_MAGIC: [u8; 4] = *b"TVDG";

/// The one wire format version this module reads and writes.
///
/// The version is CHECKED, not advisory: an unknown version is a refusal,
/// never a best-effort parse — a field added in v2 could be exactly the field
/// whose absence a v1 best-effort reader would fail open on.
pub const VERDICT_DIGEST_FORMAT_V1: u8 = 1;

const ASSUMPTION_KIND_TRUST_MARKER: u8 = 1;
const ASSUMPTION_KIND_DOMAIN_AXIOM: u8 = 2;

/// The wire tag for an assumption kind, or `None` for a kind this format
/// cannot carry. `AssumptionKind` is `#[non_exhaustive]`, and the fail-closed
/// reading of a variant we do not know is "not encodable": the mint REFUSES it
/// ([`DigestMintRefusal::UnencodableAssumption`]) rather than collapsing it
/// onto a tag that means something else.
fn assumption_kind_tag(kind: AssumptionKind) -> Option<u8> {
    match kind {
        AssumptionKind::TrustMarker => Some(ASSUMPTION_KIND_TRUST_MARKER),
        AssumptionKind::DomainAxiom => Some(ASSUMPTION_KIND_DOMAIN_AXIOM),
        _ => None,
    }
}

/// I7's wire unit: everything a kernel verdict depends on, and nothing about
/// the source text it came from.
///
/// # There is no constructor from source text — by construction
///
/// The two routes to a `VerdictDigest` are [`mint_verdict_digest`] (sealed
/// evidence in, digest out) and [`VerdictDigest::decode`] (wire bytes in,
/// CLAIM out). No method takes source, a span, a file, or a hash of any of
/// them, so "accepted on a matching source hash" is not a bug this API can
/// host — the acceptance control's failure mode is unrepresentable rather
/// than tested-against only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerdictDigest {
    decl: String,
    kernel_version: String,
    environment: EnvironmentDigest,
    /// Audited assumptions, by name. An EMPTY vector means the certification
    /// audit ran and found nothing — the mint refuses an unrecorded closure,
    /// so "nobody looked" is not encodable as an empty list.
    assumptions: Vec<Assumption>,
    carrier: CarrierDecision,
    defeq: DefeqEvidence,
}

impl VerdictDigest {
    /// The declaration the verdict is about.
    #[must_use]
    pub fn decl(&self) -> &str {
        &self.decl
    }

    /// The kernel version the verdict was minted under.
    #[must_use]
    pub fn kernel_version(&self) -> &str {
        &self.kernel_version
    }

    /// The environment digest — see [`EnvironmentDigest`] for what it binds.
    #[must_use]
    pub fn environment(&self) -> &EnvironmentDigest {
        &self.environment
    }

    /// The audited axiom closure, disclosed by name.
    #[must_use]
    pub fn assumptions(&self) -> &[Assumption] {
        &self.assumptions
    }

    /// The carrier decision.
    #[must_use]
    pub fn carrier(&self) -> &CarrierDecision {
        &self.carrier
    }

    /// The defeq evidence marker.
    #[must_use]
    pub fn defeq(&self) -> &DefeqEvidence {
        &self.defeq
    }

    /// Encode to the versioned wire format.
    ///
    /// Layout (v1, all integers little-endian, strings `u32` byte-length +
    /// UTF-8):
    ///
    /// ```text
    /// magic "TVDG" · format u8 · decl · kernel_version
    /// · env-mode u8 · env-digest-hex
    /// · assumption-count u32 · (kind u8 · name)*
    /// · argument-count u32 · (clean · rust · bits u32)* · result(clean · rust · bits u32)
    /// · defeq-tag u8 · admitted-at
    /// ```
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&VERDICT_DIGEST_MAGIC);
        out.push(VERDICT_DIGEST_FORMAT_V1);
        put_str(&mut out, &self.decl);
        put_str(&mut out, &self.kernel_version);
        out.push(ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE);
        put_str(&mut out, &self.environment.hex);
        put_u32(&mut out, u32::try_from(self.assumptions.len()).expect("closure count"));
        for assumption in &self.assumptions {
            // Both constructors refuse a kind without a tag (`mint_verdict_digest`
            // via `UnencodableAssumption`, `decode` via `Malformed`), so this
            // cannot fire without one of them having been bypassed — and there
            // is no third constructor.
            out.push(
                assumption_kind_tag(assumption.kind())
                    .expect("invariant: a VerdictDigest holds only wire-encodable assumptions"),
            );
            put_str(&mut out, assumption.name());
        }
        put_u32(&mut out, u32::try_from(self.carrier.arguments.len()).expect("arity"));
        for position in &self.carrier.arguments {
            put_position(&mut out, position);
        }
        put_position(&mut out, &self.carrier.result);
        out.push(DEFEQ_MARKER_KERNEL_AT_CARRIER);
        put_str(&mut out, &self.defeq.admitted_at_rust);
        out
    }

    /// Decode the versioned wire format, fail-closed.
    ///
    /// Everything that is not exactly a complete, well-formed v1 record
    /// refuses: wrong magic, unknown format version, unknown mode or kind
    /// tags, non-UTF-8 text, empty required fields, a malformed digest hex,
    /// truncation anywhere, and trailing bytes after a complete record. There
    /// is no partial or best-effort result — a digest either parses whole or
    /// it does not exist.
    ///
    /// # Errors
    ///
    /// [`DecodeRefusal`], naming what was wrong and where.
    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeRefusal> {
        let mut reader = Reader { bytes, at: 0 };

        let magic = reader.take(VERDICT_DIGEST_MAGIC.len(), "magic")?;
        if magic != VERDICT_DIGEST_MAGIC {
            return Err(DecodeRefusal::NotAVerdictDigest { found: magic.to_vec() });
        }
        let format = reader.u8("format version")?;
        if format != VERDICT_DIGEST_FORMAT_V1 {
            return Err(DecodeRefusal::UnknownFormatVersion {
                found: format,
                supported: VERDICT_DIGEST_FORMAT_V1,
            });
        }

        let decl = reader.non_empty_str("decl")?;
        let kernel_version = reader.non_empty_str("kernel version")?;

        let mode = reader.u8("environment digest mode")?;
        if mode != ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE {
            return Err(DecodeRefusal::Malformed {
                field: "environment digest mode",
                detail: format!(
                    "unknown mode tag {mode}; this reader computes only mode \
                     {ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE} (transitive dependency \
                     closure), and comparing digests computed over different things would \
                     make a mismatch — or a match — meaningless"
                ),
            });
        }
        let hex = reader.str("environment digest")?;
        if hex.len() != 64
            || !hex.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(DecodeRefusal::Malformed {
                field: "environment digest",
                detail: format!(
                    "`{hex}` is not 64 lowercase hex characters, so it cannot be a \
                     canonical SHA-256 rendering"
                ),
            });
        }

        let assumption_count = reader.u32("assumption count")?;
        let mut assumptions = Vec::new();
        for _ in 0..assumption_count {
            let kind = reader.u8("assumption kind")?;
            let name = reader.non_empty_str("assumption name")?;
            let assumption = match kind {
                ASSUMPTION_KIND_TRUST_MARKER => Assumption::trust_marker(name),
                ASSUMPTION_KIND_DOMAIN_AXIOM => Assumption::domain_axiom(name),
                other => {
                    return Err(DecodeRefusal::Malformed {
                        field: "assumption kind",
                        detail: format!(
                            "unknown kind tag {other}; refusing rather than guessing, \
                             because a mis-kinded assumption changes what the disclosure \
                             tells its reader"
                        ),
                    });
                }
            };
            assumptions.push(assumption.map_err(|error| DecodeRefusal::Malformed {
                field: "assumption name",
                detail: error.to_string(),
            })?);
        }

        let argument_count = reader.u32("carrier argument count")?;
        let mut arguments = Vec::new();
        for _ in 0..argument_count {
            arguments.push(read_position(&mut reader)?);
        }
        let result = read_position(&mut reader)?;

        let defeq_tag = reader.u8("defeq evidence tag")?;
        if defeq_tag != DEFEQ_MARKER_KERNEL_AT_CARRIER {
            return Err(DecodeRefusal::Malformed {
                field: "defeq evidence tag",
                detail: format!(
                    "unknown tag {defeq_tag}; the only evidence form this reader admits \
                     is kernel-defeq-at-carrier ({DEFEQ_MARKER_KERNEL_AT_CARRIER})"
                ),
            });
        }
        let admitted_at_rust = reader.non_empty_str("defeq admitted-at")?;

        if reader.at != reader.bytes.len() {
            return Err(DecodeRefusal::TrailingBytes { count: reader.bytes.len() - reader.at });
        }

        Ok(Self {
            decl,
            kernel_version,
            environment: EnvironmentDigest::from_validated_hex(hex),
            assumptions,
            carrier: CarrierDecision { arguments, result },
            defeq: DefeqEvidence { admitted_at_rust },
        })
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, text: &str) {
    // The fields here are names, versions and 64-char hashes; a >4 GiB field
    // is not a state either constructor can produce, and format v1 does not
    // pretend to carry one.
    put_u32(out, u32::try_from(text.len()).expect("a digest field exceeds u32 bytes"));
    out.extend_from_slice(text.as_bytes());
}

fn put_position(out: &mut Vec<u8>, position: &CarrierPosition) {
    put_str(out, &position.clean_type);
    put_str(out, &position.rust_carrier);
    put_u32(out, position.bits);
}

fn read_position(reader: &mut Reader<'_>) -> Result<CarrierPosition, DecodeRefusal> {
    Ok(CarrierPosition {
        clean_type: reader.non_empty_str("carrier clean type")?,
        rust_carrier: reader.non_empty_str("carrier rust type")?,
        bits: reader.u32("carrier bits")?,
    })
}

/// A cursor over wire bytes. Every read checks the remaining length FIRST, so
/// a truncated or hostile input refuses with a named field instead of
/// panicking or over-allocating (`Vec` growth is driven by actual reads, never
/// by a count field a forger controls).
struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize, field: &'static str) -> Result<&'a [u8], DecodeRefusal> {
        let remaining = self.bytes.len() - self.at;
        if remaining < n {
            return Err(DecodeRefusal::Truncated { field, needed: n, remaining });
        }
        let slice = &self.bytes[self.at..self.at + n];
        self.at += n;
        Ok(slice)
    }

    fn u8(&mut self, field: &'static str) -> Result<u8, DecodeRefusal> {
        Ok(self.take(1, field)?[0])
    }

    fn u32(&mut self, field: &'static str) -> Result<u32, DecodeRefusal> {
        let bytes = self.take(4, field)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn str(&mut self, field: &'static str) -> Result<String, DecodeRefusal> {
        let len = self.u32(field)? as usize;
        let bytes = self.take(len, field)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| DecodeRefusal::Malformed {
            field,
            detail: "not valid UTF-8".to_owned(),
        })
    }

    fn non_empty_str(&mut self, field: &'static str) -> Result<String, DecodeRefusal> {
        let text = self.str(field)?;
        if text.is_empty() {
            return Err(DecodeRefusal::Malformed {
                field,
                detail: "empty; this field names something and an unnameable record \
                         cannot be checked or disclosed"
                    .to_owned(),
            });
        }
        Ok(text)
    }
}

/// Why wire bytes were not a verdict digest.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DecodeRefusal {
    /// The bytes do not begin with the digest magic.
    NotAVerdictDigest {
        /// What was found where the magic should be (may be short).
        found: Vec<u8>,
    },
    /// The format version is not one this reader knows.
    UnknownFormatVersion {
        /// The version tag found.
        found: u8,
        /// The one version this reader supports.
        supported: u8,
    },
    /// The input ended inside a field.
    Truncated {
        /// The field being read when the input ran out.
        field: &'static str,
        /// Bytes the field needed.
        needed: usize,
        /// Bytes that were left.
        remaining: usize,
    },
    /// A field was present but not well-formed.
    Malformed {
        /// The field.
        field: &'static str,
        /// What was wrong with it.
        detail: String,
    },
    /// Bytes remained after a complete record.
    TrailingBytes {
        /// How many.
        count: usize,
    },
}

impl DecodeRefusal {
    /// The v7/D3 note: why the bytes were refused, and what to do, with
    /// options.
    #[must_use]
    pub fn note(&self) -> String {
        let options = "options:\n\
             - re-export the certificate from the dependency (a fresh encode from a \
               live VerdictDigest is well-formed by construction);\n\
             - if the bytes came through a transport, check it for truncation or \
               re-encoding — the format is exact bytes, not text;\n\
             - if the producer is a newer toolchain, rebuild THIS crate's toolchain or \
               the dependency so both speak the same format version — there is no \
               best-effort cross-version parse, on purpose.";
        match self {
            Self::NotAVerdictDigest { found } => format!(
                "these bytes are not a verdict digest: expected the `TVDG` magic, found \
                 {found:?}.\n{options}"
            ),
            Self::UnknownFormatVersion { found, supported } => format!(
                "verdict digest format version {found} is unknown to this reader \
                 (supported: {supported}). An unknown version is REFUSED, never \
                 best-effort parsed: a field added in a later version can be exactly \
                 the field whose absence an older reader would fail open on.\n{options}"
            ),
            Self::Truncated { field, needed, remaining } => format!(
                "the verdict digest is truncated inside `{field}`: {needed} byte(s) \
                 needed, {remaining} left.\n{options}"
            ),
            Self::Malformed { field, detail } => {
                format!("the verdict digest's `{field}` is malformed: {detail}.\n{options}")
            }
            Self::TrailingBytes { count } => format!(
                "{count} byte(s) remain after a complete verdict digest record; a \
                 digest with a tail is not the digest it appears to be, so it is \
                 refused whole.\n{options}"
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Minting
// ---------------------------------------------------------------------------

/// Why no verdict digest was minted.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum DigestMintRefusal {
    /// The status is not a kernel verdict, so there is no verdict to digest.
    NotKernelChecked {
        /// The declaration name.
        name: String,
        /// `trust-symbols`' own explanation, verbatim.
        explanation: String,
    },
    /// The producing pipeline never recorded the axiom closure.
    ///
    /// An unrecorded closure cannot cross a crate boundary: the importer's
    /// whole disclosure surface would be a shrug, and `trust-symbols` forbids
    /// softening "nobody looked" into "empty".
    ClosureUnrecorded {
        /// The declaration name.
        name: String,
    },
    /// The closure contains an assumption kind format v1 has no tag for.
    UnencodableAssumption {
        /// The declaration name.
        name: String,
        /// The assumption that could not be carried.
        assumption: String,
    },
    /// Some signature position's discharged carrier width has no wire-v1
    /// representation (it is not an exact fixed width).
    ///
    /// An unbounded-exact carrier is exact **by trusted runtime** — a TCB row,
    /// not a proof — so beyond being unencodable it is also a rest-on the
    /// digest's closure does not name. Refuse rather than invent a number or
    /// smuggle the assumption.
    UnencodableCarrierWidth {
        /// The declaration name.
        name: String,
        /// Which signature position.
        position: String,
        /// The witness rendering of the offending carrier.
        witness: String,
    },
    /// The defeq evidence and the carrier signature disagree about the
    /// admitted type — they are evidence from two different decisions, and a
    /// digest stitched from mismatched evidence would bind nothing.
    EvidenceMismatch {
        /// The declaration name.
        name: String,
        /// What the [`Faithful`] was admitted at.
        faithful_at: String,
        /// What the signature's result position carries at.
        signature_at: String,
    },
}

impl DigestMintRefusal {
    /// The v7/D3 note: why, and what to do, with options.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::NotKernelChecked { name, explanation } => format!(
                "no verdict digest for `{name}`: {explanation}\n\
                 A digest is the wire form of a KERNEL verdict; without one there is \
                 nothing to carry.\n\
                 options:\n\
                 - let the kernel re-check the declaration (the certification audit \
                   produces the status this mint consumes);\n\
                 - if the declaration is PROOF-only, export nothing — proof-position \
                   citation does not need a CALL certificate."
            ),
            Self::ClosureUnrecorded { name } => format!(
                "no verdict digest for `{name}`: its axiom closure was never RECORDED, \
                 and an unrecorded closure cannot be disclosed across a crate boundary \
                 — the importer would be told nothing rests on nothing by omission.\n\
                 options:\n\
                 - route the declaration through the full certification audit so the \
                   closure is recorded (audited-empty is what unlocks re-admission);\n\
                 - keep the declaration crate-local until it is audited."
            ),
            Self::UnencodableAssumption { name, assumption } => format!(
                "no verdict digest for `{name}`: assumption {assumption} has a kind \
                 wire format v1 cannot carry, and collapsing it onto another kind \
                 would change what the disclosure tells its reader.\n\
                 options:\n\
                 - discharge the assumption so it leaves the closure;\n\
                 - extend the wire format with a tag for the new kind (a format \
                   version bump — old readers will then refuse rather than misread, \
                   which is the intended behaviour)."
            ),
            Self::UnencodableCarrierWidth { name, position, witness } => format!(
                "no verdict digest for `{name}`: {position} carries at a width wire \
                 format v1 cannot represent ({witness}). v1 records an exact FIXED \
                 width per position; an unbounded-exact carrier is exact by TRUSTED \
                 RUNTIME — a TCB row, not a proof — so encoding it under v1 would \
                 both invent a number and hide what the verdict rests on.\n\
                 options:\n\
                 - restate the offending position at a fixed-width Clean type \
                   (`UInt8`/`UInt16`/`UInt32`/`UInt64`), which v1 carries exactly;\n\
                 - keep the declaration crate-local, or cite it from proof position \
                   — neither needs a wire certificate;\n\
                 - extend the wire format with a width tag AND a disclosure row for \
                   the runtime rest-on (a format version bump — old readers will \
                   then refuse rather than misread, which is the intended \
                   behaviour)."
            ),
            Self::EvidenceMismatch { name, faithful_at, signature_at } => format!(
                "no verdict digest for `{name}`: the defeq evidence was admitted at \
                 `{faithful_at}` but the carrier signature's result position carries at \
                 `{signature_at}`. These are evidence from two different decisions; a \
                 digest stitched from them would bind neither.\n\
                 options:\n\
                 - pass the CarrierSignature the emission plan actually used (the one \
                   `plan_clean_origin_body` returned for this declaration);\n\
                 - re-run the gate against the intended signature and mint from that \
                   Faithful."
            ),
        }
    }
}

/// Mint the verdict digest for one Clean-origin declaration.
///
/// Every input is sealed evidence or derived from it:
///
/// * `status` — the declaration's [`KernelStatus`]; only `KernelChecked` (whose
///   payload has a private constructor behind `trust-symbols`' sealed
///   authority seam) passes, and the axiom closure is read out of it rather
///   than taken alongside it, for the reason `crate::mint` records: two
///   parameters can desynchronise, one cannot.
/// * `environment` — computed by [`environment_digest_for`], the only public
///   constructor.
/// * `signature` — I4's sealed total-carrier signature.
/// * `faithful` — the gate's sealed verdict. Its presence in the parameter
///   list is the point: **a digest cannot be minted for a declaration whose
///   lowering never passed the gate.** The declaration name is taken from it,
///   so the digest is about the declaration the gate actually checked.
///
/// The kernel version is read from the linked kernel
/// ([`local_kernel_version`]) rather than accepted as a parameter — see that
/// function's docs for why the asymmetry with [`readmit`] is deliberate.
///
/// # Errors
///
/// [`DigestMintRefusal`] — no partial digest exists; a refusal mints nothing.
pub fn mint_verdict_digest(
    status: &KernelStatus,
    environment: EnvironmentDigest,
    signature: &CarrierSignature,
    faithful: &Faithful,
) -> Result<VerdictDigest, DigestMintRefusal> {
    let name = faithful.name();

    if let Err(refusal) = status.require_kernel_check(name) {
        return Err(DigestMintRefusal::NotKernelChecked {
            name: name.to_owned(),
            explanation: refusal.to_string(),
        });
    }

    let closure = status.closure();
    if !closure.is_recorded() {
        return Err(DigestMintRefusal::ClosureUnrecorded { name: name.to_owned() });
    }
    let mut assumptions = Vec::new();
    for assumption in closure.assumptions() {
        if assumption_kind_tag(assumption.kind()).is_none() {
            return Err(DigestMintRefusal::UnencodableAssumption {
                name: name.to_owned(),
                assumption: assumption.to_string(),
            });
        }
        assumptions.push(assumption.clone());
    }

    if faithful.admitted_at() != signature.result().rust() {
        return Err(DigestMintRefusal::EvidenceMismatch {
            name: name.to_owned(),
            faithful_at: format!("{:?}", faithful.admitted_at()),
            signature_at: format!("{:?}", signature.result().rust()),
        });
    }

    let carrier = CarrierDecision::of_signature(signature).map_err(|unencodable| {
        DigestMintRefusal::UnencodableCarrierWidth {
            name: name.to_owned(),
            position: unencodable.position,
            witness: unencodable.witness,
        }
    })?;

    Ok(VerdictDigest {
        decl: name.to_owned(),
        kernel_version: local_kernel_version().to_owned(),
        environment,
        assumptions,
        carrier,
        defeq: DefeqEvidence {
            admitted_at_rust: signature.result().witness().rust_carrier().to_owned(),
        },
    })
}

// ---------------------------------------------------------------------------
// The export seam — the ONE call the compiler's rmeta encode lane makes
// ---------------------------------------------------------------------------

/// Why [`mint_encoded_digest_for_export`] produced no encodable digest.
///
/// One wrapper per refusal family of the sealed chain the seam runs. Every
/// variant's [`Self::note`] delegates to the wrapped refusal's own v7/D3 note,
/// so a refusal here always carries the why and the options.
///
/// On the compiler's export path every one of these is FATAL at the registry
/// span: the subject already minted a `DefId` (which required `KernelChecked`,
/// an audited-empty closure and a total carrier) and already passed the MIR
/// gate (which required a [`Faithful`]), so a refusal at export time means the
/// environment disagrees with itself between runs — the same class as the sole
/// constructor's own "cannot rebuild the environment" fatal.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ExportDigestRefusal {
    /// The emission-side chain refused: the plan, the round trip, or the gate.
    Emit(EmitRefusal),
    /// No environment digest could be computed for the declaration.
    Environment(EnvironmentDigestRefusal),
    /// The digest mint itself refused.
    Mint(DigestMintRefusal),
}

impl ExportDigestRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn decl(&self) -> &str {
        match self {
            Self::Emit(refusal) => refusal.name(),
            Self::Environment(EnvironmentDigestRefusal::NoSuchDeclaration { name }) => name,
            Self::Mint(
                DigestMintRefusal::NotKernelChecked { name, .. }
                | DigestMintRefusal::ClosureUnrecorded { name }
                | DigestMintRefusal::UnencodableAssumption { name, .. }
                | DigestMintRefusal::UnencodableCarrierWidth { name, .. }
                | DigestMintRefusal::EvidenceMismatch { name, .. },
            ) => name,
        }
    }

    /// Whether this refusal is about the compiler's own state rather than
    /// about what the user wrote.
    ///
    /// [`EmitRefusal`] keeps its own classification (a fragment boundary is a
    /// capability refusal even at export time). The other two families are
    /// always compiler defects HERE: an environment that held the declaration
    /// at mint time and lost it by export time, or a status that satisfied
    /// `decide_mint` and fails the digest mint, is the pipeline disagreeing
    /// with itself.
    #[must_use]
    pub fn is_compiler_defect(&self) -> bool {
        match self {
            Self::Emit(refusal) => refusal.is_compiler_defect(),
            Self::Environment(_) | Self::Mint(_) => true,
        }
    }

    /// The v7/D3 note of the wrapped refusal, verbatim.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::Emit(refusal) => refusal.note(),
            Self::Environment(refusal) => refusal.note(),
            Self::Mint(refusal) => refusal.note(),
        }
    }
}

/// Mint and ENCODE the verdict digest for one Clean-origin declaration, as a
/// single sealed step — **the one seam the compiler's rmeta export provider
/// calls** (`rustc_mir_transform::clean_origin_export`, the local arm of the
/// `trust_clean_verdict_digest` query).
///
/// The chain, in order, every step fail-closed:
///
/// 1. [`plan_clean_origin_body`] — side A re-read from the kernel environment;
/// 2. [`admit_lowering`] — the round trip over `extracted`, which re-earns a
///    FRESH [`Faithful`] against exactly that body;
/// 3. [`environment_digest_for`] — the dependency-closure hash;
/// 4. [`mint_verdict_digest`] — the sealed mint, from that `Faithful`;
/// 5. [`VerdictDigest::encode`] — the wire bytes the rmeta table carries.
///
/// # `extracted` must be the extraction of the body being SERIALIZED
///
/// The I7 plan's decision (a): the `Faithful` earned inside the MIR gate is
/// deliberately dropped and stays dropped — a session-carried token vanishes
/// on a warm cache, and worse, could have been earned against a different
/// body than the one the encoder is writing out. So the caller extracts
/// `tcx.optimized_mir(def)` — the cached body rmeta serializes — and this
/// function re-earns its own `Faithful` against it. The digest is then a
/// claim about the bytes that actually travel, at the cost of one more
/// kernel run per exporting crate (recorded, the same stance as the design
/// doc's §6d second run). The `Faithful` never escapes: it is consumed by
/// the mint and dropped, the same discipline as the sole constructor's.
///
/// # Errors
///
/// [`ExportDigestRefusal`]. No partial digest exists; a refusal encodes
/// nothing — and the compiler-side caller must treat that as FATAL, never as
/// "skip the row": a missing digest row is how importers recognise ordinary
/// Rust, so encoding nothing for a registry def would fail OPEN.
pub fn mint_encoded_digest_for_export(
    env: &Environment,
    name: &str,
    status: &KernelStatus,
    extracted: &VerifiableFunction,
) -> Result<Vec<u8>, ExportDigestRefusal> {
    let plan = plan_clean_origin_body(env, name).map_err(ExportDigestRefusal::Emit)?;
    let faithful = admit_lowering(env, &plan, extracted).map_err(ExportDigestRefusal::Emit)?;
    let environment =
        environment_digest_for(env, name).map_err(ExportDigestRefusal::Environment)?;
    let digest = mint_verdict_digest(status, environment, plan.signature(), &faithful)
        .map_err(ExportDigestRefusal::Mint)?;
    Ok(digest.encode())
}

// ---------------------------------------------------------------------------
// Re-admission
// ---------------------------------------------------------------------------

/// Evidence that an imported verdict digest was checked, field by field,
/// against the LOCAL kernel version, the LOCAL environment content, and the
/// LOCAL carrier decision.
///
/// **Constructible only by [`readmit`].** The fields are private and there is
/// no public constructor — the same sealing as [`crate::gate::Faithful`] and
/// [`crate::mint::MintGrant`], and pinned the same way theirs is:
///
/// ```compile_fail,E0451
/// let forged = trust_clean_origin::admission::Readmitted {
///     decl: String::new(),
///     kernel_version: String::new(),
///     admitted_at_rust: String::new(),
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Readmitted {
    decl: String,
    kernel_version: String,
    admitted_at_rust: String,
}

impl Readmitted {
    /// The re-admitted declaration.
    #[must_use]
    pub fn decl(&self) -> &str {
        &self.decl
    }

    /// The kernel version both sides agree on.
    #[must_use]
    pub fn kernel_version(&self) -> &str {
        &self.kernel_version
    }

    /// The Rust carrier type the verdict is admitted at, re-confirmed against
    /// the local carrier decision.
    #[must_use]
    pub fn admitted_at_rust(&self) -> &str {
        &self.admitted_at_rust
    }
}

/// Why an imported verdict digest was refused.
///
/// Every variant names what mismatched and its note names the options — a
/// refusal with no next step is a defect (ruling v7/D3), and the reader of
/// these notes is whoever has to decide whether to rebuild, re-check, or
/// report.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ReadmissionRefusal {
    /// The digest was minted under a different kernel than the one deciding
    /// here. **This is the acceptance control's case**: refuse, never accept
    /// on any other coincidence of fields.
    KernelVersionSkew {
        /// The declaration.
        decl: String,
        /// The kernel the verdict was minted under.
        minted_under: String,
        /// The kernel deciding now.
        local: String,
    },
    /// The verdict rests on named assumptions, and re-admission here is
    /// re-admission to the CALL lane, which requires an audited-empty closure
    /// for the same reason the mint does.
    AssumptionBearing {
        /// The declaration.
        decl: String,
        /// The assumptions, disclosed by name.
        assumptions: Vec<String>,
    },
    /// The local environment does not hold the declaration at all.
    DeclarationMissing {
        /// The declaration.
        decl: String,
    },
    /// The local dependency closure hashes differently than the one the
    /// verdict was minted over.
    EnvironmentSkew {
        /// The declaration.
        decl: String,
        /// The digest's environment hash.
        imported: String,
        /// The locally recomputed hash.
        local: String,
    },
    /// The digest claims an empty closure, but a local walk of the
    /// declaration's dependency DAG finds assumptions it never disclosed.
    ///
    /// This is the belt-and-braces lane against a lying producer: the local
    /// `axiom_deps` walk never re-typechecks (it cannot see a structurally
    /// inserted term — the softening `trust-symbols` warns about), so it can
    /// only REFUTE an empty-closure claim, never certify one. Refutation is
    /// exactly what an importer can do cheaply, so it does.
    UndisclosedAssumptions {
        /// The declaration.
        decl: String,
        /// What the local walk found, by name.
        found: Vec<String>,
    },
    /// The local carrier map refuses the declaration's signature, so there is
    /// no local carrier decision to compare against.
    LocalCarrierRefused {
        /// The declaration.
        decl: String,
        /// I4's refusal, verbatim.
        refusal: CarrierRefused,
    },
    /// The LOCAL carrier decision admits some position at a width wire format
    /// v1 cannot represent, so there is no comparable local record. A v1
    /// digest only ever claims exact fixed widths; a local decision outside
    /// them is a disagreement between the two compilers' carrier policies,
    /// and comparing an invented number would hide it.
    LocalCarrierWidthUnencodable {
        /// The declaration.
        decl: String,
        /// Which signature position.
        position: String,
        /// The witness rendering of the local carrier at that position.
        witness: String,
    },
    /// The imported carrier decision and the local one disagree at some
    /// position.
    CarrierSkew {
        /// The declaration.
        decl: String,
        /// Which position disagreed (or `arity`).
        position: String,
        /// The imported decision at that position.
        imported: String,
        /// The local decision at that position.
        local: String,
    },
    /// The defeq evidence marker names a carrier type that is not the local
    /// result carrier.
    DefeqSkew {
        /// The declaration.
        decl: String,
        /// What the marker claims the agreement was admitted at.
        claimed: String,
        /// The local result carrier.
        local: String,
    },
}

impl ReadmissionRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn decl(&self) -> &str {
        match self {
            Self::KernelVersionSkew { decl, .. }
            | Self::AssumptionBearing { decl, .. }
            | Self::DeclarationMissing { decl }
            | Self::EnvironmentSkew { decl, .. }
            | Self::UndisclosedAssumptions { decl, .. }
            | Self::LocalCarrierRefused { decl, .. }
            | Self::LocalCarrierWidthUnencodable { decl, .. }
            | Self::CarrierSkew { decl, .. }
            | Self::DefeqSkew { decl, .. } => decl,
        }
    }

    /// The v7/D3 note: what mismatched, and the options.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::KernelVersionSkew { decl, minted_under, local } => format!(
                "the imported certificate for `{decl}` was minted under Clean kernel \
                 {minted_under}, but this build links kernel {local}. A kernel verdict \
                 does not survive a kernel change — defeq itself can differ between \
                 versions — so the certificate is refused REGARDLESS of every other \
                 field matching.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain, so its certificates are \
                   minted under kernel {local};\n\
                 - re-check the declaration locally (the local environment holds it; \
                   the re-check lane beside `readmit` is the documented seam — until it \
                   lands, rebuilding the dependency is the same computation done in the \
                   dependency's build);\n\
                 - if the skew is unexpected — both crates supposedly built by one \
                   toolchain — report it: something pinned two kernels into one \
                   workspace."
            ),
            Self::AssumptionBearing { decl, assumptions } => {
                let listed = assumptions.join(", ");
                format!(
                    "the imported certificate for `{decl}` is kernel-checked but rests \
                     on assumptions: {listed}. Re-admission here is re-admission to the \
                     CALL lane, and calling `{decl}` would put those assumptions behind \
                     an emitted value where nothing discloses them.\n\
                     options:\n\
                     - discharge the assumptions in the exporting crate and rebuild it;\n\
                     - cite `{decl}` from proof position instead, where the closure is \
                       disclosed by name rather than hidden behind a value."
                )
            }
            Self::DeclarationMissing { decl } => format!(
                "the imported certificate names `{decl}`, but the local Clean \
                 environment does not hold that declaration, so there is nothing to \
                 re-admit a verdict ABOUT.\n\
                 options:\n\
                 - load the dependency's Clean declarations before re-admitting its \
                   certificates (the rustc-side metadata lane is what transports them; \
                   order matters);\n\
                 - if the declaration was renamed or removed upstream, rebuild against \
                   the current dependency — the certificate is stale."
            ),
            Self::EnvironmentSkew { decl, imported, local } => format!(
                "the imported certificate for `{decl}` was minted over a dependency \
                 closure hashing {imported}, but the local closure hashes {local}. Some \
                 declaration `{decl}` depends on differs here — same names, different \
                 content — and a kernel verdict is only about the content it was \
                 decided over.\n\
                 options:\n\
                 - rebuild the dependency so both sides hold the same declarations \
                   (the usual cause is a half-updated workspace: one crate rebuilt, its \
                   dependent not);\n\
                 - if the local change is deliberate, the verdict must be re-derived — \
                   re-check locally rather than importing;\n\
                 - report it if the two crates SHOULD be identical: an environment skew \
                   under one lockfile means the build graph disagrees with itself."
            ),
            Self::UndisclosedAssumptions { decl, found } => {
                let listed = found.join(", ");
                format!(
                    "the imported certificate for `{decl}` claims an audited-empty \
                     axiom closure, but a local walk of the declaration's dependency \
                     DAG finds: {listed}. A certificate that under-discloses is refused \
                     outright — the disclosure is the product.\n\
                     options:\n\
                     - re-run the exporting crate's certification audit and re-export \
                       (an honest audit cannot miss a named constant in the DAG);\n\
                     - report the producer: a digest claiming empty over a closure that \
                       names `{listed}` was minted by something that lied or skipped \
                       the audit."
                )
            }
            Self::LocalCarrierRefused { decl, refusal } => format!(
                "the imported certificate for `{decl}` carries a carrier decision, but \
                 the LOCAL carrier map refuses the declaration's signature: \
                 {refusal:?}.\n\
                 The import cannot be admitted at a type the local compiler would not \
                 grant — that would let an old certificate override a carrier-map fix.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain so both sides make the \
                   same carrier decision;\n\
                 - if the local refusal is the surprise, that is a carrier-map \
                   regression: report it with this note."
            ),
            Self::LocalCarrierWidthUnencodable { decl, position, witness } => format!(
                "the imported certificate for `{decl}` claims exact fixed widths (the \
                 only widths wire format v1 carries), but the LOCAL carrier decision \
                 admits {position} at a width v1 cannot represent ({witness}). The two \
                 compilers' carrier policies disagree, and comparing an invented \
                 number would hide that.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain so both sides make the \
                   same carrier decision;\n\
                 - restate the declaration's {position} at a fixed-width Clean type \
                   and rebuild both sides;\n\
                 - cite `{decl}` from proof position instead — proof position needs \
                   no carrier decision."
            ),
            Self::CarrierSkew { decl, position, imported, local } => format!(
                "the imported certificate for `{decl}` admits {position} at \
                 `{imported}`, but the local carrier decision is `{local}`. Emitting a \
                 call at the imported type would make the two crates disagree about \
                 the bytes of every value crossing the boundary.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain (carrier decisions are \
                   compiler policy, and the two compilers here disagree);\n\
                 - if the imported decision looks right and the local one wrong, that \
                   is a carrier-map regression on THIS side: report it rather than \
                   forcing the import."
            ),
            Self::DefeqSkew { decl, claimed, local } => format!(
                "the imported certificate for `{decl}` says the faithfulness agreement \
                 was admitted at `{claimed}`, but the local result carrier is \
                 `{local}`. The defeq verdict is only meaningful AT the carrier it was \
                 admitted at.\n\
                 options:\n\
                 - rebuild the dependency so the gate re-runs at the current carrier;\n\
                 - report it if the carrier positions matched but this marker did not: \
                   that combination means the certificate was assembled from mismatched \
                   evidence, which the mint refuses — so it did not come from the mint."
            ),
        }
    }
}

/// Decide whether an imported verdict digest stands in the LOCAL crate.
///
/// The comparisons, in reporting order (coarsest first, the same rationale as
/// `crate::mint::decide_mint` — any failure refuses, so order is not
/// load-bearing for soundness):
///
/// 1. **kernel version** — `digest` vs `local_kernel_version`. Skew refuses;
///    the re-check alternative is a documented seam, not built (module docs).
/// 2. **axiom closure** — must be empty (audited-empty by construction: the
///    mint refuses unrecorded closures, so an empty list on an honest wire is
///    an audit that found nothing). Non-empty refuses re-admission to CALL.
/// 3. **declaration present** — the local environment must hold the subject.
/// 4. **environment digest** — recomputed over `local_env` by the same
///    [`environment_digest_for`] and compared.
/// 5. **disclosure cross-audit** — the local `axiom_deps` walk must not find
///    assumptions the digest failed to name. Refutation-only; see
///    [`ReadmissionRefusal::UndisclosedAssumptions`].
/// 6. **carrier decision** — recomputed locally from the declaration's type
///    via the local carrier map and compared position by position.
/// 7. **defeq marker** — must name the local result carrier.
///
/// `local_kernel_version` is a parameter rather than read from the linked
/// kernel so the decision stays a total function of its inputs (the same
/// purity rule `crate::mint` records) — the production caller passes
/// [`local_kernel_version`]`()`.
///
/// # Errors
///
/// [`ReadmissionRefusal`] naming the first mismatch. There is no partial
/// re-admission and no "accepted with warnings" mode: an imported verdict
/// either stands whole or it does not stand.
pub fn readmit(
    digest: &VerdictDigest,
    local_kernel_version: &str,
    local_env: &Environment,
) -> Result<Readmitted, ReadmissionRefusal> {
    let decl = digest.decl.as_str();

    // ── 1. the acceptance control: a different kernel refuses, always ──────
    if digest.kernel_version != local_kernel_version {
        return Err(ReadmissionRefusal::KernelVersionSkew {
            decl: decl.to_owned(),
            minted_under: digest.kernel_version.clone(),
            local: local_kernel_version.to_owned(),
        });
    }

    // ── 2. assumption-bearing never re-admits to CALL ──────────────────────
    if !digest.assumptions.is_empty() {
        return Err(ReadmissionRefusal::AssumptionBearing {
            decl: decl.to_owned(),
            assumptions: digest.assumptions.iter().map(|a| a.name().to_owned()).collect(),
        });
    }

    // ── 3+4. the local content must hash to what the verdict was over ──────
    let local_digest = match environment_digest_for(local_env, decl) {
        Ok(digest) => digest,
        Err(EnvironmentDigestRefusal::NoSuchDeclaration { .. }) => {
            return Err(ReadmissionRefusal::DeclarationMissing { decl: decl.to_owned() });
        }
    };
    if local_digest != digest.environment {
        return Err(ReadmissionRefusal::EnvironmentSkew {
            decl: decl.to_owned(),
            imported: digest.environment.hex.clone(),
            local: local_digest.hex.clone(),
        });
    }

    // ── 5. refute an empty-closure claim if the local DAG names assumptions ─
    let kernel_name = Name::from_string(decl);
    match local_env.axiom_deps(&kernel_name) {
        None => {
            // Unreachable after step 3/4, but a fail-closed arm rather than an
            // unwrap: if the environment disagrees with itself, refuse.
            return Err(ReadmissionRefusal::DeclarationMissing { decl: decl.to_owned() });
        }
        Some(found) if !found.is_empty() => {
            let mut names: Vec<String> = found.iter().map(ToString::to_string).collect();
            names.sort();
            return Err(ReadmissionRefusal::UndisclosedAssumptions {
                decl: decl.to_owned(),
                found: names,
            });
        }
        Some(_) => {}
    }

    // ── 6. the LOCAL carrier decision, recomputed, position by position ────
    let Some(info) = local_env.get_const(&kernel_name) else {
        return Err(ReadmissionRefusal::DeclarationMissing { decl: decl.to_owned() });
    };
    let local_signature = carrier_signature_for(&info.type_).map_err(|refusal| {
        ReadmissionRefusal::LocalCarrierRefused { decl: decl.to_owned(), refusal }
    })?;
    let local_decision = CarrierDecision::of_signature(&local_signature).map_err(|unencodable| {
        ReadmissionRefusal::LocalCarrierWidthUnencodable {
            decl: decl.to_owned(),
            position: unencodable.position,
            witness: unencodable.witness,
        }
    })?;

    if local_decision.arguments.len() != digest.carrier.arguments.len() {
        return Err(ReadmissionRefusal::CarrierSkew {
            decl: decl.to_owned(),
            position: "arity".to_owned(),
            imported: format!("{} argument(s)", digest.carrier.arguments.len()),
            local: format!("{} argument(s)", local_decision.arguments.len()),
        });
    }
    for (index, (imported, local)) in
        digest.carrier.arguments.iter().zip(local_decision.arguments.iter()).enumerate()
    {
        if imported != local {
            return Err(ReadmissionRefusal::CarrierSkew {
                decl: decl.to_owned(),
                position: format!("argument {index}"),
                imported: imported.describe(),
                local: local.describe(),
            });
        }
    }
    if digest.carrier.result != local_decision.result {
        return Err(ReadmissionRefusal::CarrierSkew {
            decl: decl.to_owned(),
            position: "the result".to_owned(),
            imported: digest.carrier.result.describe(),
            local: local_decision.result.describe(),
        });
    }

    // ── 7. the defeq marker must name the local result carrier ─────────────
    if digest.defeq.admitted_at_rust != local_decision.result.rust_carrier {
        return Err(ReadmissionRefusal::DefeqSkew {
            decl: decl.to_owned(),
            claimed: digest.defeq.admitted_at_rust.clone(),
            local: local_decision.result.rust_carrier.clone(),
        });
    }

    Ok(Readmitted {
        decl: decl.to_owned(),
        kernel_version: local_kernel_version.to_owned(),
        admitted_at_rust: local_decision.result.rust_carrier.clone(),
    })
}

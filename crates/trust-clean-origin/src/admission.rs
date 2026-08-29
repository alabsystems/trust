// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I7, crate-side half — **the verdict digest and re-admission on import**.
//!
//! The decision doc's I7 row, verbatim:
//!
//! > Cross-crate: Clean-origin MIR encoding + **re-admission on import**. The
//! > wire unit is a verdict digest (kernel version, environment digest, axiom
//! > closure, carrier decision, faithfulness certificate) — **never a source hash,
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
//! | faithfulness evidence | *how the kernel proved agreement, and at which carrier* | refuse ([`ReadmissionRefusal::FaithfulnessSkew`]) |
//!
//! # Sealing — the same discipline as the gate and the mint
//!
//! [`Readmitted`] is constructible only by [`readmit`], exactly as
//! [`crate::gate::Faithful`] is constructible only by
//! [`crate::gate::check_faithful`]. A consumer holding a `Readmitted` holds
//! evidence that every field of the digest was compared against the local
//! facts. On the mint side, [`mint_verdict_digest`] demands a
//! [`crate::gate::Faithful`] — so a digest cannot claim faithfulness evidence that was
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
//! # Local re-checking is the authority
//!
//! Re-admission is deliberately split into sealed phases. [`preflight_wire`]
//! rejects kernel skew and assumptions before the importer rebuilds an
//! environment. [`bind_readmission`] then binds the claim to the local
//! dependency closure and carrier decision without doing proof search. Finally
//! [`locally_recheck_imported_body`] runs the actual imported body through the
//! local gate, and [`readmit`] accepts only when that unforgeable local evidence
//! matches the preflight by declaration, environment, carrier, and proof
//! method. Wire bytes can describe a method; they can never choose one.
//!
//! Kernel-version skew still refuses rather than silently translating a
//! verdict. Rebuilding the dependency is the supported way to mint a new wire
//! record under the local kernel; once it arrives, the importer independently
//! rechecks the transported body as above.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use clean_kernel::{Environment, ExprVisitor, LevelVec, Name};
use trust_clean_carrier::{CarrierRefused, CarrierSignature, carrier_signature_for};
use trust_symbols::{Assumption, AssumptionKind, CarrierWidth, KernelStatus};
use trust_types::{Ty, VerifiableFunction};

use crate::emit::{CleanOriginPlan, EmitRefusal, admit_lowering, plan_clean_origin_body};
use crate::gate::{Faithful, FaithfulnessMethod};

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
/// unrepresentable. (The *re-admission* side passes the local version to
/// [`preflight_wire`] because there the value is a comparison input, not a
/// claim.)
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
/// all, because [`preflight_wire`] refuses on kernel-version skew before the
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
                let levels =
                    info.level_params.iter().map(ToString::to_string).collect::<Vec<_>>().join(",");
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
// Carrier decision and faithfulness evidence
// ---------------------------------------------------------------------------

/// One signature position of the carrier decision: which Clean type was
/// carried, at which Rust type, and with which exact extent.
///
/// The strings are the [`trust_symbols::CarrierWitness`] renderings — the
/// discharged obligation's own record of the pairing — so the wire carries
/// what was PROVED, not a re-derivation.
///
/// Wire format v1 could represent only [`CarrierWidth::Bits`]. Format v2
/// carries a width tag, so [`CarrierWidth::UnboundedExact`] is represented
/// honestly rather than collapsed onto a fictitious bit count. The exact Rust
/// carrier name remains part of the decision: for an unbounded carrier it
/// identifies the trusted runtime whose agreement the local carrier map must
/// independently re-confirm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierPosition {
    clean_type: String,
    rust_carrier: String,
    width: CarrierWidth,
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

    /// The discharged carrier extent.
    #[must_use]
    pub fn width(&self) -> CarrierWidth {
        self.width
    }

    fn describe(&self) -> String {
        match self.width {
            CarrierWidth::Bits(bits) => {
                format!("{} carried by {} ({bits} bits)", self.clean_type, self.rust_carrier)
            }
            CarrierWidth::UnboundedExact => format!(
                "{} carried by {} (unbounded, exact by trusted runtime)",
                self.clean_type, self.rust_carrier
            ),
        }
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
    /// Project a sealed I4 signature onto its v2 wire record.
    ///
    /// `CarrierWidth` is deliberately exhaustive. A future extent therefore
    /// breaks this construction and the wire encoder at compile time instead
    /// of silently inheriting either existing tag.
    #[must_use]
    pub fn of_signature(signature: &CarrierSignature) -> Self {
        fn position(carrier: &trust_clean_carrier::Carrier) -> CarrierPosition {
            let witness = carrier.witness();
            match witness.width() {
                CarrierWidth::Bits(bits) => CarrierPosition {
                    clean_type: witness.clean_type().to_owned(),
                    rust_carrier: witness.rust_carrier().to_owned(),
                    width: CarrierWidth::Bits(bits),
                },
                CarrierWidth::UnboundedExact => CarrierPosition {
                    clean_type: witness.clean_type().to_owned(),
                    rust_carrier: witness.rust_carrier().to_owned(),
                    width: CarrierWidth::UnboundedExact,
                },
            }
        }
        let mut arguments = Vec::with_capacity(signature.arguments().len());
        for carrier in signature.arguments() {
            arguments.push(position(carrier));
        }
        let result = position(signature.result());
        Self { arguments, result }
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

/// Wire tags for the two kernel evidence forms accepted by the faithfulness
/// gate. They remain distinct on wire: structural induction is never renamed
/// to definitional equality.
const FAITHFULNESS_KERNEL_DEFEQ_AT_CARRIER: u8 = 1;
const FAITHFULNESS_KERNEL_INDUCTION_AT_CARRIER: u8 = 2;

/// The wire tag for one faithfulness method, or `None` for an evidence form
/// the format deliberately does not spell.
///
/// R1 accounting: the per-defining-equation judgment
/// ([`crate::gate::check_faithful_equations`], §6e as amended) has NO tag —
/// a wire-format statement of the per-equation mode is its own reviewed
/// change, and collapsing it onto either whole-term tag would tell the
/// importer a judgment happened that never did. [`mint_verdict_digest`]
/// refuses on `None` ([`DigestMintRefusal::UnencodableFaithfulness`]), and
/// `decode` has no tag that maps back to it, so a [`VerdictDigest`] holds
/// only spellable evidence. (The match is deliberately exhaustive: a new
/// method variant breaks it at compile time rather than inheriting a tag.)
fn faithfulness_method_tag(method: FaithfulnessMethod) -> Option<u8> {
    match method {
        FaithfulnessMethod::DefinitionalEquality => Some(FAITHFULNESS_KERNEL_DEFEQ_AT_CARRIER),
        FaithfulnessMethod::StructuralInduction => Some(FAITHFULNESS_KERNEL_INDUCTION_AT_CARRIER),
        // R2 accounting, same rule, RE-AFFIRMED when the lane was wired
        // (2026-08-22): an F-layer verdict
        // ([`crate::gate::check_faithful_wf_functional`]) is not whole-term
        // defeq. It additionally rests on a BORROW and a CLOSURE AUDIT taken
        // in THIS crate's environment — and on this lane the closure is not
        // disclosure metadata, it is the other half of the TERMINATION
        // argument (probe c1). No wire field carries either, so it has no tag
        // and stays crate-local. Adding one is a reviewed format change that
        // lands WITH the fields, and whose decode side must refuse an unknown
        // tag rather than best-effort parse it.
        FaithfulnessMethod::PerEquationDefeq | FaithfulnessMethod::WellFoundedFunctionalDefeq => {
            None
        }
    }
}

/// The faithfulness evidence marker: how the gate established agreement, and
/// the Rust carrier type at which it admitted the lowering.
///
/// On the mint side this is constructible only from a [`crate::gate::Faithful`]
/// (via [`mint_verdict_digest`]), so a freshly minted digest cannot claim
/// faithfulness evidence that was never produced. A DECODED marker is a claim like
/// the rest of the wire unit; [`readmit`] checks it against the locally
/// recomputed carrier decision, and the rustc-side metadata channel is what
/// authenticates the producer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulnessEvidence {
    method: FaithfulnessMethod,
    admitted_at_rust: String,
}

impl FaithfulnessEvidence {
    /// The proof method recorded by the sealed gate.
    #[must_use]
    pub fn method(&self) -> FaithfulnessMethod {
        self.method
    }

    /// The Rust carrier type the kernel agreement was admitted at.
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

/// Historical wire format still accepted by the decoder.
///
/// The version is CHECKED, not advisory: an unknown version is a refusal,
/// never a best-effort parse — a field added in v2 could be exactly the field
/// whose absence a v1 best-effort reader would fail open on.
pub const VERDICT_DIGEST_FORMAT_V1: u8 = 1;
/// Current wire format: adds explicit faithfulness-method and carrier-width
/// tags. The encoder always writes v2; the decoder accepts complete v1 and v2
/// records and refuses every unknown version.
pub const VERDICT_DIGEST_FORMAT_V2: u8 = 2;

const CARRIER_WIDTH_FIXED_BITS: u8 = 1;
const CARRIER_WIDTH_UNBOUNDED_EXACT: u8 = 2;

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
    faithfulness: FaithfulnessEvidence,
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

    /// The kernel faithfulness evidence marker.
    #[must_use]
    pub fn faithfulness(&self) -> &FaithfulnessEvidence {
        &self.faithfulness
    }

    /// Encode to the versioned wire format.
    ///
    /// Layout (v2, all integers little-endian, strings `u32` byte-length +
    /// UTF-8):
    ///
    /// ```text
    /// magic "TVDG" · format u8 · decl · kernel_version
    /// · env-mode u8 · env-digest-hex
    /// · assumption-count u32 · (kind u8 · name)*
    /// · argument-count u32
    /// · (clean · rust · width-tag u8 · [bits u32])* · result(same)
    /// · faithfulness-tag u8 · admitted-at
    /// ```
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&VERDICT_DIGEST_MAGIC);
        out.push(VERDICT_DIGEST_FORMAT_V2);
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
            put_position_v2(&mut out, position);
        }
        put_position_v2(&mut out, &self.carrier.result);
        // Both constructors refuse an unspellable method (`mint_verdict_digest`
        // via `UnencodableFaithfulness`, `decode` by having no tag for one), so
        // this cannot fire without one of them having been bypassed — and there
        // is no third constructor. Same discipline as the assumption tags above.
        out.push(
            faithfulness_method_tag(self.faithfulness.method)
                .expect("invariant: a VerdictDigest holds only wire-encodable faithfulness"),
        );
        put_str(&mut out, &self.faithfulness.admitted_at_rust);
        out
    }

    /// Decode the versioned wire format, fail-closed.
    ///
    /// Everything that is not exactly a complete, well-formed v1/v2 record
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
        if !matches!(format, VERDICT_DIGEST_FORMAT_V1 | VERDICT_DIGEST_FORMAT_V2) {
            return Err(DecodeRefusal::UnknownFormatVersion {
                found: format,
                supported: VERDICT_DIGEST_FORMAT_V2,
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
        if hex.len() != 64 || !hex.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
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
            arguments.push(read_position(&mut reader, format)?);
        }
        let result = read_position(&mut reader, format)?;

        let faithfulness_tag = reader.u8("faithfulness evidence tag")?;
        let method = match (format, faithfulness_tag) {
            (
                VERDICT_DIGEST_FORMAT_V1 | VERDICT_DIGEST_FORMAT_V2,
                FAITHFULNESS_KERNEL_DEFEQ_AT_CARRIER,
            ) => FaithfulnessMethod::DefinitionalEquality,
            (VERDICT_DIGEST_FORMAT_V2, FAITHFULNESS_KERNEL_INDUCTION_AT_CARRIER) => {
                FaithfulnessMethod::StructuralInduction
            }
            _ => {
                return Err(DecodeRefusal::Malformed {
                    field: "faithfulness evidence tag",
                    detail: format!(
                        "unknown tag {faithfulness_tag} for format v{format}; v1 admits \
                         only kernel-defeq-at-carrier \
                         ({FAITHFULNESS_KERNEL_DEFEQ_AT_CARRIER}), while v2 also admits \
                         kernel-induction-at-carrier \
                         ({FAITHFULNESS_KERNEL_INDUCTION_AT_CARRIER})"
                    ),
                });
            }
        };
        let admitted_at_rust = reader.non_empty_str("faithfulness admitted-at")?;

        if reader.at != reader.bytes.len() {
            return Err(DecodeRefusal::TrailingBytes { count: reader.bytes.len() - reader.at });
        }

        Ok(Self {
            decl,
            kernel_version,
            environment: EnvironmentDigest::from_validated_hex(hex),
            assumptions,
            carrier: CarrierDecision { arguments, result },
            faithfulness: FaithfulnessEvidence { method, admitted_at_rust },
        })
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_str(out: &mut Vec<u8>, text: &str) {
    // The fields here are names, versions and 64-char hashes; a >4 GiB field
    // is not a state either constructor can produce, and the wire does not
    // pretend to carry one.
    put_u32(out, u32::try_from(text.len()).expect("a digest field exceeds u32 bytes"));
    out.extend_from_slice(text.as_bytes());
}

fn put_position_v2(out: &mut Vec<u8>, position: &CarrierPosition) {
    put_str(out, &position.clean_type);
    put_str(out, &position.rust_carrier);
    match position.width {
        CarrierWidth::Bits(bits) => {
            out.push(CARRIER_WIDTH_FIXED_BITS);
            put_u32(out, bits);
        }
        CarrierWidth::UnboundedExact => out.push(CARRIER_WIDTH_UNBOUNDED_EXACT),
    }
}

fn read_position(reader: &mut Reader<'_>, format: u8) -> Result<CarrierPosition, DecodeRefusal> {
    let clean_type = reader.non_empty_str("carrier clean type")?;
    let rust_carrier = reader.non_empty_str("carrier rust type")?;
    let width = if format == VERDICT_DIGEST_FORMAT_V1 {
        CarrierWidth::Bits(reader.u32("carrier bits")?)
    } else {
        match reader.u8("carrier width tag")? {
            CARRIER_WIDTH_FIXED_BITS => CarrierWidth::Bits(reader.u32("carrier bits")?),
            CARRIER_WIDTH_UNBOUNDED_EXACT => CarrierWidth::UnboundedExact,
            other => {
                return Err(DecodeRefusal::Malformed {
                    field: "carrier width tag",
                    detail: format!(
                        "unknown tag {other}; v2 admits fixed-bits \
                         ({CARRIER_WIDTH_FIXED_BITS}) or unbounded-exact \
                         ({CARRIER_WIDTH_UNBOUNDED_EXACT}), and guessing would change \
                         the value domain crossing the crate boundary"
                    ),
                });
            }
        }
    };
    Ok(CarrierPosition { clean_type, rust_carrier, width })
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
        String::from_utf8(bytes.to_vec())
            .map_err(|_| DecodeRefusal::Malformed { field, detail: "not valid UTF-8".to_owned() })
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
        /// The newest/current format version this reader supports.
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
    /// The closure contains an assumption kind the current format has no tag for.
    UnencodableAssumption {
        /// The declaration name.
        name: String,
        /// The assumption that could not be carried.
        assumption: String,
    },
    /// The faithfulness evidence and the carrier signature disagree about the
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
    /// The gate's evidence form has no wire spelling in the current format.
    ///
    /// R1 accounting: a `StructuralNatRec` verdict is earned by the
    /// per-defining-equation judgment
    /// ([`crate::gate::check_faithful_equations`]), and
    /// [`FaithfulnessEvidence`] deliberately has no spelling that
    /// distinguishes it from whole-term defeq — a wire-format statement of
    /// the per-equation mode is its own reviewed change. Collapsing it onto
    /// either existing tag would tell the importer a whole-term judgment
    /// happened that never did, so the mint refuses instead.
    UnencodableFaithfulness {
        /// The declaration name.
        name: String,
        /// The evidence form with no wire spelling.
        method: FaithfulnessMethod,
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
                 the current wire format cannot carry, and collapsing it onto another kind \
                 would change what the disclosure tells its reader.\n\
                 options:\n\
                 - discharge the assumption so it leaves the closure;\n\
                 - extend the wire format with a tag for the new kind (a format \
                   version bump — old readers will then refuse rather than misread, \
                   which is the intended behaviour)."
            ),
            Self::EvidenceMismatch { name, faithful_at, signature_at } => format!(
                "no verdict digest for `{name}`: the faithfulness evidence was admitted at \
                 `{faithful_at}` but the carrier signature's result position carries at \
                 `{signature_at}`. These are evidence from two different decisions; a \
                 digest stitched from them would bind neither.\n\
                 options:\n\
                 - pass the CarrierSignature the emission plan actually used (the one \
                   `plan_clean_origin_body` returned for this declaration);\n\
                 - re-run the gate against the intended signature and mint from that \
                   Faithful."
            ),
            Self::UnencodableFaithfulness { name, method } => format!(
                "no verdict digest for `{name}`: its faithfulness was established by \
                 {method:?}, an evidence form the current wire format deliberately has \
                 no tag for — spelling it as whole-term defeq or induction would tell \
                 the importer a judgment happened that never did.\n\
                 options:\n\
                 - keep the declaration crate-local and call it there (the local gate \
                   already admitted it);\n\
                 - restate the definition inside a whole-term-gated shape so its \
                   evidence has a wire spelling;\n\
                 - extend the wire format with a per-equation evidence tag (a format \
                   version bump and its own reviewed change — old readers will then \
                   refuse rather than misread, which is the intended behaviour)."
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

    if faithfulness_method_tag(faithful.method()).is_none() {
        return Err(DigestMintRefusal::UnencodableFaithfulness {
            name: name.to_owned(),
            method: faithful.method(),
        });
    }

    let carrier = CarrierDecision::of_signature(signature);

    Ok(VerdictDigest {
        decl: name.to_owned(),
        kernel_version: local_kernel_version().to_owned(),
        environment,
        assumptions,
        carrier,
        faithfulness: FaithfulnessEvidence {
            method: faithful.method(),
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
                | DigestMintRefusal::EvidenceMismatch { name, .. }
                | DigestMintRefusal::UnencodableFaithfulness { name, .. },
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
///
/// # RECURSIVE verdicts cannot cross a crate boundary (R1 and R2 accounting)
///
/// A `StructuralNatRec` verdict is earned by the PER-EQUATION judgment
/// (`check_faithful_equations`), and [`FaithfulnessEvidence`] has no
/// spelling that distinguishes it from whole-term defeq — a wire-format
/// statement of the per-equation mode is its own reviewed change. Wire
/// format v2 carries the `Nat` (unbounded-exact) carrier honestly, so the
/// v1 width refusal that used to backstop this is gone; the fail-closed
/// arm is now EXPLICIT: [`mint_verdict_digest`] refuses any [`Faithful`]
/// whose method has no wire tag
/// ([`DigestMintRefusal::UnencodableFaithfulness`]), which covers the whole
/// per-equation slice — a recursive def stays crate-local rather than
/// riding the whole-term evidence spelling. (The inductive-projection lane
/// is different on purpose: its evidence IS a whole-term structural-
/// induction verdict, which v2 spells honestly.)
///
/// **R2 (2026-08-22) keeps that boundary, and the reasoning is STRONGER for
/// it — this is a decision, not an omission.** A `WellFoundedNatRec` verdict
/// (`check_faithful_wf_functional`) rests on three things the wire unit
/// cannot state: an F-LAYER comparison rather than a whole-term one; a BORROW
/// of side A's decrease proofs, whose correctness is a property of the
/// exporting environment's declaration; and an AXIOM-CLOSURE AUDIT of both
/// sides, which is the *other half of the termination argument* on this lane
/// (probe c1: one assumed decrease and a diverging functional admits). The
/// digest does carry an axiom closure for the declaration — but a tag saying
/// "well-founded functional defeq" would tell an importer that a judgment
/// happened whose inputs the format has no field for, and the importer's own
/// re-gate is what would then be silently doing all the work. Adding the tag
/// is therefore a REVIEWED format change that must land with the fields, not
/// a one-line enum arm; and the decode side must refuse an unknown tag when
/// it does (the existing versioned-refusal discipline: an unknown tag is a
/// refusal, never a best-effort parse). Until then a cross-crate call to a
/// well-founded Clean def refuses at this seam, fail-closed.
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

/// Sealed evidence that the ACTUAL imported body passed the local gate, bound
/// to the exact local dependency-closure digest used for that check.
///
/// A caller cannot construct this from a wire method tag. The only constructor
/// is [`locally_recheck_imported_body`], which runs [`admit_lowering`] in the
/// exact `Environment` borrowed and sealed by [`ReadmissionPreflight`]. The
/// token copies that precomputed environment digest; it never recomputes or
/// accepts a caller-selected binding.
///
/// ```compile_fail,E0451
/// let forged = trust_clean_origin::LocallyRechecked {
///     faithful: todo!(),
///     environment: todo!(),
/// };
/// ```
#[derive(Debug)]
pub struct LocallyRechecked {
    faithful: Faithful,
    environment: EnvironmentDigest,
}

impl LocallyRechecked {
    /// Declaration whose actual imported body was checked.
    #[must_use]
    pub fn decl(&self) -> &str {
        self.faithful.name()
    }

    /// Locally observed proof method. Diagnostic only until [`readmit`]
    /// matches it to a complete preflight.
    #[must_use]
    pub fn method(&self) -> FaithfulnessMethod {
        self.faithful.method()
    }
}

/// Failure to bind an actual imported body to local gate evidence.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum LocalBodyRecheckRefusal {
    /// The supplied plan belongs to another declaration.
    PlanSubjectSkew {
        /// Declaration established by preflight.
        expected: String,
        /// Declaration named by the plan.
        planned: String,
    },
    /// The supplied plan's carrier signature differs from local preflight.
    PlanCarrierSkew {
        /// Declaration being imported.
        decl: String,
    },
    /// The body did not agree with its locally planned Clean declaration.
    Emit(EmitRefusal),
}

impl LocalBodyRecheckRefusal {
    /// Declaration whose local re-check failed.
    #[must_use]
    pub fn decl(&self) -> &str {
        match self {
            Self::PlanSubjectSkew { expected, .. } => expected,
            Self::PlanCarrierSkew { decl } => decl,
            Self::Emit(refusal) => refusal.name(),
        }
    }

    /// Whether this is emitted-body/compiler drift rather than a capability
    /// boundary in the declaration itself.
    #[must_use]
    pub fn is_compiler_defect(&self) -> bool {
        match self {
            Self::PlanSubjectSkew { .. } | Self::PlanCarrierSkew { .. } => true,
            Self::Emit(refusal) => refusal.is_compiler_defect(),
        }
    }

    /// Operator-facing resolution.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::PlanSubjectSkew { expected, planned } => format!(
                "the local re-check preflight is for `{expected}`, but the supplied \
                 emission plan is for `{planned}`. A plan for one declaration cannot \
                 purchase proof search for another. Please report this compiler \
                 metadata/plan pairing defect."
            ),
            Self::PlanCarrierSkew { decl } => format!(
                "the local emission plan for `{decl}` has a different carrier signature \
                 from the signature already bound by readmission preflight. Proof search \
                 was not started. Please report this compiler planning defect."
            ),
            Self::Emit(refusal) => refusal.note(),
        }
    }
}

/// Run the local gate over one actual decoded MIR body and bind the resulting
/// sealed evidence to the environment in which it was earned.
///
/// # Errors
///
/// [`LocalBodyRecheckRefusal`] if the plan does not match preflight or the body
/// fails the local gate. No token exists on either path.
pub fn locally_recheck_imported_body(
    preflight: &ReadmissionPreflight<'_>,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<LocallyRechecked, LocalBodyRecheckRefusal> {
    if plan.name() != preflight.decl {
        return Err(LocalBodyRecheckRefusal::PlanSubjectSkew {
            expected: preflight.decl.clone(),
            planned: plan.name().to_owned(),
        });
    }
    if plan.signature() != &preflight.signature {
        return Err(LocalBodyRecheckRefusal::PlanCarrierSkew { decl: preflight.decl.clone() });
    }
    let faithful =
        admit_lowering(preflight.env, plan, extracted).map_err(LocalBodyRecheckRefusal::Emit)?;
    Ok(LocallyRechecked { faithful, environment: preflight.environment.clone() })
}

/// Cheap, sealed result of checking every wire/environment/carrier field that
/// does not require proof search over the imported body.
///
/// It is deliberately not authority by itself. [`readmit`] also requires a
/// [`LocallyRechecked`] token and binds the two by declaration, environment,
/// carrier, and proof method.
#[derive(Debug)]
pub struct ReadmissionPreflight<'env> {
    env: &'env Environment,
    decl: String,
    kernel_version: String,
    environment: EnvironmentDigest,
    admitted_at_rust: String,
    result_carrier: Ty,
    signature: CarrierSignature,
    claimed_method: FaithfulnessMethod,
}

impl ReadmissionPreflight<'_> {
    /// Locally recomputed, fully discharged carrier signature. This is exposed
    /// read-only so the compiler can reject encoded Rust ABI skew before
    /// planning or induction; callers still cannot construct a preflight.
    #[must_use]
    pub fn signature(&self) -> &CarrierSignature {
        &self.signature
    }
}

/// Sealed result of the checks that require only wire bytes and the local
/// kernel identity. This phase deliberately precedes loading/re-elaborating an
/// imported Clean environment, so a stale or assumption-bearing row cannot
/// purchase expensive work.
#[derive(Clone, Debug)]
pub struct WirePreflight {
    digest: VerdictDigest,
    local_kernel_version: String,
}

/// Perform the constant/linear wire-only rejection phase.
///
/// # Errors
///
/// Kernel skew or any assumption-bearing CALL certificate is rejected before
/// environment construction or proof search.
pub fn preflight_wire(
    digest: &VerdictDigest,
    local_kernel_version: &str,
) -> Result<WirePreflight, ReadmissionRefusal> {
    let decl = digest.decl.as_str();
    if digest.kernel_version != local_kernel_version {
        return Err(ReadmissionRefusal::KernelVersionSkew {
            decl: decl.to_owned(),
            minted_under: digest.kernel_version.clone(),
            local: local_kernel_version.to_owned(),
        });
    }
    if !digest.assumptions.is_empty() {
        return Err(ReadmissionRefusal::AssumptionBearing {
            decl: decl.to_owned(),
            assumptions: digest.assumptions.iter().map(|a| a.name().to_owned()).collect(),
        });
    }
    Ok(WirePreflight {
        digest: digest.clone(),
        local_kernel_version: local_kernel_version.to_owned(),
    })
}

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
///     method: todo!(),
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Readmitted {
    decl: String,
    kernel_version: String,
    admitted_at_rust: String,
    method: FaithfulnessMethod,
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

    /// How the exporter proved the body faithful, preserved without
    /// relabelling through decode and re-admission.
    #[must_use]
    pub fn method(&self) -> FaithfulnessMethod {
        self.method
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
    /// The faithfulness evidence marker names a carrier type that is not the local
    /// result carrier.
    FaithfulnessSkew {
        /// The declaration.
        decl: String,
        /// What the marker claims the agreement was admitted at.
        claimed: String,
        /// The local result carrier.
        local: String,
    },
    /// The wire records a different proof method from the method the local
    /// compiler re-earned against the imported body.
    FaithfulnessMethodSkew {
        /// The declaration.
        decl: String,
        /// The method named by the imported digest.
        claimed: FaithfulnessMethod,
        /// The method observed by the local re-gate.
        local: FaithfulnessMethod,
    },
    /// The sealed local gate evidence belongs to a different declaration.
    LocalEvidenceSubjectSkew {
        /// Declaration named by the preflighted digest.
        decl: String,
        /// Declaration whose body the local gate actually checked.
        checked: String,
    },
    /// The sealed local gate evidence was earned over a different dependency
    /// closure from the one preflighted for this import.
    LocalEvidenceEnvironmentSkew {
        /// Declaration being imported.
        decl: String,
        /// Environment digest bound into the local gate token.
        checked: String,
        /// Environment digest established by preflight.
        local: String,
    },
    /// The sealed local gate evidence was earned at a different result carrier.
    LocalEvidenceCarrierSkew {
        /// Declaration being imported.
        decl: String,
        /// Carrier at which the local gate ran.
        checked: String,
        /// Carrier established by local signature preflight.
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
            | Self::CarrierSkew { decl, .. }
            | Self::FaithfulnessSkew { decl, .. }
            | Self::FaithfulnessMethodSkew { decl, .. }
            | Self::LocalEvidenceSubjectSkew { decl, .. }
            | Self::LocalEvidenceEnvironmentSkew { decl, .. }
            | Self::LocalEvidenceCarrierSkew { decl, .. } => decl,
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
                 - rebuild the dependency, then let the importer independently re-check \
                   every transported MIR body under this local kernel before `readmit`;\n\
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
            Self::FaithfulnessSkew { decl, claimed, local } => format!(
                "the imported certificate for `{decl}` says the faithfulness agreement \
                 was admitted at `{claimed}`, but the local result carrier is \
                 `{local}`. The kernel verdict is only meaningful AT the carrier it was \
                 admitted at.\n\
                 options:\n\
                 - rebuild the dependency so the gate re-runs at the current carrier;\n\
                 - report it if the carrier positions matched but this marker did not: \
                   that combination means the certificate was assembled from mismatched \
                   evidence, which the mint refuses — so it did not come from the mint."
            ),
            Self::FaithfulnessMethodSkew { decl, claimed, local } => format!(
                "the imported certificate for `{decl}` claims faithfulness method \
                 `{claimed:?}`, but the local compiler re-earned `{local:?}` from the \
                 actual imported body. The wire may describe evidence, but it cannot \
                 choose which proof the local gate observed.\n\
                 options:\n\
                 - rebuild the dependency with this toolchain so the digest records \
                   the proof method the current gate derives;\n\
                 - report it if a fresh rebuild still disagrees: either the metadata \
                   or the imported body changed after certification."
            ),
            Self::LocalEvidenceSubjectSkew { decl, checked } => format!(
                "the imported certificate names `{decl}`, but the sealed local gate \
                 evidence was earned for `{checked}`. Evidence for one declaration \
                 cannot authorize another.\n\
                 options:\n\
                 - re-run the local body gate for `{decl}` and pass that token;\n\
                 - report this if the compiler paired these rows automatically: the \
                   metadata/body registry is internally inconsistent."
            ),
            Self::LocalEvidenceEnvironmentSkew { decl, checked, local } => format!(
                "the sealed local body check for `{decl}` was earned over dependency \
                 closure {checked}, but certificate preflight established {local}. A \
                 proof from one environment cannot be rebound to another.\n\
                 options:\n\
                 - re-run the local body gate after loading the final dependency \
                   environment;\n\
                 - report it if one compiler session produced both values."
            ),
            Self::LocalEvidenceCarrierSkew { decl, checked, local } => format!(
                "the sealed local body check for `{decl}` ran at carrier `{checked}`, \
                 but local signature preflight established `{local}`. The gate's \
                 equality is meaningful only at the carrier it checked.\n\
                 options:\n\
                 - re-plan and re-check the imported body at the current carrier;\n\
                 - report it if the compiler paired these values automatically."
            ),
        }
    }
}

/// Bind a wire preflight to the local environment and carrier map before any
/// local proof search over an imported body.
///
/// The comparisons, in reporting order (coarsest first, the same rationale as
/// `crate::mint::decide_mint` — any failure refuses, so order is not
/// load-bearing for soundness):
///
/// 1. **declaration present** — the local environment must hold the subject.
/// 2. **environment digest** — recomputed over `local_env` by the same
///    [`environment_digest_for`] and compared.
/// 3. **disclosure cross-audit** — the local `axiom_deps` walk must not find
///    assumptions the digest failed to name. Refutation-only; see
///    [`ReadmissionRefusal::UndisclosedAssumptions`].
/// 4. **carrier decision** — recomputed locally from the declaration's type
///    via the local carrier map and compared position by position.
/// 5. **faithfulness carrier marker** — must name the local result carrier.
///    The claimed METHOD is retained for [`readmit`] to compare with sealed
///    locally re-earned evidence; it is never accepted as an input fact.
///
/// # Errors
///
/// [`ReadmissionRefusal`] naming the first mismatch. Success is only a sealed
/// [`ReadmissionPreflight`], not a [`Readmitted`] authority.
pub fn bind_readmission<'env>(
    wire: &WirePreflight,
    local_env: &'env Environment,
) -> Result<ReadmissionPreflight<'env>, ReadmissionRefusal> {
    let digest = &wire.digest;
    let decl = digest.decl.as_str();

    // ── 1+2. the local content must hash to what the verdict was over ──────
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

    // ── 3. refute an empty-closure claim if the local DAG names assumptions ─
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

    // ── 4. the LOCAL carrier decision, recomputed, position by position ────
    let Some(info) = local_env.get_const(&kernel_name) else {
        return Err(ReadmissionRefusal::DeclarationMissing { decl: decl.to_owned() });
    };
    let local_signature = carrier_signature_for(&info.type_).map_err(|refusal| {
        ReadmissionRefusal::LocalCarrierRefused { decl: decl.to_owned(), refusal }
    })?;
    let local_decision = CarrierDecision::of_signature(&local_signature);

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

    // ── 5. the faithfulness marker must name the local result carrier ──────
    if digest.faithfulness.admitted_at_rust != local_decision.result.rust_carrier {
        return Err(ReadmissionRefusal::FaithfulnessSkew {
            decl: decl.to_owned(),
            claimed: digest.faithfulness.admitted_at_rust.clone(),
            local: local_decision.result.rust_carrier.clone(),
        });
    }
    Ok(ReadmissionPreflight {
        env: local_env,
        decl: decl.to_owned(),
        kernel_version: wire.local_kernel_version.clone(),
        environment: local_digest,
        admitted_at_rust: local_decision.result.rust_carrier.clone(),
        result_carrier: local_signature.result().rust().clone(),
        signature: local_signature,
        claimed_method: digest.faithfulness.method,
    })
}

/// Finalize a cheap preflight with sealed evidence earned from the actual
/// imported body.
///
/// Neither input alone is authority: preflight validates the wire and local
/// environment but performs no proof search; [`LocallyRechecked`] proves a
/// body but does not say which wire row requested it. This function binds them
/// by subject, dependency closure, carrier, and proof method.
///
/// A caller-supplied method is deliberately not part of this API:
///
/// ```compile_fail,E0061
/// # use trust_clean_origin::{FaithfulnessMethod, LocallyRechecked, ReadmissionPreflight};
/// fn cannot_echo_wire_method(
///     preflight: &ReadmissionPreflight<'_>,
///     local: &LocallyRechecked,
/// ) {
///     let _ = trust_clean_origin::readmit(
///         preflight,
///         local,
///         FaithfulnessMethod::StructuralInduction,
///     );
/// }
/// ```
///
/// # Errors
///
/// [`ReadmissionRefusal`] on any mismatch. There is no warning/partial mode.
pub fn readmit(
    preflight: &ReadmissionPreflight<'_>,
    local: &LocallyRechecked,
) -> Result<Readmitted, ReadmissionRefusal> {
    if local.faithful.name() != preflight.decl {
        return Err(ReadmissionRefusal::LocalEvidenceSubjectSkew {
            decl: preflight.decl.clone(),
            checked: local.faithful.name().to_owned(),
        });
    }
    if local.environment != preflight.environment {
        return Err(ReadmissionRefusal::LocalEvidenceEnvironmentSkew {
            decl: preflight.decl.clone(),
            checked: local.environment.hex.clone(),
            local: preflight.environment.hex.clone(),
        });
    }
    if local.faithful.admitted_at() != &preflight.result_carrier {
        return Err(ReadmissionRefusal::LocalEvidenceCarrierSkew {
            decl: preflight.decl.clone(),
            checked: format!("{:?}", local.faithful.admitted_at()),
            local: format!("{:?}", preflight.result_carrier),
        });
    }
    if local.faithful.method() != preflight.claimed_method {
        return Err(ReadmissionRefusal::FaithfulnessMethodSkew {
            decl: preflight.decl.clone(),
            claimed: preflight.claimed_method,
            local: local.faithful.method(),
        });
    }

    Ok(Readmitted {
        decl: preflight.decl.clone(),
        kernel_version: preflight.kernel_version.clone(),
        admitted_at_rust: preflight.admitted_at_rust.clone(),
        method: local.faithful.method(),
    })
}

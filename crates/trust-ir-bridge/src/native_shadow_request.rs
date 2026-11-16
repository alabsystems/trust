//! Direct-lane SHADOW verification bundle planning (Step 4 of
//! `docs/design/DIRECT-LANE-PROOF-AUTHORITY.md`) — the SIBLING of
//! [`crate::native_request`], never a loosening of it.
//!
//! The MIR-compatibility planner's two pinned refusals stand byte-untouched
//! next door: `EmptyObligations` and `NonMirCompatibilityProducer` still
//! refuse every direct module at that entry, and this module hardcodes the
//! OTHER wire pair — [`NativeBundleProducer::TRust`] +
//! [`NativeAdapterInput::TrustIrModule`] — with no parameter that can vary
//! either, so anti-relabelling is by construction on this side exactly as the
//! MIR entry hardcodes `TrustIr`/`RustMir`. Both producer and input tags are
//! domain-separated into every bundle digest (`request/digest.rs` writes the
//! producer tag and the input tag + optional digest into
//! `NativeVerificationBundle::stable_digest`), so a shadow bundle can never
//! collide with a MIR-compatibility bundle at the digest layer even over
//! identical module bytes.
//!
//! WHAT A SHADOW BUNDLE IS. Differential material, never authority:
//!
//! * every planned obligation is `Pending` and STAYS `Pending` — a planner
//!   that finds anything else refuses; solving a shadow request produces
//!   evidence rows elsewhere, never a verdict write-back into the module;
//! * `emits_native_verification_requests()` in the direct producer stays
//!   FALSE and ungated — no compiler call site invokes this entry; invoking
//!   it IS the explicit caller decision (a test harness or a differential
//!   lane), and there is no flag that turns it on in production;
//! * `grants_proof_authority()` is untouched and false.
//!
//! SOURCE BINDING — the decision, made explicitly. With input
//! [`NativeAdapterInput::TrustIrModule`], `bundle.source_digest()` is
//! structurally `None` (the input variant IS the digest carrier), and this
//! planner does NOT counterfeit an anchor:
//!
//! 1. it never runs trust-mir-extract to mint a `rust-mir.v1` digest — that
//!    upstream is exactly what milestone M1 removes;
//! 2. it never puts anything in the `RustMir` slot — that is the
//!    impersonation the anti-relabelling gates exist to stop;
//! 3. `provenance.source_digest` stays `None` — with input `TrustIrModule`
//!    the `InputDigestMismatch` cross-check cannot fire, so a stamped
//!    `Some(any non-zero SHA-256)` would VALIDATE while binding NOTHING;
//!    leaving it `None` is the honest spelling and is pinned by test.
//!
//! What the lineage DOES attest is a real, recomputable fact: one
//! [`ProofTransformStage::Frontend`] node (sole root) whose `source_module`
//! is the stable digest of the module AS RECEIVED (the emitted direct
//! artifact, pre enrichment) and whose `target_module` is the enriched
//! module the bundle carries. Because the in-process typestate below
//! evaporates at serialization, the same disclosure also rides the WIRE:
//! [`DIRECT_SHADOW_WIRE_DISCLOSURE`] is stamped into the lineage node's
//! replay invocation and every request's replay invocation, both of which
//! are digest-framed and serialized, so a deserialized shadow bundle still
//! names itself unanchored in-band.
//!
//! FAIL CLOSED ON THE LINEAGE GAP. The checks that DO NOT APPLY because the
//! source digest is absent are enumerated as stable strings in
//! [`DIRECT_SHADOW_NON_APPLYING_CHECKS`] and carried on every
//! [`DirectShadowLineageDisclosure`]. The inner bundle is private: the ONLY
//! way to take it by value is [`DirectShadowBundle::
//! acknowledge_unanchored_lineage`], so no in-process consumer can obtain the
//! bundle without the disclosure having been in its hands. For consumers of
//! the SERIALIZED form, the durable identity is the digest-bound
//! producer/input tag pair plus the disclosure strings above — refuse on
//! those, not on the absent wrapper.
//!
//! HARNESS CONFINEMENT. Nothing here mints or touches
//! `SourceGenerationAuthority` (`mint_from_live_lowering`); a shadow bundle
//! must only ever enter a verifier's DIAGNOSTIC path. A harness that routes a
//! shadow bundle into a proof-grade admission path is out of contract even
//! though the labels would be honest — the refusal belongs at that seam, and
//! this planner deliberately gives it the in-band strings to refuse on.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use thiserror::Error;
use trust_ir::binary::BinaryProjectionError;
use trust_ir::{
    FuncId, Module, NativeAdapterInput, NativeBundleProducer, NativeCompilerFacts,
    NativeDiagnosticsPolicy, NativeMonomorphizationId, NativeRequestId, NativeRequestProvenance,
    NativeSourceLanguage, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, ObligationKind,
    PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, Producer, ProofDigest, ProofDigestAlgorithm,
    ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligationSourceRange,
    ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
    PublicObligationIdentity, TrustMcNativeRequest, TrustMcVerificationMode,
};
use trust_types::fx::FxHashMap;

use crate::native_request::{
    NativeVerificationBundleBuildError, native_monomorphization_fact, native_replay_context,
    native_wp_request, obligation_sources_for_owners, require_native_module_binary_identity,
    trust_mc_chc_request_options,
};

#[cfg(test)]
#[path = "native_shadow_metadata_tests.rs"]
mod metadata_tests;

/// Transform/contract version for the direct-lane SHADOW planner.
pub const TRUST_DIRECT_SHADOW_TRANSFORM_VERSION: &str = "direct-shadow-request-v1";

/// The one source vocabulary the shadow planner admits (mirrors
/// `trust-thir-lower/src/direct_obligations.rs::DIRECT_ASSERT_SOURCE_ID`,
/// spelled here as a literal so this crate stays free of a rustc_private
/// dependency edge; the round-trip against the real installer is pinned at
/// the driver level, where trust-thir-lower is buildable).
pub const DIRECT_SHADOW_ADMITTED_SOURCE_ID: &str = "trust-thir-lower/direct-assert@1";

/// Prefix of every shadow-minted public obligation id. The remainder is the
/// row's `assertion_id`, percent-encoded (the direct identity grammar
/// contains `#`, which `trust_ir::proof::is_canonical_public_obligation_id`
/// rejects; the encoded form satisfies both that check and
/// trust-verifier-api's `canonical_artifact_owner_id`).
pub const DIRECT_SHADOW_PUBLIC_ID_PREFIX: &str = "direct:";

/// The in-band, wire-durable statement of what a shadow bundle's lineage does
/// NOT bind. Stamped into the lineage node's replay invocation and into every
/// request's replay invocation — both digest-framed and serialized — because
/// the [`DirectShadowBundle`] typestate is in-process only and a deserialized
/// bundle sheds it entirely.
pub const DIRECT_SHADOW_WIRE_DISCLOSURE: &str = "SHADOW LANE (lineage-unanchored): input TrustIrModule carries no compiler-source digest, \
     so bundle.source_digest() is None and every source-digest-keyed lineage check does not \
     apply; verdicts over this bundle are differential evidence only, never proof authority";

/// The source-digest-keyed checks that DO NOT APPLY to a shadow bundle,
/// spelled as stable strings so a consumer can display or refuse on them.
/// One entry per check found in the lineage audit; silence is the failure
/// mode this list exists to prevent.
pub const DIRECT_SHADOW_NON_APPLYING_CHECKS: &[&str] = &[
    "trust-ir bundle.validate: input.rust_mir.body_digest zero-digest check \
     (vacuous — the input is TrustIrModule; no RustMir body digest exists)",
    "trust-ir bundle.validate: input.source_digest algorithm check \
     (vacuous — bundle.source_digest() is None)",
    "trust-ir bundle.validate_provenance: InputDigestMismatch cross-check \
     (cannot fire — it compares provenance.source_digest against an input digest that is absent)",
    "trust-ir bundle.validate_lineage_digests: SourceDigestNotInLineage \
     (no source digest exists to demand in the lineage)",
    "trust-ir bundle.validate_requests: RequestSourceDigestNotInLineage \
     (no source digest exists to demand per request)",
    "trust-ir request/digest.rs source_bound_lineage_membership \
     (a None source digest admits every root closure; membership is unbound)",
    "trust-mc evidence binding: per-evidence source-digest validation and the \
     \"native.source\" binding-hash component (both apply only when a source digest is Some)",
];

/// Why a derived owner is not eligible to own direct-lane obligation rows.
///
/// Owners are derived FROM the obligation rows, which makes the reused
/// planner's `ObligationFunctionMismatch` a tautology on this lane — any row
/// naming `Some(f)` automatically makes `f` an owner. This check is the
/// compensating control: an owner must be a real, bodied, direct-produced
/// function, or the row is refused rather than planned into a Chc request
/// that dies later inside trust-mc as a mislabeled missing-function failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectOwnerIneligibility {
    /// The row names a `FuncId` the module does not declare.
    NotInModule,
    /// The row names a bodyless declaration (`Function::is_declaration`) —
    /// the fail-closed extern stubs the direct finalizer mints have no body
    /// to translate, so no Chc request about them can be honest.
    Bodyless,
    /// The row names a function whose producer is not `Producer::TRust`.
    /// `Producer::Clean` join rows are admitted as translation CONTEXT but
    /// are claim-free by the 2026-08-27 design and may not own rows here.
    NonDirectProducer(Option<Producer>),
}

impl core::fmt::Display for DirectOwnerIneligibility {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotInModule => f.write_str("the function is missing from the module"),
            Self::Bodyless => f.write_str("the function is a bodyless declaration"),
            Self::NonDirectProducer(producer) => {
                write!(f, "the function's producer is {producer:?}, expected Producer::TRust")
            }
        }
    }
}

/// Builder errors for the direct-lane shadow planner. Every refusal names the
/// fix (v7/D3): "unsupported" with no next step is a defect.
#[derive(Debug, Clone, PartialEq, Error)]
pub enum DirectShadowBundleBuildError {
    #[error("direct shadow module has no binary identity: {0}")]
    ModuleBinaryIdentity(BinaryProjectionError),
    #[error("cannot plan a direct shadow bundle for an empty TrustIr module")]
    EmptyModule,
    #[error(
        "cannot plan a direct shadow bundle: function {function} has producer {producer:?}; \
         this entry admits only the direct lane's Producer::TRust bodies (plus claim-free \
         Producer::Clean join rows as context) — a MIR-compatibility module belongs to \
         native_verification_bundle_from_module, not to this sibling"
    )]
    NonDirectProducer { function: FuncId, producer: Option<Producer> },
    #[error(
        "cannot plan a direct shadow bundle without direct obligation rows; the direct finalizer \
         births them at tier obligation-bearing-pending-v2 — lower a body that mints an \
         arithmetic-safety assert, or check DIRECT_OBLIGATION_CAPABILITY"
    )]
    NoDirectObligations,
    #[error(
        "cannot plan a direct shadow bundle over a module carrying {certificates} proof \
         certificate(s); the direct tier is claim-free and a certificate here could ride the \
         kernel-import re-route into self-minted evidence — strip the certificates or use the \
         authority-bearing MIR lane they came from"
    )]
    CertificateBearingModule { certificates: usize },
    #[error(
        "direct shadow obligation {0} has no embedded source identity; every direct row is \
         minted with one by install_direct_obligations — this module did not come from the \
         direct finalizer"
    )]
    MissingObligationSource(ProofId),
    #[error(
        "direct shadow obligation {obligation} carries foreign source_id {source_id:?}; this \
         entry admits only {DIRECT_SHADOW_ADMITTED_SOURCE_ID:?} — route other vocabularies \
         through their own planners"
    )]
    ForeignObligationSourceId { obligation: ProofId, source_id: String },
    #[error(
        "direct shadow obligation {0} already carries a public obligation identity; the shadow \
         planner mints the public pair itself at request-build time, so a pre-enriched row is \
         either a replay of this planner's own output or a MIR-lane row wearing the wrong \
         source_id — hand this module's rows over public-identity-free"
    )]
    PreEnrichedPublicIdentity(ProofId),
    #[error(
        "direct shadow obligation {obligation} has status {status}; only Pending claims may be \
         planned — a {status} row is a verdict, and verdicts never enter the shadow lane \
         (re-earn it downstream as differential evidence instead)"
    )]
    NonPendingObligation { obligation: ProofId, status: ProofStatus },
    #[error(
        "direct shadow obligation {obligation} has kind {kind:?}; the direct lane mints \
         ArithmeticSafety and BoundsCheck only — extend the admitted vocabulary in a reviewed \
         change, not by feeding this planner foreign kinds"
    )]
    NonDirectObligationKind { obligation: ProofId, kind: ObligationKind },
    #[error(
        "direct shadow obligation {0} carries a formula; direct rows are formula-free below \
         Step 6 — a formula here would smuggle a proposition past the tier gate"
    )]
    FormulaBearingObligation(ProofId),
    #[error(
        "direct shadow obligation {0} has no owning-function scope; per-function request \
         slicing derives owners FROM the rows, so an unscoped row cannot be planned — bind \
         .with_function at the mint"
    )]
    UnscopedObligation(ProofId),
    #[error(
        "direct shadow obligation {0} has no ObligationSite; direct rows bind their site at \
         emission — a site-less row did not come from the direct installer"
    )]
    MissingObligationSite(ProofId),
    #[error(
        "direct shadow obligation {obligation} is owned by function {function}, which is not \
         direct-eligible: {reason}; owners must be bodied Producer::TRust functions of this \
         module — fix the row's .with_function binding or lower the owner's body"
    )]
    OwnerNotDirectEligible {
        obligation: ProofId,
        function: FuncId,
        reason: DirectOwnerIneligibility,
    },
    #[error(
        "direct shadow obligation {obligation} has a source range naming file index {file}, \
         but the module interns only {files} file(s); re-intern the file at the mint rather \
         than shipping a dangling index"
    )]
    MalformedObligationRange { obligation: ProofId, file: u32, files: usize },
    #[error(
        "direct shadow obligation {obligation}: the canonical trust-verifier-api semantic \
         digest refused the projection ({detail}); fix the row's description/source so the \
         ratified pre-transport schema accepts it — this planner never substitutes a \
         non-canonical digest"
    )]
    SemanticDigestRejected { obligation: ProofId, detail: String },
    #[error(
        "direct shadow public obligation id {public_obligation_id:?} collides between rows \
         {first} and {second} after the byte-cap clamp; shorten the assertion-id head (crate/\
         def-path) or raise the identity's distinguishing suffix — the planner refuses rather \
         than aliasing two obligations under one public id"
    )]
    PublicObligationIdCollision { public_obligation_id: String, first: ProofId, second: ProofId },
    #[error(
        "direct shadow planning found {obligations} obligation row(s) but none carries a \
         ProofObligationSourceRange, so none is requestable (requested rows must carry \
         span + assertion); re-lower with real spans or accept that this module has nothing \
         to shadow-verify"
    )]
    NoRequestableObligations { obligations: usize },
    #[error(
        "direct shadow planning failed inside the reused MIR-planner helpers: {0}; this is \
         unreachable-by-construction after the sibling's own pre-checks and indicates a defect \
         in this planner, not in the module"
    )]
    Planner(NativeVerificationBundleBuildError),
    #[error("direct shadow bundle validation failed")]
    Validation(Vec<NativeVerificationBundleError>),
}

/// A validated shadow bundle plus the typed statement of what its lineage
/// does NOT bind.
///
/// The inner [`NativeVerificationBundle`] is private: the only way to obtain
/// it BY VALUE is [`Self::acknowledge_unanchored_lineage`], so no in-process
/// consumer can take the bundle without the disclosure having been in its
/// hands. This typestate does not cross serialization — the wire-durable
/// identity is the digest-bound `TRust`/`TrustIrModule` tag pair plus
/// [`DIRECT_SHADOW_WIRE_DISCLOSURE`] inside the bundle itself.
#[derive(Debug, Clone, PartialEq)]
pub struct DirectShadowBundle {
    bundle: NativeVerificationBundle,
    pub disclosure: DirectShadowLineageDisclosure,
}

impl DirectShadowBundle {
    /// Inspect the bundle without consuming the disclosure.
    pub fn bundle(&self) -> &NativeVerificationBundle {
        &self.bundle
    }

    /// Take the bundle by value, acknowledging that its lineage is
    /// unanchored: no compiler-source digest is bound, and every check in
    /// [`DIRECT_SHADOW_NON_APPLYING_CHECKS`] silently does not apply. The
    /// caller owns routing the bundle to a DIAGNOSTIC path only.
    pub fn acknowledge_unanchored_lineage(self) -> NativeVerificationBundle {
        self.bundle
    }
}

/// What a shadow bundle's lineage attests, what it does not, and the counts a
/// differential consumer needs to reconcile the plan against the module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectShadowLineageDisclosure {
    /// `stable_digest()` of the module AS RECEIVED (pre public-identity
    /// enrichment) — the lineage node's `source_module` attests exactly this
    /// value, and it is recomputable from the emitted direct artifact.
    pub pristine_module_digest: ProofDigest,
    /// `stable_digest()` of the enriched module the bundle carries
    /// (== `bundle.trust_ir_module_digest`).
    pub enriched_module_digest: ProofDigest,
    /// Rows planned into requests (one TrustMc Chc request per row).
    pub obligations_planned: usize,
    /// Rows with no `ProofObligationSourceRange`: their sidecar span is
    /// `None`, therefore they are NOT requestable — counted, never silently
    /// dropped.
    pub obligations_unrequestable_missing_range: usize,
    /// The source-digest-keyed checks that DO NOT APPLY to this bundle.
    pub non_applying_checks: &'static [&'static str],
}

/// Build the direct THIR lane's typed SHADOW verification bundle from one
/// crate-level `Producer::TRust` module.
///
/// Producer is [`NativeBundleProducer::TRust`], input is
/// [`NativeAdapterInput::TrustIrModule`] — hardcoded; no parameter can vary
/// them. Scope: NO physical slicing — one crate-level bundle, per-function
/// scoping through the existing multi-owner sidecar mechanism with owners
/// DERIVED from the obligation rows themselves (ascending `FuncId`), each
/// checked bodied + `Producer::TRust`. Requests mirror the MIR planner's
/// shape: owner-major, one `TrustMc` Chc request per obligation, so the
/// trust-ir validator re-checks scope per request for free
/// (`RequestObligationFunctionMismatch`).
///
/// The public identity pair the validator demands per row is minted HERE, at
/// request-build time, into this planner's owned copy of the module — never
/// in trust-thir-lower, never in the emitted artifact: `public_obligation_id
/// = "direct:" + percent-encoded assertion_id` and `semantic_digest =` the
/// canonical trust-verifier-api `TrustObligation::
/// canonical_semantic_digest_sha256` over the minimal projection (public id,
/// `ArithmeticSafety`, the row's range rendered through `module.files`
/// or the pinned all-`None` `SourceLocation` for rangeless rows, the row's
/// description; no contract/proof-item ids, no summary facts, no metadata).
///
/// Returns a wrapper, never a bare bundle — see [`DirectShadowBundle`].
pub fn direct_shadow_verification_bundle_from_module(
    module: Module,
) -> Result<DirectShadowBundle, DirectShadowBundleBuildError> {
    direct_shadow_bundle_with_contract_claims(module, &BTreeMap::new())
}

/// Prepared by the query-bound contract entry, never by a source decoder.
pub(super) struct DirectShadowContractClaim {
    pub public: PublicObligationIdentity,
    pub formula: trust_ir::ProofFormula,
    pub range: ProofObligationSourceRange,
}

pub(super) fn direct_shadow_bundle_with_contract_claims(
    module: Module,
    contracts: &BTreeMap<ProofId, DirectShadowContractClaim>,
) -> Result<DirectShadowBundle, DirectShadowBundleBuildError> {
    let mut module = module;
    if module.functions.is_empty() {
        return Err(DirectShadowBundleBuildError::EmptyModule);
    }
    // The anti-relabelling mirror (positive provenance FIRST, before any
    // row-shape check, so a MIR-compatibility module gets the producer error
    // and not an incidental row-shape one): every function must be the direct
    // lane's own `TRust` or a claim-free `Clean` join row. Missing provenance
    // fails closed — this planner cannot infer that an unlabelled function
    // came from the direct path.
    let mut source_languages = BTreeSet::from([NativeSourceLanguage::TrustIr]);
    for function in &module.functions {
        match function.producer.as_ref() {
            Some(Producer::TRust) => {
                source_languages.insert(NativeSourceLanguage::Rust);
            }
            Some(Producer::Clean) => {
                source_languages.insert(NativeSourceLanguage::Clean);
            }
            other => {
                return Err(DirectShadowBundleBuildError::NonDirectProducer {
                    function: function.id,
                    producer: other.cloned(),
                });
            }
        }
    }
    if module.proof_obligations.is_empty() {
        return Err(DirectShadowBundleBuildError::NoDirectObligations);
    }
    require_native_module_binary_identity(&module)
        .map_err(DirectShadowBundleBuildError::ModuleBinaryIdentity)?;
    if !module.proof_certificates.is_empty() {
        return Err(DirectShadowBundleBuildError::CertificateBearingModule {
            certificates: module.proof_certificates.len(),
        });
    }

    let pristine_module_digest = module.stable_digest();

    // Row conformance + owner derivation, fail-closed per row. `owner_state`
    // caches the per-function eligibility verdict so each owner is judged
    // once.
    let mut owner_state: FxHashMap<FuncId, Result<(), DirectOwnerIneligibility>> =
        FxHashMap::default();
    let mut owners: BTreeSet<FuncId> = BTreeSet::new();
    for obligation in &module.proof_obligations {
        let source = obligation
            .source
            .as_ref()
            .ok_or(DirectShadowBundleBuildError::MissingObligationSource(obligation.id))?;
        let contract = contracts.contains_key(&obligation.id);
        if source.source_id != DIRECT_SHADOW_ADMITTED_SOURCE_ID
            && !(contract && source.source_id == "trust-thir-lower/contract@1")
        {
            return Err(DirectShadowBundleBuildError::ForeignObligationSourceId {
                obligation: obligation.id,
                source_id: source.source_id.clone(),
            });
        }
        if source.public.is_some() {
            return Err(DirectShadowBundleBuildError::PreEnrichedPublicIdentity(obligation.id));
        }
        if obligation.status != ProofStatus::Pending {
            return Err(DirectShadowBundleBuildError::NonPendingObligation {
                obligation: obligation.id,
                status: obligation.status,
            });
        }
        // Trust (Step 5, docs/design/DIRECT-LANE-PROOF-AUTHORITY.md): the
        // admitted kind set is EXACTLY the direct installer's mint range —
        // {ArithmeticSafety, BoundsCheck} — widened from the single kind in
        // the same reviewed change that taught the installer to mint bounds
        // rows. Both sides of the S6-closure property (allowlist == mint
        // range) move together; nothing wider.
        if !matches!(
            obligation.kind,
            ObligationKind::ArithmeticSafety | ObligationKind::BoundsCheck
        ) && !(contract && obligation.kind == ObligationKind::Postcondition)
        {
            return Err(DirectShadowBundleBuildError::NonDirectObligationKind {
                obligation: obligation.id,
                kind: obligation.kind.clone(),
            });
        }
        if obligation.formula.is_some() && !contract {
            return Err(DirectShadowBundleBuildError::FormulaBearingObligation(obligation.id));
        }
        if obligation.site.is_none() && !contract {
            return Err(DirectShadowBundleBuildError::MissingObligationSite(obligation.id));
        }
        let function = obligation
            .function
            .ok_or(DirectShadowBundleBuildError::UnscopedObligation(obligation.id))?;
        let eligibility = owner_state
            .entry(function)
            .or_insert_with(|| direct_owner_eligibility(&module, function));
        if let Err(reason) = eligibility {
            return Err(DirectShadowBundleBuildError::OwnerNotDirectEligible {
                obligation: obligation.id,
                function,
                reason: reason.clone(),
            });
        }
        owners.insert(function);
    }

    // Enrichment: mint the public identity pair per row (EVERY row, ranged or
    // not — the sidecar public id is per-row, not per-requested-row) into this
    // planner's owned copy. Computed immutably first so `module.files` can be
    // read while the rows are still borrowed.
    let mut minted: Vec<PublicObligationIdentity> =
        Vec::with_capacity(module.proof_obligations.len());
    let mut public_ids: FxHashMap<String, ProofId> =
        FxHashMap::with_capacity_and_hasher(module.proof_obligations.len(), Default::default());
    for obligation in &module.proof_obligations {
        let source = obligation
            .source
            .as_ref()
            .ok_or(DirectShadowBundleBuildError::MissingObligationSource(obligation.id))?;
        if let Some(contract) = contracts.get(&obligation.id) {
            minted.push(contract.public.clone());
            continue;
        }
        let public_obligation_id = shadow_public_obligation_id(&source.assertion_id);
        debug_assert!(
            trust_ir::proof::is_canonical_public_obligation_id(&public_obligation_id),
            "the percent-encoding must yield a canonical public id: {public_obligation_id:?}"
        );
        if let Some(first) = public_ids.insert(public_obligation_id.clone(), obligation.id) {
            return Err(DirectShadowBundleBuildError::PublicObligationIdCollision {
                public_obligation_id,
                first,
                second: obligation.id,
            });
        }
        let semantic_digest = shadow_semantic_digest(
            &module,
            obligation.id,
            &obligation.kind,
            &public_obligation_id,
            &obligation.description,
            source.range.as_ref(),
        )?;
        minted.push(PublicObligationIdentity {
            obligation_id: public_obligation_id,
            semantic_digest,
        });
    }
    for (obligation, public) in module.proof_obligations.iter_mut().zip(minted) {
        let source = obligation
            .source
            .as_mut()
            .ok_or(DirectShadowBundleBuildError::MissingObligationSource(obligation.id))?;
        source.public = Some(public);
        if let Some(contract) = contracts.get(&obligation.id) {
            obligation.formula = Some(contract.formula.clone());
            source.range = Some(contract.range);
        }
    }

    let enriched_module_digest = module.stable_digest();
    debug_assert_ne!(
        pristine_module_digest, enriched_module_digest,
        "enrichment adds public identities, so the digests must differ"
    );

    // Compiler facts through the EXISTING multi-owner mechanism. Owners are
    // the ascending-FuncId set derived above; the sibling's pre-checks make
    // MissingObligationSource / MissingPublicObligationIdentity /
    // ObligationFunctionMismatch unreachable here (debug-asserted; the typed
    // wrapper stays the release-mode behavior — deliberately NOT a
    // debug_assert band-aid, because the error path still fails closed).
    let owners: Vec<FuncId> = owners.into_iter().collect();
    let owner_indices: BTreeMap<FuncId, usize> =
        owners.iter().enumerate().map(|(index, function)| (*function, index)).collect();
    let Some(&root) = owners.first() else {
        return Err(DirectShadowBundleBuildError::EmptyModule);
    };
    let mut compiler_facts = NativeCompilerFacts::default();
    compiler_facts.monomorphizations = owners
        .iter()
        .enumerate()
        .map(|(index, function)| {
            native_monomorphization_fact(
                &module,
                *function,
                NativeMonomorphizationId::new(index as u32),
                enriched_module_digest,
            )
        })
        .collect();
    compiler_facts.obligation_sources =
        obligation_sources_for_owners(&module, &owner_indices, root).map_err(|error| {
            debug_assert!(false, "unreachable after the sibling's own row pre-checks: {error:?}");
            DirectShadowBundleBuildError::Planner(error)
        })?;

    // Requestable partition: only rows with a real source range may be
    // requested (a requested row must carry span + assertion downstream);
    // rangeless rows keep their sidecar entry and ride the disclosure count.
    let mut requestable_by_owner: BTreeMap<FuncId, Vec<ProofId>> = BTreeMap::new();
    let mut obligations_unrequestable_missing_range = 0usize;
    for obligation in &module.proof_obligations {
        let source = obligation
            .source
            .as_ref()
            .ok_or(DirectShadowBundleBuildError::MissingObligationSource(obligation.id))?;
        if source.range.is_some() {
            requestable_by_owner
                .entry(
                    obligation
                        .function
                        .ok_or(DirectShadowBundleBuildError::UnscopedObligation(obligation.id))?,
                )
                .or_default()
                .push(obligation.id);
        } else {
            obligations_unrequestable_missing_range += 1;
        }
    }
    let obligations_planned: usize = requestable_by_owner.values().map(Vec::len).sum();
    if obligations_planned == 0 {
        return Err(DirectShadowBundleBuildError::NoRequestableObligations {
            obligations: module.proof_obligations.len(),
        });
    }

    let lineage = direct_shadow_lineage(
        pristine_module_digest,
        enriched_module_digest,
        module.proof_obligations.iter().map(|obligation| obligation.id).collect(),
    );
    let lineage_root = DIRECT_SHADOW_LINEAGE_ROOT;

    // Owner-major, one TrustMc Chc request per obligation — the MIR planner's
    // shape, so the trust-ir validator re-checks per-request function
    // equality and lineage membership at request granularity for free.
    let mut requests = Vec::with_capacity(obligations_planned);
    let mut next_request_id = 0u32;
    for (owner, owned) in &requestable_by_owner {
        for obligation in owned {
            let request_obligations = vec![*obligation];
            let provenance = direct_shadow_trust_mc_request_provenance(
                &module,
                &compiler_facts,
                pristine_module_digest,
                enriched_module_digest,
                &request_obligations,
            );
            requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
                id: NativeRequestId::new(next_request_id),
                mode: TrustMcVerificationMode::Chc,
                function: *owner,
                obligations: request_obligations,
                lineage_roots: vec![lineage_root],
                options: trust_mc_chc_request_options(),
                diagnostics: NativeDiagnosticsPolicy::default(),
                provenance,
            }));
            next_request_id += 1;
        }
    }

    // The staged contract entry appends alternatives after the same primary
    // inventory. Request construction is shared with the compatibility path.
    for (owner, owned) in &requestable_by_owner {
        for obligation in owned.iter().filter(|id| contracts.contains_key(id)) {
            let replay = ProofReplayIdentity::new(
                "trust_wp",
                format!("replay_trust_ir_body_contracts; {DIRECT_SHADOW_WIRE_DISCLOSURE}"),
            )
            .with_transcript_digest(shadow_replay_transcript_digest(
                "trust_wp-direct-contract-shadow",
                pristine_module_digest,
                enriched_module_digest,
                &[*obligation],
            ));
            requests.push(native_wp_request(
                NativeRequestId::new(next_request_id),
                *owner,
                *obligation,
                lineage_root,
                replay,
            ));
            next_request_id += 1;
        }
    }

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::TrustIrModule,
        enriched_module_digest,
        module,
        lineage,
    );
    bundle.provenance.producer_version = env!("CARGO_PKG_VERSION").to_string();
    // The primary artifact is TrustIr; the set covers only actual admitted
    // function tags, not a compiler-source binding. Imports may not widen the
    // admitted language set: upstream validation refuses uncovered producers.
    bundle.provenance.source_language = NativeSourceLanguage::TrustIr;
    bundle.provenance.source_languages = source_languages;
    // Pinned decision: stays None. A stamped Some(non-zero SHA-256) would
    // VALIDATE (the InputDigestMismatch cross-check needs an input digest to
    // fire) while binding nothing — the dishonest spelling.
    bundle.provenance.source_digest = None;
    bundle.provenance.toolchain = vec![direct_shadow_tool_identity()];
    bundle.compiler_facts = compiler_facts;
    bundle.requests = requests;
    bundle.validate().map_err(DirectShadowBundleBuildError::Validation)?;
    debug_assert!(
        bundle.source_digest().is_none(),
        "a TrustIrModule-input bundle has no source digest by construction"
    );

    Ok(DirectShadowBundle {
        bundle,
        disclosure: DirectShadowLineageDisclosure {
            pristine_module_digest,
            enriched_module_digest,
            obligations_planned,
            obligations_unrequestable_missing_range,
            non_applying_checks: DIRECT_SHADOW_NON_APPLYING_CHECKS,
        },
    })
}

fn direct_owner_eligibility(
    module: &Module,
    function: FuncId,
) -> Result<(), DirectOwnerIneligibility> {
    let Some(function) = module
        .functions
        .get(function.index() as usize)
        .filter(|candidate| candidate.id == function)
        .or_else(|| module.function_by_id(function))
    else {
        return Err(DirectOwnerIneligibility::NotInModule);
    };
    if function.producer.as_ref() != Some(&Producer::TRust) {
        return Err(DirectOwnerIneligibility::NonDirectProducer(function.producer.clone()));
    }
    if function.is_declaration() {
        return Err(DirectOwnerIneligibility::Bodyless);
    }
    Ok(())
}

fn direct_shadow_tool_identity() -> NativeToolIdentity {
    NativeToolIdentity::new("trust-thir-lower-direct-shadow")
        .with_version(env!("CARGO_PKG_VERSION"))
        .with_revision(TRUST_DIRECT_SHADOW_TRANSFORM_VERSION)
}

/// `"direct:" + percent-encoded assertion_id`, re-clamped
/// head-preserving-suffix to the format's byte cap: every byte outside graphic
/// ASCII, plus `%`, `?` and `#`, becomes `%XX` (uppercase hex), and when the
/// result exceeds `PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES`, leading encoded
/// bytes are dropped without splitting a `%XX` triple so the `#L..C..#slug#o..`
/// tail survives verbatim. A post-clamp collision is REFUSED by the caller,
/// never aliased.
fn shadow_public_obligation_id(assertion_id: &str) -> String {
    let prefix_len = DIRECT_SHADOW_PUBLIC_ID_PREFIX.len();
    let mut out = String::with_capacity(prefix_len + assertion_id.len() + 8);
    out.push_str(DIRECT_SHADOW_PUBLIC_ID_PREFIX);
    for byte in assertion_id.bytes() {
        if byte.is_ascii_graphic() && !matches!(byte, b'%' | b'?' | b'#') {
            out.push(byte as char);
        } else {
            let _ = write!(&mut out, "%{byte:02X}");
        }
    }
    let max = PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES;
    if out.len() <= max {
        return out;
    }
    let budget = max - prefix_len;
    let encoded_len = out.len() - prefix_len;
    let bytes = &out.as_bytes()[prefix_len..];
    let mut start = encoded_len - budget;
    // `%` appears only as a triple starter (a literal `%` is itself encoded),
    // so a cut landing inside a triple is detected by looking back two bytes.
    if start >= 1 && bytes[start - 1] == b'%' {
        start += 2;
    } else if start >= 2 && bytes[start - 2] == b'%' {
        start += 1;
    }
    let start = start.min(encoded_len);
    out.drain(prefix_len..prefix_len + start);
    out
}

/// The pinned semantic-digest recipe (deterministic on purpose: changing any
/// part of this projection later changes every shadow semantic digest):
/// the canonical trust-verifier-api `TrustObligation::
/// canonical_semantic_digest_sha256` over exactly
/// `{obligation_id: the public id, kind: the ROW's kind projected
/// variant-to-variant (ArithmeticSafety -> ArithmeticSafety, BoundsCheck ->
/// BoundsCheck; any other kind is the fail-closed NonDirectObligationKind
/// error — unreachable behind the admission gate, but never a wildcard),
/// contract_id: None, proof_item_id: None, source: the row's range rendered
/// through `module.files` (all-`None` `SourceLocation` when the row has no
/// range), description: the row's description, no summary facts, no
/// metadata}`.
///
/// Trust (Step 5): the projection moved from the hardcoded `ArithmeticSafety`
/// literal to the row's kind. Projection-FAITHFUL for every pre-existing row:
/// an ArithmeticSafety row projects the identical struct, so every existing
/// digest pin passes UNCHANGED; only BoundsCheck rows mint new digests.
fn shadow_semantic_digest(
    module: &Module,
    obligation: ProofId,
    kind: &ObligationKind,
    public_obligation_id: &str,
    description: &str,
    range: Option<&ProofObligationSourceRange>,
) -> Result<ProofDigest, DirectShadowBundleBuildError> {
    let projected_kind = match kind {
        ObligationKind::ArithmeticSafety => trust_verifier_api::ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck => trust_verifier_api::ObligationKind::BoundsCheck,
        other => {
            return Err(DirectShadowBundleBuildError::NonDirectObligationKind {
                obligation,
                kind: other.clone(),
            });
        }
    };
    let source = match range {
        None => trust_verifier_api::SourceLocation::default(),
        Some(range) => {
            let file = module.files.get(range.file as usize).cloned().ok_or(
                DirectShadowBundleBuildError::MalformedObligationRange {
                    obligation,
                    file: range.file,
                    files: module.files.len(),
                },
            )?;
            trust_verifier_api::SourceLocation {
                file: Some(file),
                line: Some(range.start_line),
                column: Some(range.start_col),
                end_line: Some(range.end_line),
                end_column: Some(range.end_col),
            }
        }
    };
    let projection = trust_verifier_api::TrustObligation {
        obligation_id: public_obligation_id.to_string(),
        kind: projected_kind,
        contract_id: None,
        proof_item_id: None,
        source,
        description: description.to_string(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    };
    let hex = projection.canonical_semantic_digest_sha256().map_err(|detail| {
        DirectShadowBundleBuildError::SemanticDigestRejected { obligation, detail }
    })?;
    proof_digest_from_sha256_hex(&hex).ok_or_else(|| {
        DirectShadowBundleBuildError::SemanticDigestRejected {
            obligation,
            detail: format!("canonical digest is not a usable non-zero SHA-256 hex string: {hex}"),
        }
    })
}

fn proof_digest_from_sha256_hex(value: &str) -> Option<ProofDigest> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return None;
    }
    let mut bytes = [0_u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let high = (pair[0] as char).to_digit(16)? as u8;
        let low = (pair[1] as char).to_digit(16)? as u8;
        bytes[index] = (high << 4) | low;
    }
    if bytes == [0; 32] {
        return None;
    }
    Some(ProofDigest::sha256(bytes))
}

/// The shadow lineage: ONE `Frontend` node, sole root, carrying every
/// obligation row. `source_module` is the PRISTINE module digest — the
/// independently recomputable anchor to the emitted direct artifact —
/// `target_module` the enriched module this bundle carries. The typed stage
/// difference from the MIR lane's `TrustIrLowering` is deliberate: nothing
/// here lowered MIR, and the stage is part of the node's digest.
/// The ONE root `direct_shadow_lineage` builds. Named so the planner can use
/// it directly instead of asserting its way back out of the manifest: the
/// manifest is constructed four lines below with exactly this root, so
/// `roots.first().expect(..)` was restating a local literal as a panic.
const DIRECT_SHADOW_LINEAGE_ROOT: ProofLineageId = ProofLineageId::new(0);

fn direct_shadow_lineage(
    pristine_module_digest: ProofDigest,
    enriched_module_digest: ProofDigest,
    obligations: Vec<ProofId>,
) -> ProofLineageManifest {
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "trust-thir-lower-direct-to-trust_ir-shadow",
            "TRust",
            TRUST_DIRECT_SHADOW_TRANSFORM_VERSION,
        ),
        pristine_module_digest,
        enriched_module_digest,
    );
    node.obligations = obligations;
    node.replay = Some(
        ProofReplayIdentity::new(
            "Trust.direct-shadow-admission",
            format!(
                "trust-ir-bridge emit-direct-shadow-verification-bundle --contract \
                 {TRUST_DIRECT_SHADOW_TRANSFORM_VERSION}; {DIRECT_SHADOW_WIRE_DISCLOSURE}"
            ),
        )
        .with_transcript_digest(shadow_replay_transcript_digest(
            "trust-direct-shadow-admission",
            pristine_module_digest,
            enriched_module_digest,
            &node.obligations,
        )),
    );
    ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![node],
        roots: vec![DIRECT_SHADOW_LINEAGE_ROOT],
    }
}

fn direct_shadow_trust_mc_request_provenance(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    pristine_module_digest: ProofDigest,
    enriched_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> NativeRequestProvenance {
    NativeRequestProvenance::trust_mc(
        NativeToolIdentity::new("trust_mc")
            .with_version(TRUST_DIRECT_SHADOW_TRANSFORM_VERSION)
            .with_revision(TRUST_DIRECT_SHADOW_TRANSFORM_VERSION),
    )
    .with_solver(NativeToolIdentity::new("ay"))
    .with_replay(
        ProofReplayIdentity::new(
            "trust_mc",
            format!(
                "trust_mc-driver native-bundle --mode chc --diagnostic-only \
                 --trust-direct-shadow-contract {TRUST_DIRECT_SHADOW_TRANSFORM_VERSION}; \
                 {DIRECT_SHADOW_WIRE_DISCLOSURE}"
            ),
        )
        .with_transcript_digest(shadow_replay_transcript_digest(
            "trust_mc-direct-shadow",
            pristine_module_digest,
            enriched_module_digest,
            obligations,
        )),
    )
    .with_replay_context(native_replay_context(module, compiler_facts, obligations))
}

/// Domain-separated from the MIR lane's replay-transcript digest on purpose:
/// even byte-identical framing material can never collide across lanes.
fn shadow_replay_transcript_digest(
    lane: &str,
    pristine_module_digest: ProofDigest,
    enriched_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> ProofDigest {
    let mut bytes = Vec::with_capacity(96 + lane.len() + obligations.len().saturating_mul(4));
    shadow_append_len_prefixed(&mut bytes, lane.as_bytes());
    shadow_append_digest(&mut bytes, pristine_module_digest);
    shadow_append_digest(&mut bytes, enriched_module_digest);
    bytes.extend_from_slice(&shadow_len_u64(obligations.len()).to_be_bytes());
    for obligation in obligations {
        bytes.extend_from_slice(&obligation.index().to_be_bytes());
    }
    ProofDigest::sha256_domain("trust.direct-shadow.replay-transcript.v1", &bytes)
}

/// A length into the canonical `u64` wire framing, with NO panic path.
///
/// This is total by the compile-time proof below, not by swapping a counted
/// construct for an uncounted one: on every target where `usize` is no wider
/// than `u64` there is no truncating case to handle, and the assertion makes
/// a target where that stopped holding a BUILD failure rather than a silently
/// wrong digest. The `.expect("exceeds canonical u64 framing")` it replaces
/// could never fire on any such target, so nothing that could fail moved.
const _: () = assert!(
    usize::BITS <= u64::BITS,
    "shadow wire framing widens a length to u64; a wider usize would truncate"
);
fn shadow_len_u64(len: usize) -> u64 {
    len as u64
}

fn shadow_append_digest(bytes: &mut Vec<u8>, digest: ProofDigest) {
    bytes.push(match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    });
    bytes.extend_from_slice(&digest.bytes);
}

fn shadow_append_len_prefixed(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(&shadow_len_u64(value.len()).to_be_bytes());
    bytes.extend_from_slice(value);
}

#[cfg(test)]
mod tests {
    use trust_ir::{
        Block, BlockId, Constant, FuncTy, Function, Inst, InstrNode, ObligationSite,
        ProofAnnotation, ProofEvidence, ProofObligation, ProofObligationSourceIdentity, SourceSpan,
        Ty, ValueId,
    };

    use super::*;

    fn digest(seed: u8) -> ProofDigest {
        ProofDigest::sha256([seed; 32])
    }

    fn bodied_function(
        id: FuncId,
        name: &str,
        ft: trust_ir::FuncTyId,
        producer: Producer,
    ) -> Function {
        let mut function = Function::new(id, name, ft, BlockId::new(0)).with_producer(producer);
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(0)),
        );
        let mut assert_one = InstrNode::new(Inst::Assert {
            cond: ValueId::new(0),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        })
        .with_proof(ProofAnnotation::NoOverflow);
        assert_one.span = Some(SourceSpan { file: 0, line: 15, col: 4 });
        block.body.push(assert_one);
        let mut assert_two = InstrNode::new(Inst::Assert {
            cond: ValueId::new(0),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        })
        .with_proof(ProofAnnotation::DivNonZero);
        assert_two.span = Some(SourceSpan { file: 0, line: 15, col: 4 });
        block.body.push(assert_two);
        block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        function.blocks.push(block);
        function
    }

    fn direct_row(
        id: u32,
        function: FuncId,
        assertion_id: &str,
        description: &str,
        range: Option<ProofObligationSourceRange>,
    ) -> ProofObligation {
        let mut source =
            ProofObligationSourceIdentity::new(DIRECT_SHADOW_ADMITTED_SOURCE_ID, assertion_id);
        if let Some(range) = range {
            source = source.with_range(range);
        }
        ProofObligation::new(
            ProofId::new(id),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            description,
        )
        .with_function(function)
        .with_source(source)
        .with_site(ObligationSite::new(function, BlockId::new(0), 1))
    }

    /// The fixture mirrors the direct finalizer's output shape: bodied
    /// `Producer::TRust` owners, a claim-free `Producer::Clean` join row and
    /// a bodyless `TRust` extern declaration as translation CONTEXT, and
    /// Pending / ArithmeticSafety / formula-free / public-identity-free rows
    /// under the admitted `source_id`, function- and site-bound, with the
    /// direct `{crate}::{def_path}#L{line}C{col}#{slug}#o{occ}` identity
    /// grammar. Row 3 is deliberately rangeless (the dummy-span disclosure
    /// path).
    pub(super) fn direct_shadow_module_fixture() -> Module {
        let mut module = Module::new("shadow_fixture");
        let file = module.intern_file("src/arith.rs").expect("Module::intern_file: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(bodied_function(
                FuncId::new(0),
                "shadow_fixture::arith::checked_add",
                ft,
                Producer::TRust,
            ))
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(bodied_function(
                FuncId::new(1),
                "shadow_fixture::arith::checked_mul",
                ft,
                Producer::TRust,
            ))
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(bodied_function(
                FuncId::new(2),
                "shadow_fixture::clean::lemma_ctx",
                ft,
                Producer::Clean,
            ))
            .expect("Module::try_add_function: test fixture");
        let decl_ft = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: true,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .try_add_function(
                Function::new(FuncId::new(3), "core::panicking::panic", decl_ft, BlockId::new(0))
                    .with_producer(Producer::TRust),
            )
            .expect("Module::try_add_function: test fixture");

        let range = ProofObligationSourceRange {
            file,
            start_line: 15,
            start_col: 4,
            end_line: 15,
            end_col: 11,
        };
        module.proof_obligations.push(direct_row(
            0,
            FuncId::new(0),
            "shadow_fixture::arith::checked_add#L15C4#overflow#o0",
            "direct THIR Assert (overflow) at L15C4 of `shadow_fixture::arith::checked_add`: \
             arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED.",
            Some(range),
        ));
        module.proof_obligations.push(direct_row(
            1,
            FuncId::new(0),
            "shadow_fixture::arith::checked_add#L15C4#overflow#o1",
            "direct THIR Assert (overflow) at L15C4 of `shadow_fixture::arith::checked_add`: \
             arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED.",
            Some(range),
        ));
        module.proof_obligations.push(direct_row(
            2,
            FuncId::new(1),
            "shadow_fixture::arith::checked_mul#L20C2#div_by_zero#o0",
            "direct THIR Assert (div_by_zero) at L20C2 of `shadow_fixture::arith::checked_mul`: \
             divisor is nonzero. RECORDED BY THE LOWERING, NOT PROVED.",
            Some(ProofObligationSourceRange {
                file,
                start_line: 20,
                start_col: 2,
                end_line: 20,
                end_col: 9,
            }),
        ));
        module.proof_obligations.push(direct_row(
            3,
            FuncId::new(0),
            "shadow_fixture::arith::checked_add#L0C0#overflow#o0",
            "direct THIR Assert (overflow) at L0C0 of `shadow_fixture::arith::checked_add`: \
             arithmetic does not overflow. RECORDED BY THE LOWERING, NOT PROVED.",
            None,
        ));
        module
    }

    #[test]
    fn shadow_bundle_builds_with_shadow_wire_identity_and_owner_scoped_requests() {
        let pristine = direct_shadow_module_fixture().stable_digest();
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("the direct fixture plans a shadow bundle");

        // Disclosure: the typed statement of what the lineage does and does
        // not bind, with the unrequestable row COUNTED, not dropped.
        assert_eq!(shadow.disclosure.pristine_module_digest, pristine);
        assert_ne!(shadow.disclosure.enriched_module_digest, pristine);
        assert_eq!(shadow.disclosure.obligations_planned, 3);
        assert_eq!(shadow.disclosure.obligations_unrequestable_missing_range, 1);
        assert_eq!(shadow.disclosure.non_applying_checks.len(), 7);
        assert_eq!(shadow.disclosure.non_applying_checks, DIRECT_SHADOW_NON_APPLYING_CHECKS);

        let bundle = shadow.bundle();
        // The shadow wire pair, hardcoded — and the absent source digest.
        assert_eq!(bundle.producer, NativeBundleProducer::TRust);
        assert!(matches!(bundle.input, NativeAdapterInput::TrustIrModule));
        assert_eq!(bundle.source_digest(), None);
        assert_eq!(bundle.provenance.source_digest, None);
        assert_eq!(bundle.provenance.source_language, NativeSourceLanguage::TrustIr);
        assert_eq!(bundle.provenance.toolchain, vec![direct_shadow_tool_identity()]);
        assert_eq!(bundle.trust_ir_module_digest, shadow.disclosure.enriched_module_digest);

        // Lineage: one Frontend node, sole root, pristine -> enriched, with
        // the wire disclosure in its replay invocation.
        assert_eq!(bundle.lineage.nodes.len(), 1);
        let node = &bundle.lineage.nodes[0];
        assert_eq!(node.transform.stage, ProofTransformStage::Frontend);
        assert_eq!(node.transform.producer, "TRust");
        assert_eq!(node.transform.version, TRUST_DIRECT_SHADOW_TRANSFORM_VERSION);
        assert_eq!(node.source_module, pristine);
        assert_eq!(node.target_module, shadow.disclosure.enriched_module_digest);
        assert_eq!(node.obligations.len(), 4, "every row rides the lineage node");
        assert!(
            node.replay
                .as_ref()
                .is_some_and(|replay| replay.invocation.contains(DIRECT_SHADOW_WIRE_DISCLOSURE)),
            "the lineage replay invocation must carry the wire disclosure"
        );

        // Requests: owner-major, one TrustMc Chc request per RANGED row, the
        // rangeless row in none of them, every invocation disclosure-stamped.
        assert_eq!(bundle.requests.len(), 3);
        let expected: [(u32, FuncId, u32); 3] =
            [(0, FuncId::new(0), 0), (1, FuncId::new(0), 1), (2, FuncId::new(1), 2)];
        for (&(id, function, obligation), request) in expected.iter().zip(&bundle.requests) {
            let NativeVerificationRequest::TrustMc(request) = request else {
                panic!("the shadow planner emits TrustMc requests only, got {request:?}");
            };
            assert_eq!(request.id, NativeRequestId::new(id));
            assert_eq!(request.mode, TrustMcVerificationMode::Chc);
            assert_eq!(request.function, function);
            assert_eq!(request.obligations, vec![ProofId::new(obligation)]);
            assert!(request.options.chc.emit_horn_clauses);
            assert_eq!(request.options, trust_mc_chc_request_options());
            assert_eq!(
                request.provenance.expected_verifier.version.as_deref(),
                Some(TRUST_DIRECT_SHADOW_TRANSFORM_VERSION)
            );
            assert!(
                request.provenance.replay.as_ref().is_some_and(|replay| replay
                    .invocation
                    .contains(DIRECT_SHADOW_WIRE_DISCLOSURE)),
                "every request replay invocation must carry the wire disclosure"
            );
        }
        assert!(
            bundle
                .requests
                .iter()
                .all(|request| { !request.obligations().contains(&ProofId::new(3)) }),
            "the rangeless row must never be requested"
        );

        // No verdict write-back: every row in the carried module stays Pending.
        assert!(
            bundle
                .module
                .proof_obligations
                .iter()
                .all(|obligation| obligation.status == ProofStatus::Pending)
        );
        // No planner-manufactured evidence.
        assert!(bundle.evidence_bundles.is_empty());

        // Public identities: minted per ROW (rangeless included), "direct:"
        // prefixed, canonical, `#` percent-encoded, sidecar == embedded.
        for obligation in &bundle.module.proof_obligations {
            let public = obligation
                .source
                .as_ref()
                .and_then(|source| source.public.as_ref())
                .expect("every row is enriched");
            assert!(public.obligation_id.starts_with(DIRECT_SHADOW_PUBLIC_ID_PREFIX));
            assert!(trust_ir::proof::is_canonical_public_obligation_id(&public.obligation_id));
            let sidecar =
                bundle.obligation_source(obligation.id).expect("every row has a sidecar entry");
            assert_eq!(sidecar.public_obligation_id, public.obligation_id);
        }
        assert_eq!(
            bundle.module.proof_obligations[0]
                .source
                .as_ref()
                .unwrap()
                .public
                .as_ref()
                .unwrap()
                .obligation_id,
            "direct:shadow_fixture::arith::checked_add%23L15C4%23overflow%23o0"
        );

        bundle.validate().expect("the shadow bundle validates");
    }

    #[test]
    fn shadow_semantic_digest_recipe_is_pinned_for_ranged_and_rangeless_rows() {
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("shadow bundle builds");
        let bundle = shadow.bundle();

        let minted_hex = |index: usize| {
            let public = bundle.module.proof_obligations[index]
                .source
                .as_ref()
                .unwrap()
                .public
                .as_ref()
                .unwrap();
            let mut hex = String::new();
            for byte in &public.semantic_digest.bytes {
                let _ = write!(&mut hex, "{byte:02x}");
            }
            (public.obligation_id.clone(), hex)
        };

        // Ranged row 0: SourceLocation is the row's range rendered through
        // module.files, both endpoints.
        let (public_id, hex) = minted_hex(0);
        let expected = trust_verifier_api::TrustObligation {
            obligation_id: public_id,
            kind: trust_verifier_api::ObligationKind::ArithmeticSafety,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation {
                file: Some("src/arith.rs".to_string()),
                line: Some(15),
                column: Some(4),
                end_line: Some(15),
                end_column: Some(11),
            },
            description: bundle.module.proof_obligations[0].description.clone(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
        .canonical_semantic_digest_sha256()
        .expect("the projection is admissible");
        assert_eq!(hex, expected, "the ranged-row digest recipe moved");

        // Rangeless row 3: the PINNED all-None SourceLocation.
        let (public_id, hex) = minted_hex(3);
        let expected = trust_verifier_api::TrustObligation {
            obligation_id: public_id,
            kind: trust_verifier_api::ObligationKind::ArithmeticSafety,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: bundle.module.proof_obligations[3].description.clone(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
        .canonical_semantic_digest_sha256()
        .expect("the projection is admissible");
        assert_eq!(hex, expected, "the rangeless-row digest recipe moved");
    }

    /// Trust (Step 5): a `BoundsCheck` row — the direct installer's second
    /// minted kind — is PLANNED, and the semantic-digest projection carries
    /// the row's kind rather than the retired `ArithmeticSafety` literal. A
    /// mutation hardcoding the literal back is caught here: the expected
    /// digest below is computed with `ObligationKind::BoundsCheck`.
    #[test]
    fn bounds_check_rows_are_planned_and_the_digest_projects_their_kind() {
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[1].kind = ObligationKind::BoundsCheck;
        module.proof_obligations[1].source.as_mut().unwrap().assertion_id =
            "shadow_fixture::arith::checked_add#L15C4#bounds_check#o0".to_string();
        module.proof_obligations[1].description = "direct THIR Assert (bounds_check) at L15C4 of \
             `shadow_fixture::arith::checked_add`: index is in bounds. RECORDED BY THE \
             LOWERING, NOT PROVED."
            .to_string();

        let shadow = direct_shadow_verification_bundle_from_module(module)
            .expect("a BoundsCheck row is an admitted direct kind and must plan");
        let bundle = shadow.bundle();

        let row = &bundle.module.proof_obligations[1];
        assert_eq!(row.kind, ObligationKind::BoundsCheck);
        let public = row.source.as_ref().unwrap().public.as_ref().expect("row is enriched");
        assert_eq!(
            public.obligation_id,
            "direct:shadow_fixture::arith::checked_add%23L15C4%23bounds_check%23o0"
        );

        let mut hex = String::new();
        for byte in &public.semantic_digest.bytes {
            let _ = write!(&mut hex, "{byte:02x}");
        }
        let expected = trust_verifier_api::TrustObligation {
            obligation_id: public.obligation_id.clone(),
            kind: trust_verifier_api::ObligationKind::BoundsCheck,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation {
                file: Some("src/arith.rs".to_string()),
                line: Some(15),
                column: Some(4),
                end_line: Some(15),
                end_column: Some(11),
            },
            description: row.description.clone(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
        .canonical_semantic_digest_sha256()
        .expect("the projection is admissible");
        assert_eq!(
            hex, expected,
            "the BoundsCheck digest must be minted over kind BoundsCheck, not the retired \
             ArithmeticSafety literal"
        );

        bundle.validate().expect("the mixed-kind shadow bundle validates");
    }

    #[test]
    fn shadow_bundle_serialized_form_keeps_the_shadow_discriminators() {
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("shadow bundle builds");
        let bundle = shadow.acknowledge_unanchored_lineage();

        let json = serde_json::to_string(&bundle).expect("shadow bundle serializes");
        let decoded: NativeVerificationBundle =
            serde_json::from_str(&json).expect("shadow bundle deserializes");

        // The in-process typestate is gone, but the wire identity is not:
        // the digest-bound tag pair and the in-band disclosure strings are
        // what a consumer of the serialized form refuses on.
        assert_eq!(decoded.producer, NativeBundleProducer::TRust);
        assert!(matches!(decoded.input, NativeAdapterInput::TrustIrModule));
        assert_eq!(decoded.source_digest(), None);
        assert_eq!(decoded.provenance.source_digest, None);
        assert!(
            decoded.lineage.nodes[0]
                .replay
                .as_ref()
                .is_some_and(|replay| replay.invocation.contains(DIRECT_SHADOW_WIRE_DISCLOSURE))
        );
        assert!(decoded.requests.iter().all(|request| {
            request
                .provenance()
                .replay_identity()
                .is_some_and(|replay| replay.invocation.contains(DIRECT_SHADOW_WIRE_DISCLOSURE))
        }));
        assert_eq!(decoded, bundle, "serde must round-trip the shadow bundle");
        assert_eq!(decoded.stable_digest(), bundle.stable_digest());
        decoded.validate().expect("the deserialized shadow bundle validates");
    }

    #[test]
    fn shadow_bundle_digest_separates_from_the_mir_lane_at_both_wire_tags() {
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("shadow bundle builds");
        let pristine = shadow.disclosure.pristine_module_digest;
        let bundle = shadow.acknowledge_unanchored_lineage();
        let shadow_digest = bundle.stable_digest();

        // Producer tag: TRust (0) vs TrustIr (3) is framed into the digest.
        let mut relabelled = bundle.clone();
        relabelled.producer = NativeBundleProducer::TrustIr;
        assert_ne!(
            relabelled.stable_digest(),
            shadow_digest,
            "the producer tag must be digest-separating"
        );

        // Input tag: TrustIrModule (bare 1) vs RustMir (0 + digest) likewise.
        let mut relabelled = bundle.clone();
        relabelled.input = NativeAdapterInput::RustMir { body_digest: pristine };
        assert_ne!(
            relabelled.stable_digest(),
            shadow_digest,
            "the input tag must be digest-separating"
        );
    }

    /// The anti-relabelling boundary, pinned SYMMETRICALLY: the MIR planner
    /// still refuses the direct module (its pinned gate, untouched), and the
    /// sibling refuses a MIR-compatibility module with a typed PRODUCER error
    /// — before any row-shape check can fire incidentally, certificates
    /// included.
    #[test]
    fn mir_planner_refuses_the_shadow_module_and_the_sibling_refuses_a_mir_module() {
        let error = crate::native_request::native_verification_bundle_from_module(
            direct_shadow_module_fixture(),
            digest(0x51),
            FuncId::new(0),
        )
        .expect_err("a direct module must not enter the MIR-compatibility planner");
        assert_eq!(
            error,
            NativeVerificationBundleBuildError::NonMirCompatibilityProducer {
                function: FuncId::new(0),
                producer: Some(Producer::TRust),
            }
        );

        // Converse: a Producer::TrustIr module — even one carrying a
        // certificate — is refused by the sibling on the PRODUCER axis.
        let mut mir_module = direct_shadow_module_fixture();
        for function in &mut mir_module.functions {
            function.producer = Some(Producer::TrustIr);
        }
        mir_module.proof_certificates.push(trust_ir::ProofCertificate {
            obligation: ProofId::new(0),
            prover: "trust_vc".to_string(),
            evidence: ProofEvidence::LeanProof("exact sorry_free".into()),
            // v41: no native evidence bundle to project a coverage assurance from.
            assurance: None,
        });
        let error = direct_shadow_verification_bundle_from_module(mir_module)
            .expect_err("a MIR-compatibility module must not be re-wrapped as a shadow bundle");
        assert_eq!(
            error,
            DirectShadowBundleBuildError::NonDirectProducer {
                function: FuncId::new(0),
                producer: Some(Producer::TrustIr),
            }
        );

        // Missing provenance fails closed on the same axis.
        let mut unlabelled = direct_shadow_module_fixture();
        unlabelled.functions[1].producer = None;
        let error = direct_shadow_verification_bundle_from_module(unlabelled)
            .expect_err("an unlabelled function must not be inferred direct");
        assert_eq!(
            error,
            DirectShadowBundleBuildError::NonDirectProducer {
                function: FuncId::new(1),
                producer: None,
            }
        );
    }

    /// The claim-free contract, row by row: a verdict-bearing, decorated, or
    /// foreign row is refused with its own typed error, never planned.
    #[test]
    fn discharged_or_decorated_direct_rows_are_refused() {
        // A Discharged row planned would be a verdict entering the shadow
        // lane — the exact thing the hard boundary forbids.
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[1].status = ProofStatus::Discharged;
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a Discharged row must not be planned"),
            DirectShadowBundleBuildError::NonPendingObligation {
                obligation: ProofId::new(1),
                status: ProofStatus::Discharged,
            }
        );

        // Trust (Step 5, the M-THIRD-KIND pin at GATE 2): the admitted set is
        // EXACTLY {ArithmeticSafety, BoundsCheck}. Postcondition (the original
        // pin, KEPT) and PanicFreedom (the nearest-neighbour kind a careless
        // widening would admit — bounds checks ROUTE like panic-freedom, but
        // the direct lane does not mint it) are each refused with the typed
        // kind error.
        for foreign in [ObligationKind::Postcondition, ObligationKind::PanicFreedom] {
            let mut module = direct_shadow_module_fixture();
            module.proof_obligations[0].kind = foreign.clone();
            assert_eq!(
                direct_shadow_verification_bundle_from_module(module)
                    .expect_err("a foreign kind must not be planned"),
                DirectShadowBundleBuildError::NonDirectObligationKind {
                    obligation: ProofId::new(0),
                    kind: foreign,
                }
            );
        }

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].formula =
            Some(trust_ir::ProofFormula::smtlib2("(assert true)", "Bool"));
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a formula-bearing row must not be planned"),
            DirectShadowBundleBuildError::FormulaBearingObligation(ProofId::new(0))
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[2].source.as_mut().unwrap().source_id =
            "trust-ir-frontend/mir-assert@1".to_string();
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a foreign source vocabulary must not be planned"),
            DirectShadowBundleBuildError::ForeignObligationSourceId {
                obligation: ProofId::new(2),
                source_id: "trust-ir-frontend/mir-assert@1".to_string(),
            }
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].source.as_mut().unwrap().public =
            Some(PublicObligationIdentity {
                obligation_id: "vc:foo:arithmetic_safety:0".to_string(),
                semantic_digest: digest(0x61),
            });
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a pre-enriched row must not be planned"),
            DirectShadowBundleBuildError::PreEnrichedPublicIdentity(ProofId::new(0))
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].source = None;
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a source-less row must not be planned"),
            DirectShadowBundleBuildError::MissingObligationSource(ProofId::new(0))
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].function = None;
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("an unscoped row must not be planned"),
            DirectShadowBundleBuildError::UnscopedObligation(ProofId::new(0))
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].site = None;
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a site-less row must not be planned"),
            DirectShadowBundleBuildError::MissingObligationSite(ProofId::new(0))
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_certificates.push(trust_ir::ProofCertificate {
            obligation: ProofId::new(0),
            prover: "manual".to_string(),
            evidence: ProofEvidence::Trusted("manual audit".to_string()),
            // v41: no native evidence bundle to project a coverage assurance from.
            assurance: None,
        });
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a certificate-bearing module must not be planned"),
            DirectShadowBundleBuildError::CertificateBearingModule { certificates: 1 }
        );
    }

    /// Owners are DERIVED from the rows, which makes the reused planner's
    /// function-mismatch check a tautology — so the compensating control must
    /// hold: a row smuggled onto a foreign (bodyless / non-direct / absent)
    /// function is refused with the reason, never planned into a request.
    #[test]
    fn rows_owned_by_ineligible_functions_are_refused_with_the_reason() {
        // A bodyless TRust declaration: a Chc request about it would die
        // later inside trust-mc as a mislabeled missing-function failure.
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[2].function = Some(FuncId::new(3));
        module.proof_obligations[2].site =
            Some(ObligationSite::new(FuncId::new(3), BlockId::new(0), 1));
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a bodyless owner must be refused"),
            DirectShadowBundleBuildError::OwnerNotDirectEligible {
                obligation: ProofId::new(2),
                function: FuncId::new(3),
                reason: DirectOwnerIneligibility::Bodyless,
            }
        );

        // A Producer::Clean join row is claim-free translation context and
        // may not OWN direct rows.
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[2].function = Some(FuncId::new(2));
        module.proof_obligations[2].site =
            Some(ObligationSite::new(FuncId::new(2), BlockId::new(0), 1));
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a Clean-owned row must be refused"),
            DirectShadowBundleBuildError::OwnerNotDirectEligible {
                obligation: ProofId::new(2),
                function: FuncId::new(2),
                reason: DirectOwnerIneligibility::NonDirectProducer(Some(Producer::Clean)),
            }
        );

        // A function the module does not declare at all.
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[2].function = Some(FuncId::new(99));
        module.proof_obligations[2].site =
            Some(ObligationSite::new(FuncId::new(99), BlockId::new(0), 1));
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("a foreign-function row must be refused"),
            DirectShadowBundleBuildError::OwnerNotDirectEligible {
                obligation: ProofId::new(2),
                function: FuncId::new(99),
                reason: DirectOwnerIneligibility::NotInModule,
            }
        );
    }

    #[test]
    fn all_rangeless_rows_fail_closed_as_no_requestable_obligations() {
        let mut module = direct_shadow_module_fixture();
        for obligation in &mut module.proof_obligations {
            obligation.source.as_mut().unwrap().range = None;
        }
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("an all-rangeless module has nothing to shadow-verify"),
            DirectShadowBundleBuildError::NoRequestableObligations { obligations: 4 }
        );
    }

    /// Downstream scope re-check is real, not assumed: tampering a planned
    /// request onto the other owner is refused by the trust-ir validator at
    /// request granularity.
    #[test]
    fn request_scope_tamper_is_refused_by_the_trust_ir_validator() {
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("shadow bundle builds");
        let mut bundle = shadow.acknowledge_unanchored_lineage();
        let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[0] else {
            panic!("expected a TrustMc request");
        };
        assert_eq!(request.function, FuncId::new(0));
        request.function = FuncId::new(1);

        let errors = bundle.validate().expect_err("a cross-owner tamper must be refused");
        assert!(
            errors.iter().any(|error| matches!(
                error,
                NativeVerificationBundleError::RequestObligationFunctionMismatch {
                    request: NativeRequestId(0),
                    obligation: ProofId(0),
                    expected: FuncId(1),
                    actual: Some(FuncId(0)),
                }
            )),
            "expected RequestObligationFunctionMismatch, got {errors:?}"
        );
    }

    /// The counterfeit-anchor hazard, pinned as the reason the decision is
    /// what it is: a stamped `provenance.source_digest` on a TrustIrModule
    /// bundle VALIDATES while binding nothing (the InputDigestMismatch
    /// cross-check needs an input digest to fire), so the honest spelling —
    /// and the sibling's pinned behavior — is None.
    #[test]
    fn a_counterfeit_provenance_source_digest_would_validate_while_binding_nothing() {
        let shadow = direct_shadow_verification_bundle_from_module(direct_shadow_module_fixture())
            .expect("shadow bundle builds");
        let bundle = shadow.acknowledge_unanchored_lineage();
        assert_eq!(
            bundle.provenance.source_digest, None,
            "the sibling must never stamp a source digest it cannot bind"
        );

        let mut counterfeit = bundle.clone();
        counterfeit.provenance.source_digest = Some(digest(0x77));
        assert!(
            counterfeit.validate().is_ok(),
            "a counterfeit Some(digest) validates unconstrained — which is exactly why \
             stamping one would be dishonest, and why consumers must refuse on the \
             disclosure instead"
        );
    }

    #[test]
    fn public_id_encoding_clamps_head_preserving_suffix_and_collisions_are_refused() {
        // Injective encoding of the canonical-hostile bytes.
        assert_eq!(
            shadow_public_obligation_id("a b#L1C2#overflow#o0"),
            "direct:a%20b%23L1C2%23overflow%23o0"
        );
        assert_eq!(shadow_public_obligation_id("a%b?c"), "direct:a%25b%3Fc");

        // Over-cap ids clamp from the HEAD; the distinguishing suffix
        // survives verbatim and the result stays canonical and within cap.
        let long_head = "a".repeat(1000);
        let long_id = format!("{long_head}#L1C1#overflow#o0");
        let clamped = shadow_public_obligation_id(&long_id);
        assert!(clamped.len() <= PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES);
        assert!(clamped.starts_with(DIRECT_SHADOW_PUBLIC_ID_PREFIX));
        assert!(clamped.ends_with("%23L1C1%23overflow%23o0"));
        assert!(trust_ir::proof::is_canonical_public_obligation_id(&clamped));

        // Two rows whose ids differ only in the clamped-away head bytes
        // collide post-clamp — REFUSED, never aliased.
        let mut module = direct_shadow_module_fixture();
        module.proof_obligations[0].source.as_mut().unwrap().assertion_id =
            format!("{}{}", "x".repeat(6), &long_id[6..]);
        module.proof_obligations[1].source.as_mut().unwrap().assertion_id =
            format!("{}{}", "y".repeat(6), &long_id[6..]);
        let error = direct_shadow_verification_bundle_from_module(module)
            .expect_err("a post-clamp collision must be refused");
        assert!(
            matches!(
                &error,
                DirectShadowBundleBuildError::PublicObligationIdCollision {
                    first: ProofId(0),
                    second: ProofId(1),
                    ..
                }
            ),
            "expected PublicObligationIdCollision, got {error:?}"
        );
    }

    #[test]
    fn empty_and_obligation_free_modules_fail_closed() {
        assert_eq!(
            direct_shadow_verification_bundle_from_module(Module::new("empty"))
                .expect_err("an empty module is refused"),
            DirectShadowBundleBuildError::EmptyModule
        );

        let mut module = direct_shadow_module_fixture();
        module.proof_obligations.clear();
        assert_eq!(
            direct_shadow_verification_bundle_from_module(module)
                .expect_err("an obligation-free module is refused"),
            DirectShadowBundleBuildError::NoDirectObligations
        );
    }
}

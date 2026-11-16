//! Trust native verifier request planning over upstream TrustIr request types.
//!
//! The schema types live in `trust_ir`; this bridge only decides how a lowered
//! Trust module is split into primary TrustVc and TrustMc requests, with
//! body-aware TrustWp alternatives for postconditions. All strategies retain
//! one module, source identity, and proof-obligation inventory.

use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;
use trust_ir::binary::{
    BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ModuleObligationRows,
    ModuleSymbolProjection, ProjectedModuleBinaryPlan,
};
use trust_ir::{
    FuncId, Module, NativeAdapterInput, NativeAssertionId, NativeBundleProducer,
    NativeCompilerFactRef, NativeCompilerFacts, NativeDiagnosticsPolicy, NativeEvidenceArtifact,
    NativeEvidenceArtifactKind, NativeEvidenceBundle, NativeMonomorphizationFact,
    NativeMonomorphizationId, NativeObligationCause, NativeObligationSource, NativeReplayAtom,
    NativeReplayAtomId, NativeReplayContext, NativeRequestId, NativeRequestProvenance,
    NativeSourceLanguage, NativeToolIdentity, NativeUnsupportedMode, NativeUnsupportedModeReason,
    NativeVerificationBundle, NativeVerificationBundleError, NativeVerificationRequest,
    ObligationKind, Producer, ProofCertificate, ProofDigest, ProofDigestAlgorithm, ProofId,
    ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofReplayIdentity, ProofTransform,
    ProofTransformStage, SourceSpan, TrustMcArithmeticModel, TrustMcBmcOptions, TrustMcChcEngine,
    TrustMcChcOptions, TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeRequest,
    TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions, TrustMcSlicingMode,
    TrustMcVerificationMode, TrustVcNativeEvidenceBundle, TrustVcNativeRequest,
    TrustVcRequestOptions, TrustVcVerificationMode, TrustWpNativeRequest, TrustWpRequestOptions,
    TrustWpVerificationMode,
};

#[cfg(test)]
use crate::lower::TRUST_OBLIGATION_SOURCE_SCHEMA;

#[cfg(test)]
#[path = "native_request_metadata_tests.rs"]
pub(super) mod metadata_tests;

/// Transform version string used in TrustIr-bridge lineage for this boundary.
pub const TRUST_NATIVE_REQUEST_TRANSFORM_VERSION: &str = "native-request-schema-v1";
/// Trust-owned admission contract required for native TrustMc proof-grade requests.
pub const TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION: &str =
    "trust-mc-native-admission-contract-v1";
/// TrustIr bridge package version reported in compiler-emitted native bundle metadata.
const TRUST_NATIVE_REQUEST_COMPILER_VERSION: &str = env!("CARGO_PKG_VERSION");
/// TrustIr bridge revision label for deterministic native-request planning.
const TRUST_NATIVE_REQUEST_COMPILER_REVISION: &str = TRUST_NATIVE_REQUEST_TRANSFORM_VERSION;
/// TrustVc native request interface version expected by TrustIr-bridge bundles.
const TRUST_VC_NATIVE_REQUEST_INTERFACE_VERSION: &str = "trust-vc-native-request-v1";
/// TrustVc interface revision reported with request provenance.
const TRUST_VC_NATIVE_REQUEST_INTERFACE_REVISION: &str = TRUST_NATIVE_REQUEST_TRANSFORM_VERSION;
/// Lean proof-kernel interface version expected for TrustVc certificate replay.
const TRUST_VC_LEAN_SOLVER_INTERFACE_VERSION: &str = "lean4-trust_vc-proof-kernel-v1";

/// Builder errors for the TrustIr MIR-compatibility native-request planner.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum NativeVerificationBundleBuildError {
    #[error("native verification module has no binary identity: {0}")]
    ModuleBinaryIdentity(BinaryProjectionError),
    #[error("cannot emit native verification bundle for an empty TrustIr module")]
    EmptyModule,
    #[error("native request target function {0} is missing from the TrustIr module")]
    MissingFunction(FuncId),
    #[error("cannot emit native verification bundle without proof obligations")]
    EmptyObligations,
    #[error("native proof obligation {0} is missing exact embedded source identity")]
    MissingObligationSource(ProofId),
    #[error("native proof obligation {0} is missing its atomic public obligation identity")]
    MissingPublicObligationIdentity(ProofId),
    #[error(
        "native proof obligation {obligation} is scoped to function {actual:?}, expected {expected}"
    )]
    ObligationFunctionMismatch { obligation: ProofId, expected: FuncId, actual: Option<FuncId> },
    #[error(
        "cannot emit a native verification bundle with non-authoritative source digest algorithm {algorithm:?}; SHA-256 is required"
    )]
    NonAuthoritativeSourceDigest { algorithm: ProofDigestAlgorithm },
    #[error(
        "cannot emit a native verification bundle with non-authoritative TrustIr module digest algorithm {algorithm:?}; SHA-256 is required"
    )]
    NonAuthoritativeModuleDigest { algorithm: ProofDigestAlgorithm },
    #[error(
        "cannot emit a MIR-compatibility native verification bundle: function {function} has \
         producer {producer:?}, expected Producer::TrustIr"
    )]
    NonMirCompatibilityProducer { function: FuncId, producer: Option<Producer> },
    #[error("native verification request planning produced no request variants")]
    EmptyRequests,
    #[error("cannot emit a native verification bundle without an owning function")]
    EmptyOwners,
    #[error("native verification bundle owner {0} is listed more than once")]
    DuplicateOwner(FuncId),
    #[error("native verification bundle validation failed")]
    Validation(Vec<NativeVerificationBundleError>),
    /// A module certificate arrived with `ProofCertificate::assurance`
    /// (trust-ir v41) already recorded. See the COVERAGE ASSURANCE section of
    /// [`native_verification_bundle_from_module_owners`]: a row must cite a
    /// request of the bundle it travels in, those requests are minted here, and
    /// each one binds the module digest the row itself feeds, so a row present
    /// on entry cites a request of some OTHER bundle. Refused by name here
    /// rather than shipped for trust-ir-build to refuse later as
    /// `CoverageAssuranceRequestUnknown`.
    #[error(
        "native proof certificate for obligation {obligation} carries a coverage assurance \
         recorded before this bundle's requests existed; a coverage row must cite a request \
         of the bundle it travels in, and none can be cited from outside it"
    )]
    PreRecordedCoverageAssurance { obligation: ProofId },
}

/// One body whose proof obligations a native verification bundle may carry.
///
/// Index 0 of an owner slice is the ROOT: the bundle subject, whose
/// `source_digest` becomes the bundle-level `provenance.source_digest` and the
/// [`NativeAdapterInput::RustMir`] body digest. Every other entry is a MEMBER —
/// a body the callee closure bundled into the same module.
///
/// `source_digest` attests **which** body was lowered. It never attests **that**
/// the body passed: no verdict crosses this boundary in either direction, and
/// the gate that decides a verdict re-runs locally and mints its own token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeBundleOwner {
    /// The lowered TrustIr body this owner names.
    pub function: FuncId,
    /// SHA-256 identity of the exact compiler source artifact it was lowered
    /// from. Authority-bearing, so a non-cryptographic algorithm fails closed.
    pub source_digest: ProofDigest,
}

/// Build the MIR-compatibility bridge's typed native request bundle for one
/// lowered TrustIr module/function pair.
///
/// The input remains explicitly [`NativeAdapterInput::RustMir`], while the
/// producer is [`NativeBundleProducer::TrustIr`]: the former identifies the
/// backing source artifact and the latter identifies the component that
/// performed this retained compatibility lowering. Direct THIR/source lowering
/// is the distinct `TRust` producer. The planner keeps the TrustIr module and
/// proof lineage in one typed envelope. Its authority digest is derived from
/// the completed module's canonical serialization inside this boundary; callers
/// cannot inject a digest for different contents. The caller-supplied source
/// identity must also use SHA-256; legacy stable labels are readable elsewhere
/// for compatibility diagnostics but cannot authorize native proof reuse. The
/// planner then emits request variants for the current ownership split:
///
/// - TrustVc owns memory-safety and refinement certificate import/merge work.
/// - TrustMc owns body-aware contract/loop/termination and reachability work.
/// - TrustWp receives a body-aware alternative for each postcondition. A
///   formula-less structural give-back record still carries no proof authority.
///
/// This planner does not manufacture solver-result evidence. It emits one
/// narrow TrustVc import-evidence row only when every certificate in that
/// request is a typed `CleanCic` certificate. Bundle validation then replays
/// each exact certificate in-process; an opaque `LeanProof`, public
/// `Discharged` label, or mixed certificate request can never cross this
/// boundary as evidence.
///
/// See [`native_verification_bundle_from_module_owners`] for why every
/// certificate it carries leaves with `assurance: None` (NOT RECORDED).
pub fn native_verification_bundle_from_module(
    module: Module,
    source_digest: ProofDigest,
    function: FuncId,
) -> Result<NativeVerificationBundle, NativeVerificationBundleBuildError> {
    native_verification_bundle_from_module_owners(
        module,
        &[NativeBundleOwner { function, source_digest }],
    )
}

/// [`native_verification_bundle_from_module`] over SEVERAL owning bodies.
///
/// The single-owner entry point above is the whole of today's behaviour and
/// delegates here; with one owner this planner is byte-identical to the one it
/// replaces. The multi-owner shape exists so that a module which carries a
/// bundled MEMBER's obligations can produce a well-formed bundle at all —
/// nothing here generates or discharges a member obligation.
///
/// What becomes per-owner: the monomorphization fact each obligation source
/// cites, the lineage node that attests which body was lowered, and the request
/// `function` / replay-transcript digest. What stays root-scoped: the bundle's
/// own `provenance.source_digest` and adapter input, which name the SUBJECT.
///
/// # Coverage assurance (trust-ir v41 `ProofCertificate::assurance`)
///
/// A coverage row is recorded exactly when trust-ir-build's establishing
/// criterion holds for the request it cites (`coverage_assurance_report`,
/// admitting on `is_checked() && errors().is_empty() && undetermined() == 0`):
/// the cited request is in this bundle, lists the certificate's obligation,
/// fixes a bound from its own fields, and no sibling over the obligation fixes
/// a shorter one. For every certificate this planner carries the criterion
/// does NOT hold, so every row leaves as `None` — NOT RECORDED, which a
/// fail-closed consumer reads as unknown coverage, never as unbounded:
///
/// * a certificate rides the TrustVc `ImportProofCertificates` request of its
///   owner (a `CleanCic` one regardless of kind), and trust-ir-build fixes NO
///   bound for any TrustVc mode — the import's coverage is whatever the
///   imported certificate established, not a field of the request. Recording
///   `Unbounded` there is the over-claim trust-ir-build calls the unsound
///   direction (pinned by test against `coverage_assurance_report` itself);
/// * the TrustMc `Chc` requests minted here are PENDING solve requests. A
///   certificate the module already carries did not come from one of them,
///   so citing one would state a provenance that is false, and a `CleanCic`
///   obligation is excluded from them anyway;
/// * no row can be recorded here even where a bound were established: every
///   request binds `trust_ir_module_digest` through its replay-transcript
///   digest, and that module digest covers the row's own `request_digest`.
///   A row citing a request of the same bundle is a digest cycle.
///
/// For the same reason a certificate that ARRIVES with a row recorded is
/// refused ([`NativeVerificationBundleBuildError::PreRecordedCoverageAssurance`]):
/// whatever request it cites is not one of the requests minted below.
pub fn native_verification_bundle_from_module_owners(
    module: Module,
    owners: &[NativeBundleOwner],
) -> Result<NativeVerificationBundle, NativeVerificationBundleBuildError> {
    let Some(&root_owner) = owners.first() else {
        return Err(NativeVerificationBundleBuildError::EmptyOwners);
    };
    let function = root_owner.function;
    let source_digest = root_owner.source_digest;

    if module.functions.is_empty() {
        return Err(NativeVerificationBundleBuildError::EmptyModule);
    }
    if module.function_by_id(function).is_none() {
        return Err(NativeVerificationBundleBuildError::MissingFunction(function));
    }
    if module.proof_obligations.is_empty() {
        return Err(NativeVerificationBundleBuildError::EmptyObligations);
    }
    if source_digest.algorithm != ProofDigestAlgorithm::Sha256 {
        return Err(NativeVerificationBundleBuildError::NonAuthoritativeSourceDigest {
            algorithm: source_digest.algorithm,
        });
    }
    // Members are admitted AFTER the root's four checks, in owner order, so a
    // single-owner bundle reports exactly the errors it always did, in exactly
    // the order it always did.
    let mut owner_indices: BTreeMap<FuncId, usize> = BTreeMap::new();
    owner_indices.insert(function, 0);
    for (index, owner) in owners.iter().enumerate().skip(1) {
        if module.function_by_id(owner.function).is_none() {
            return Err(NativeVerificationBundleBuildError::MissingFunction(owner.function));
        }
        if owner.source_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            return Err(NativeVerificationBundleBuildError::NonAuthoritativeSourceDigest {
                algorithm: owner.source_digest.algorithm,
            });
        }
        if owner_indices.insert(owner.function, index).is_some() {
            return Err(NativeVerificationBundleBuildError::DuplicateOwner(owner.function));
        }
    }
    require_mir_compatibility_producers(&module, function)?;
    if let Some(certificate) =
        module.proof_certificates.iter().find(|certificate| certificate.assurance.is_some())
    {
        return Err(NativeVerificationBundleBuildError::PreRecordedCoverageAssurance {
            obligation: certificate.obligation,
        });
    }
    require_native_module_binary_identity(&module)
        .map_err(NativeVerificationBundleBuildError::ModuleBinaryIdentity)?;
    let trust_ir_module_digest = module.stable_digest();
    if trust_ir_module_digest.algorithm != ProofDigestAlgorithm::Sha256 {
        return Err(NativeVerificationBundleBuildError::NonAuthoritativeModuleDigest {
            algorithm: trust_ir_module_digest.algorithm,
        });
    }

    // Compiler facts are built BEFORE the module moves into the bundle, so the
    // lineage partition below can reuse the same owner resolution. The hoist
    // cannot change which error a malformed module reports: everything between
    // here and bundle construction is infallible, and
    // `obligation_sources_for_owners` runs the per-row source / public-identity
    // / owner checks in the order the single-owner planner always ran them.
    let mut compiler_facts = NativeCompilerFacts::default();
    let owner_functions: Vec<FuncId> = owners.iter().map(|owner| owner.function).collect();
    populate_compiler_facts_for_owners(
        &mut compiler_facts,
        &module,
        &owner_functions,
        &owner_indices,
        function,
        trust_ir_module_digest,
    )?;

    let lineage =
        native_lineage_for_owners(&module, owners, &owner_indices, trust_ir_module_digest);
    // Every request names this one root. With a single owner it IS the single
    // lowering node, unchanged; with several it is the composition join, which
    // is the only node whose closure reaches every owner's obligations AND the
    // bundle source digest that `source_bound_lineage_membership` binds through.
    let lineage_root = *lineage.roots.first().expect("owner list is non-empty");
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        trust_ir_module_digest,
        module,
        lineage,
    );
    bundle.provenance.producer_version = TRUST_NATIVE_REQUEST_COMPILER_VERSION.to_string();
    bundle.provenance.source_language = NativeSourceLanguage::Rust;
    // Rust is the backing source; the admitted function tags describe the
    // retained TrustIr MIR bridge. Do not infer extra languages from imports:
    // upstream bundle validation must refuse any uncovered dependency tag.
    bundle.provenance.source_languages =
        BTreeSet::from([NativeSourceLanguage::Rust, NativeSourceLanguage::TrustIr]);
    bundle.provenance.source_digest = Some(source_digest);
    bundle.provenance.toolchain = vec![trust_ir_bridge_tool_identity()];
    bundle.compiler_facts = compiler_facts;

    // Trust (kernel-replay routing): an obligation whose module certificate is
    // CleanCic is ALREADY kernel-proved — route it to the trust_vc
    // certificate-import request (whose validation replays the certificate
    // in-process under trust-ir's clean-expr authority) regardless of kind,
    // and exclude it from the trust_mc solve lane so a native
    // engine is never asked to re-derive a kernel-checked proof. Kind-based
    // ownership is unchanged for everything else, keeping request-id order
    // (trust_vc, then trust_mc) stable.
    // Hoisted out of the per-owner loop below, and out of the closure it used
    // to be: the answer is a property of the module, not of an owner, and
    // materializing it keeps the loop from holding a borrow of `bundle.module`
    // across the pushes into `bundle.requests`.
    let clean_cic_obligations = bundle
        .module
        .proof_certificates
        .iter()
        .filter(|certificate| {
            matches!(certificate.evidence, trust_ir::ProofEvidence::CleanCic { .. })
        })
        .map(|certificate| certificate.obligation)
        .collect::<BTreeSet<_>>();
    let mut next_request_id = 0;
    // Owner-major, and within an owner trust_vc before trust_mc — the order a
    // single-owner module has always produced, extended outward rather than
    // interleaved, so request ids stay stable for the subject.
    for owner in owners {
        let owned_by =
            |obligation: &trust_ir::ProofObligation| obligation.function == Some(owner.function);
        let trust_vc_obligations = request_obligations(&bundle.module, |obligation| {
            owned_by(obligation)
                && (trust_vc_owns_obligation(&obligation.kind)
                    || clean_cic_obligations.contains(&obligation.id))
        });
        let trust_mc_obligations = request_obligations(&bundle.module, |obligation| {
            owned_by(obligation)
                && trust_mc_owns_obligation(&obligation.kind)
                && !clean_cic_obligations.contains(&obligation.id)
        });
        if !trust_vc_obligations.is_empty() {
            let trust_vc_set = trust_vc_obligations.iter().copied().collect::<BTreeSet<_>>();
            let certificates = bundle
                .module
                .proof_certificates
                .iter()
                .filter(|certificate| trust_vc_set.contains(&certificate.obligation))
                .map(ProofCertificate::lineage_ref)
                .collect();
            let provenance = trust_vc_request_provenance(
                &bundle.module,
                &bundle.compiler_facts,
                owner.source_digest,
                trust_ir_module_digest,
                &trust_vc_obligations,
            );
            let request_id = NativeRequestId::new(next_request_id);
            let request = TrustVcNativeRequest {
                id: request_id,
                mode: TrustVcVerificationMode::ImportProofCertificates,
                obligations: trust_vc_obligations,
                certificates,
                lineage_roots: vec![lineage_root],
                options: TrustVcRequestOptions::default(),
                diagnostics: NativeDiagnosticsPolicy::default(),
                provenance,
                // Correct BY CONSTRUCTION, not by convention. Every obligation
                // in this module resolves to one of `owners` in
                // `obligation_sources_for_owners`, which returns
                // ObligationFunctionMismatch and aborts the builder otherwise;
                // this set is then filtered by `owned_by`, so it holds exactly
                // this owner's rows. That is the equality the bundle validator
                // re-checks per request as RequestObligationFunctionMismatch.
                function: Some(owner.function),
            };
            let evidence_bundle =
                trust_vc_request_has_only_clean_cic_certificates(&bundle.module, &request).then(
                    || trust_vc_evidence_bundle_for_request(&request, trust_ir_module_digest),
                );
            bundle.requests.push(NativeVerificationRequest::TrustVc(request));
            if let Some(evidence_bundle) = evidence_bundle {
                bundle.evidence_bundles.push(NativeEvidenceBundle::TrustVc(evidence_bundle));
            }
            next_request_id += 1;
        }
        for trust_mc_obligation in trust_mc_obligations {
            let trust_mc_obligations = vec![trust_mc_obligation];
            let provenance = trust_mc_request_provenance(
                &bundle.module,
                &bundle.compiler_facts,
                owner.source_digest,
                trust_ir_module_digest,
                &trust_mc_obligations,
            );
            bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
                id: NativeRequestId::new(next_request_id),
                mode: TrustMcVerificationMode::Chc,
                function: owner.function,
                obligations: trust_mc_obligations,
                lineage_roots: vec![lineage_root],
                options: trust_mc_chc_request_options(),
                diagnostics: NativeDiagnosticsPolicy::default(),
                provenance,
            }));
            next_request_id += 1;
        }
    }
    // Alternative proof strategies share the exact module, public obligation
    // and source binding. Append after every primary request so their stable
    // ids and the primary ownership table are unchanged.
    for owner in owners {
        for obligation in request_obligations(&bundle.module, |obligation| {
            obligation.function == Some(owner.function)
                && obligation.kind == ObligationKind::Postcondition
                && !clean_cic_obligations.contains(&obligation.id)
        }) {
            let obligations = vec![obligation];
            bundle.requests.push(native_wp_request(
                NativeRequestId::new(next_request_id),
                owner.function,
                obligation,
                lineage_root,
                ProofReplayIdentity::new("trust_wp", "replay_trust_ir_body_contracts")
                    .with_transcript_digest(native_replay_transcript_digest(
                        "trust_wp",
                        owner.source_digest,
                        trust_ir_module_digest,
                        &obligations,
                    )),
            ));
            next_request_id += 1;
        }
    }
    if bundle.requests.is_empty() {
        return Err(NativeVerificationBundleBuildError::EmptyRequests);
    }
    bundle.validate().map_err(NativeVerificationBundleBuildError::Validation)?;
    // TRUSTED LIVE SEAM (b62 merge migration): the old direct mark-live bundle
    // flag (deliberately not spelled here: trust-bmc's
    // `root_source_authority_issuer_is_unique_and_legacy_marker_is_absent`
    // census greps the tree, comments included, to prove the forgeable legacy
    // marker is GONE) was superseded by trust-ir
    // main's strictly stronger `SourceGenerationAuthority::mint_from_live_lowering`
    // (private Arc-nonce identity, one-shot validated mint, full-bundle-digest
    // binding). The builder therefore returns the bundle UNMARKED; the compiler's
    // authorized seam mints the affine authority from the live bundle itself, and
    // a deserialized copy can never be authorized (fail-closed direction kept).
    Ok(bundle)
}

/// Assemble the same single-question WP request for either input provenance.
/// The caller supplies its own truthful replay identity: direct diagnostic
/// requests must not invent a MIR source digest or source authority.
pub(super) fn native_wp_request(
    id: NativeRequestId,
    function: FuncId,
    obligation: ProofId,
    lineage_root: ProofLineageId,
    replay: ProofReplayIdentity,
) -> NativeVerificationRequest {
    let provenance = NativeRequestProvenance::trust_wp(
        NativeToolIdentity::new("trust_wp")
            .with_version("trust-wp-trust-ir-body-wp-v1")
            .with_revision(TRUST_NATIVE_REQUEST_TRANSFORM_VERSION),
    )
    .with_solver(
        NativeToolIdentity::new("trust-wp-core.native-pure-replay")
            .with_version("trust_wp.native-pure-replay.v1"),
    )
    .with_replay(replay);
    NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id,
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function,
        obligations: vec![obligation],
        lineage_roots: vec![lineage_root],
        options: TrustWpRequestOptions::default(),
        diagnostics: NativeDiagnosticsPolicy::default(),
        provenance,
    })
}

/// Require positive MIR-compatibility provenance before relabeling a module as
/// [`NativeAdapterInput::RustMir`] / [`NativeBundleProducer::TrustIr`].
///
/// TrustIr records producer provenance per function rather than per module.
/// This planner inventories module-wide obligations, so checking only the
/// selected target would still let a mixed direct/MIR module cross the boundary
/// under a single MIR label. Check the target first for an actionable error,
/// then every other function. Missing provenance also fails closed: this bridge
/// cannot infer that an unlabelled function came from the retained MIR path.
fn require_mir_compatibility_producers(
    module: &Module,
    target: FuncId,
) -> Result<(), NativeVerificationBundleBuildError> {
    let target_function = module
        .function_by_id(target)
        .ok_or(NativeVerificationBundleBuildError::MissingFunction(target))?;

    for function in std::iter::once(target_function)
        .chain(module.functions.iter().filter(|function| function.id != target))
    {
        if function.producer.as_ref() != Some(&Producer::TrustIr) {
            return Err(NativeVerificationBundleBuildError::NonMirCompatibilityProducer {
                function: function.id,
                producer: function.producer.clone(),
            });
        }
    }

    Ok(())
}

/// Admit the exact module to its existing binary identity without deriving a
/// second digest or dropping claims. Adaptive Raw accepts every lossless wire
/// version; the default RawV38 would reject already-supported v39-v46 content.
pub(super) fn require_native_module_binary_identity(
    module: &Module,
) -> Result<(), BinaryProjectionError> {
    ProjectedModuleBinaryPlan::try_new(
        module,
        ModuleBinaryOptions {
            body: ModuleBinaryBody::Raw,
            symbols: ModuleSymbolProjection::Exact,
            obligations: ModuleObligationRows::All,
        },
    )
    .map(|_| ())
}

fn trust_ir_bridge_tool_identity() -> NativeToolIdentity {
    NativeToolIdentity::new("TrustIr")
        .with_version(TRUST_NATIVE_REQUEST_COMPILER_VERSION)
        .with_revision(TRUST_NATIVE_REQUEST_COMPILER_REVISION)
}

/// The per-owner lineage manifest.
///
/// One [`ProofTransformStage::TrustIrLowering`] node per owning body, each
/// attesting the source digest of the body it actually lowered. That is the
/// whole point of making this per-owner: a single root node can only ever say
/// which body the SUBJECT came from, so a member's obligations would ride on an
/// attestation of a different body's bytes.
///
/// The multi-owner shape is forced, not chosen. Per-body lowerings are
/// PARALLEL — different sources, one target module — so they cannot be linked
/// with `depends_on`, whose shape rule (`ProofLineageManifest::validate_shape`)
/// requires a dependency's `target_module` to equal the dependent's own
/// `source_module`. `Composition` is the one stage that rule exempts, and it is
/// the honest label for a join. It is also what preserves request binding: the
/// bundle validator admits a request's obligations only through a lineage root
/// whose closure contains the bundle's own source digest
/// (`source_bound_lineage_membership`), and the join's closure contains every
/// owner's node, hence the root owner's digest.
///
/// With ONE owner no join is emitted and this is exactly the single node, single
/// root, all-obligations, all-certificates manifest that shipped before.
#[inline]
fn obligation_by_id(module: &Module, id: ProofId) -> Option<&trust_ir::ProofObligation> {
    let idx = id.index() as usize;
    module
        .proof_obligations
        .get(idx)
        .filter(|obligation| obligation.id == id)
        .or_else(|| module.proof_obligations.iter().find(|obligation| obligation.id == id))
}

fn native_lineage_for_owners(
    module: &Module,
    owners: &[NativeBundleOwner],
    owner_indices: &BTreeMap<FuncId, usize>,
    trust_ir_module_digest: ProofDigest,
) -> ProofLineageManifest {
    // An obligation reaching here has already resolved to an owner in
    // `obligation_sources_for_owners`; the `unwrap_or(0)` is unreachable and
    // keeps an unowned row on the ROOT node, which is where it sat before —
    // so a module that would have failed node-shape validation still fails it
    // the same way instead of silently landing somewhere new.
    let owner_of = |function: Option<FuncId>| {
        function.and_then(|function| owner_indices.get(&function).copied()).unwrap_or(0)
    };
    let mut per_owner_obligations: Vec<Vec<ProofId>> = vec![Vec::new(); owners.len()];
    let mut all_obligations: Vec<ProofId> = Vec::with_capacity(module.proof_obligations.len());
    for obligation in &module.proof_obligations {
        all_obligations.push(obligation.id);
        per_owner_obligations[owner_of(obligation.function)].push(obligation.id);
    }

    let obligation_owner = |id: ProofId| {
        owner_of(obligation_by_id(module, id).and_then(|obligation| obligation.function))
    };
    let mut per_owner_certificates = vec![Vec::new(); owners.len()];
    let mut all_certificates = Vec::with_capacity(module.proof_certificates.len());
    for certificate in &module.proof_certificates {
        let reference = ProofCertificate::lineage_ref(certificate);
        all_certificates.push(reference.clone());
        per_owner_certificates[obligation_owner(certificate.obligation)].push(reference);
    }

    let mut nodes = Vec::with_capacity(owners.len() + 1);
    for (index, owner) in owners.iter().enumerate() {
        let mut node = ProofLineageNode::new(
            ProofLineageId::new(index as u32),
            ProofTransform::new(
                ProofTransformStage::TrustIrLowering,
                "rustc-mir-to-trust_ir",
                "TrustIr",
                TRUST_NATIVE_REQUEST_TRANSFORM_VERSION,
            ),
            owner.source_digest,
            trust_ir_module_digest,
        );
        node.obligations = std::mem::take(&mut per_owner_obligations[index]);
        node.certificates = std::mem::take(&mut per_owner_certificates[index]);
        node.replay = Some(trust_mc_native_admission_replay_identity(
            owner.source_digest,
            trust_ir_module_digest,
            &node.obligations,
        ));
        nodes.push(node);
    }

    if owners.len() == 1 {
        let root = nodes[0].id;
        return ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes,
            roots: vec![root],
        };
    }

    let join = ProofLineageId::new(owners.len() as u32);
    let mut join_node = ProofLineageNode::new(
        join,
        ProofTransform::new(
            ProofTransformStage::Composition,
            "trust_ir-multi-body-bundle-composition",
            "TrustIr",
            TRUST_NATIVE_REQUEST_TRANSFORM_VERSION,
        ),
        trust_ir_module_digest,
        trust_ir_module_digest,
    );
    join_node.depends_on = nodes.iter().map(|node| node.id).collect();
    join_node.obligations = all_obligations;
    join_node.certificates = all_certificates;
    join_node.replay = Some(trust_mc_native_admission_replay_identity(
        // The SUBJECT's digest: this node's replay identity is about the bundle
        // as a whole, and the bundle's subject is owner 0. Each member's own
        // digest is attested by its own node, above.
        owners[0].source_digest,
        trust_ir_module_digest,
        &join_node.obligations,
    ));
    nodes.push(join_node);
    ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes,
        roots: vec![join],
    }
}

/// Single-owner [`populate_compiler_facts_for_owners`], retained for the
/// planner's own provenance fixtures.
#[cfg(test)]
fn populate_compiler_facts_for_module(
    compiler_facts: &mut NativeCompilerFacts,
    module: &Module,
    function: FuncId,
    trust_ir_module_digest: ProofDigest,
) -> Result<(), NativeVerificationBundleBuildError> {
    let mut owner_indices = BTreeMap::new();
    owner_indices.insert(function, 0);
    populate_compiler_facts_for_owners(
        compiler_facts,
        module,
        &[function],
        &owner_indices,
        function,
        trust_ir_module_digest,
    )
}

fn populate_compiler_facts_for_owners(
    compiler_facts: &mut NativeCompilerFacts,
    module: &Module,
    owner_functions: &[FuncId],
    owner_indices: &BTreeMap<FuncId, usize>,
    root: FuncId,
    trust_ir_module_digest: ProofDigest,
) -> Result<(), NativeVerificationBundleBuildError> {
    // One monomorphization fact per OWNING body. `validate_compiler_facts`
    // already admits several; what it requires of each is a distinct id, a
    // distinct non-zero SHA-256 `stable_digest`, a distinct `symbol`, and a
    // `function` the module declares. `native_monomorphization_digest` frames
    // the owner's `FuncId`, so two owners cannot collide on the digest; the
    // symbol is the module-unique function name.
    compiler_facts.monomorphizations = owner_functions
        .iter()
        .enumerate()
        .map(|(index, function)| {
            native_monomorphization_fact(
                module,
                *function,
                NativeMonomorphizationId::new(index as u32),
                trust_ir_module_digest,
            )
        })
        .collect();
    compiler_facts.obligation_sources = obligation_sources_for_owners(module, owner_indices, root)?;
    Ok(())
}

pub(crate) fn native_monomorphization_fact(
    module: &Module,
    function: FuncId,
    id: NativeMonomorphizationId,
    trust_ir_module_digest: ProofDigest,
) -> NativeMonomorphizationFact {
    let source_item = module
        .function_by_id(function)
        .map(|function| function.name.clone())
        .unwrap_or_else(|| format!("function#{}", function.index()));
    NativeMonomorphizationFact {
        id,
        source_item: source_item.clone(),
        symbol: source_item.clone(),
        // This compatibility bridge receives an already-monomorphized TrustIr
        // function and has no authoritative generic-argument spellings to
        // retain. Do not reconstruct them from the symbol. The stable digest
        // below commits the exact typed module instead, so two erased generic
        // instantiations cannot share authority unless their canonical TrustIr
        // identity is actually equal.
        generic_args: Vec::new(),
        function: Some(function),
        stable_digest: native_monomorphization_digest(
            trust_ir_module_digest,
            &module.name,
            function,
            &source_item,
        ),
    }
}

fn native_monomorphization_digest(
    trust_ir_module_digest: ProofDigest,
    module_name: &str,
    function: FuncId,
    source_item: &str,
) -> ProofDigest {
    let mut bytes = Vec::new();
    append_digest_material(&mut bytes, trust_ir_module_digest);
    append_len_prefixed_bytes(&mut bytes, module_name.as_bytes());
    bytes.extend_from_slice(&function.index().to_be_bytes());
    append_len_prefixed_bytes(&mut bytes, source_item.as_bytes());
    ProofDigest::sha256_domain("trust.native-request.monomorphization.v2", &bytes)
}

pub(crate) fn obligation_sources_for_owners(
    module: &Module,
    owner_indices: &BTreeMap<FuncId, usize>,
    root: FuncId,
) -> Result<Vec<NativeObligationSource>, NativeVerificationBundleBuildError> {
    module
        .proof_obligations
        .iter()
        .map(|obligation| {
            let source = obligation.source.as_ref().ok_or(
                NativeVerificationBundleBuildError::MissingObligationSource(obligation.id),
            )?;
            let public = source.public.as_ref().ok_or(
                NativeVerificationBundleBuildError::MissingPublicObligationIdentity(obligation.id),
            )?;
            // The owner is a LOOKUP, not the root by assumption — but it is
            // still fail-closed: a row naming a body this bundle does not own
            // aborts the builder. With a single owner that lookup succeeds on
            // exactly the rows the old `!= Some(root)` equality admitted, and
            // fails on exactly the rows it rejected.
            let Some(owner_index) =
                obligation.function.and_then(|function| owner_indices.get(&function).copied())
            else {
                return Err(NativeVerificationBundleBuildError::ObligationFunctionMismatch {
                    obligation: obligation.id,
                    expected: root,
                    actual: obligation.function,
                });
            };
            let monomorphization = NativeMonomorphizationId::new(owner_index as u32);
            Ok(NativeObligationSource {
                obligation: obligation.id,
                public_obligation_id: public.obligation_id.clone(),
                function: obligation.function,
                // This `trust_ir::SourceSpan` carries OBLIGATION-IDENTITY coordinates, not
                // debug info: `range` is the raw LO edge of a `ProofObligationSourceRange`,
                // fed from `trust_types::SourceSpan` by `lower.rs::ObligationSourceMetadata::
                // to_proof_source_identity` (NOT callsite-rebased — the same type on
                // `InstrNode.span` IS callsite-rebased; the lane is a property of the
                // producer, not the type). trust-wp's verifier_api equality-compares this
                // projection against the embedded source, so it must stay verbatim.
                span: source.range.map(|range| SourceSpan {
                    file: range.file,
                    line: range.start_line,
                    col: range.start_col,
                }),
                assertion_id: Some(NativeAssertionId::new(trust_types::stable_u32_id(
                    source.assertion_id.as_bytes(),
                ))),
                cause: native_obligation_cause(&obligation.kind),
                monomorphization: Some(monomorphization),
                facts: vec![NativeCompilerFactRef::Monomorphization(monomorphization)],
            })
        })
        .collect()
}

pub(crate) fn native_obligation_cause(kind: &ObligationKind) -> NativeObligationCause {
    match kind {
        ObligationKind::Precondition => NativeObligationCause::Precondition,
        ObligationKind::Postcondition => NativeObligationCause::Postcondition,
        ObligationKind::LoopInvariant => NativeObligationCause::Assert,
        ObligationKind::TypeInvariant | ObligationKind::RefinementType => {
            NativeObligationCause::Assert
        }
        ObligationKind::MemorySafety => NativeObligationCause::BorrowCheck,
        ObligationKind::GiveBackRefinement => NativeObligationCause::BorrowCheck,
        ObligationKind::TranslationValidation => NativeObligationCause::Translation,
        // Trust (trust-ir-spine item T1): the new routing-grade panic-class
        // kinds are panic-freedom obligations — route them exactly like
        // `PanicFreedom` to preserve current dispatch behavior.
        ObligationKind::PanicFreedom
        | ObligationKind::ArithmeticSafety
        | ObligationKind::BoundsCheck => NativeObligationCause::Panic,
        ObligationKind::TemporalSafety | ObligationKind::Liveness => {
            NativeObligationCause::Temporal
        }
        // `ObligationKind` is `#[non_exhaustive]`; an unknown future kind is
        // conservatively treated as a generic panic-class obligation.
        _ => NativeObligationCause::Panic,
    }
}

fn trust_vc_request_provenance(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    source_digest: ProofDigest,
    trust_ir_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> NativeRequestProvenance {
    NativeRequestProvenance::trust_vc(
        NativeToolIdentity::new("trust_vc")
            .with_version(TRUST_VC_NATIVE_REQUEST_INTERFACE_VERSION)
            .with_revision(TRUST_VC_NATIVE_REQUEST_INTERFACE_REVISION),
    )
    .with_solver(
        NativeToolIdentity::new("lean4")
            .with_version(TRUST_VC_LEAN_SOLVER_INTERFACE_VERSION)
            .with_revision(TRUST_VC_NATIVE_REQUEST_INTERFACE_REVISION),
    )
    .with_replay(
        ProofReplayIdentity::new("trust_vc", "trust_vc-trust-engine admit-native-proof-artifacts")
            .with_transcript_digest(native_replay_transcript_digest(
                "trust_vc",
                source_digest,
                trust_ir_module_digest,
                obligations,
            )),
    )
    .with_replay_context(native_replay_context(module, compiler_facts, obligations))
}

/// Declare the native whole-function safety encoding and native PDR execution.
/// Keep this explicit: the wire defaults also describe backends and transforms
/// that this producer does not request or supply.
pub fn trust_mc_chc_request_options() -> TrustMcRequestOptions {
    TrustMcRequestOptions {
        memory_model: TrustMcMemoryModel::TrustIrPlaces,
        arithmetic_model: TrustMcArithmeticModel::FixedWidthBitvectors,
        // Inactive on CHC/PDR requests; this does not claim cyclic BMC support.
        bmc: TrustMcBmcOptions { unwind_limit: 1, unwinding_assertions: true },
        chc: TrustMcChcOptions {
            engine: TrustMcChcEngine::NativePdr,
            // Solver-internal candidate discovery is not an imported invariant.
            invariant_source: TrustMcInvariantSource::None,
            pdr: TrustMcPdrOptions {
                enabled: true,
                max_frames: None,
                generalization: TrustMcPdrGeneralization::Cubes,
            },
            emit_horn_clauses: true,
        },
        slicing: TrustMcSlicingMode::None,
    }
}

fn trust_mc_request_provenance(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    source_digest: ProofDigest,
    trust_ir_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> NativeRequestProvenance {
    NativeRequestProvenance::trust_mc(
        NativeToolIdentity::new("trust_mc")
            .with_version(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
            .with_revision(TRUST_NATIVE_REQUEST_TRANSFORM_VERSION),
    )
    .with_solver(NativeToolIdentity::new("ay"))
    .with_replay(
        ProofReplayIdentity::new(
            "trust_mc",
            format!(
                "trust_mc-driver native-bundle --mode chc --trust-native-admission-contract {}",
                TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
            ),
        )
        .with_transcript_digest(native_replay_transcript_digest(
            "trust_mc",
            source_digest,
            trust_ir_module_digest,
            obligations,
        )),
    )
    .with_replay_context(trust_mc_native_replay_context(module, compiler_facts, obligations))
}

fn trust_mc_native_admission_replay_identity(
    source_digest: ProofDigest,
    trust_ir_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> ProofReplayIdentity {
    ProofReplayIdentity::new(
        "Trust.native-admission",
        format!(
            "trust-ir-bridge emit-native-verification-bundle --trust_mc-admission-contract {}",
            TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
        ),
    )
    .with_transcript_digest(native_replay_transcript_digest(
        "trust-mc-native-admission",
        source_digest,
        trust_ir_module_digest,
        obligations,
    ))
}

pub(crate) fn native_replay_context(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    obligations: &[ProofId],
) -> NativeReplayContext {
    let mut context = NativeReplayContext::default();
    for (index, obligation_id) in obligations.iter().enumerate() {
        let Some(obligation) = obligation_by_id(module, *obligation_id) else {
            continue;
        };
        let Some(formula) = obligation.formula.clone() else {
            continue;
        };
        if formula.schema.trim().is_empty() || formula.payload.trim().is_empty() {
            continue;
        }

        let mut atom = NativeReplayAtom::assertion(NativeReplayAtomId::new(index as u32), formula)
            .with_obligation(*obligation_id);
        if let Some(source) = compiler_facts.obligation_source(*obligation_id) {
            if let Some(assertion_id) = source.assertion_id {
                atom = atom.with_assertion_id(assertion_id);
            }
            if let Some(span) = source.span {
                atom = atom.with_span(span);
            }
        }
        context = context.with_atom(atom);
    }
    context
}

fn trust_mc_native_replay_context(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    obligations: &[ProofId],
) -> NativeReplayContext {
    let mut context = native_replay_context(module, compiler_facts, obligations);
    for obligation_id in obligations {
        let Some(obligation) = obligation_by_id(module, *obligation_id) else {
            continue;
        };
        if let Some(unsupported) = trust_mc_unsupported_semantics_mode(obligation) {
            context = context.with_unsupported_mode(unsupported);
        }
    }
    context
}

#[derive(serde::Deserialize)]
struct NativeAdmissionPayload {
    unsupported_semantics_status: Option<String>,
    status: Option<String>,
    detail: Option<String>,
}

#[derive(serde::Deserialize)]
struct NativeAdmissionEnvelope {
    trust_native_admission: Option<NativeAdmissionPayload>,
}

fn trust_mc_unsupported_semantics_mode(
    obligation: &trust_ir::ProofObligation,
) -> Option<NativeUnsupportedMode> {
    let formula = obligation.formula.as_ref()?;
    let payload = formula.payload.as_str();
    if !payload.contains("trust_native_admission") && !payload.contains("\\u") {
        return None;
    }
    if let Ok(envelope) = serde_json::from_str::<NativeAdmissionEnvelope>(payload) {
        let admission = envelope.trust_native_admission?;
        let status =
            admission.unsupported_semantics_status.as_deref().or(admission.status.as_deref())?;
        if status != "unsupported" && status != "unsupported_semantics" {
            return None;
        }
        let detail = admission
            .detail
            .as_deref()
            .filter(|detail| !detail.trim().is_empty())
            .unwrap_or("TrustMc native admission contract marked unsupported semantics");
        return Some(NativeUnsupportedMode::new(
            NativeUnsupportedModeReason::UnsupportedVerifierMode,
            format!("{}: {}", TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION, detail),
        ));
    }
    let value: serde_json::Value = serde_json::from_str(payload).ok()?;
    let admission = value.get("trust_native_admission")?;
    let status = admission
        .get("unsupported_semantics_status")
        .or_else(|| admission.get("status"))
        .and_then(serde_json::Value::as_str)?;
    if status != "unsupported" && status != "unsupported_semantics" {
        return None;
    }
    let detail = admission
        .get("detail")
        .and_then(serde_json::Value::as_str)
        .filter(|detail| !detail.trim().is_empty())
        .unwrap_or("TrustMc native admission contract marked unsupported semantics");
    Some(NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::UnsupportedVerifierMode,
        format!("{}: {}", TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION, detail),
    ))
}

fn native_replay_transcript_digest(
    verifier_suite: &str,
    source_digest: ProofDigest,
    trust_ir_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> ProofDigest {
    let mut bytes = Vec::new();
    append_len_prefixed_bytes(&mut bytes, verifier_suite.as_bytes());
    append_digest_material(&mut bytes, source_digest);
    append_digest_material(&mut bytes, trust_ir_module_digest);
    bytes.extend_from_slice(
        &u64::try_from(obligations.len())
            .expect("native replay obligation count exceeds canonical u64 framing")
            .to_be_bytes(),
    );
    for obligation in obligations {
        bytes.extend_from_slice(&obligation.index().to_be_bytes());
    }
    ProofDigest::sha256_domain("trust.native-request.replay-transcript.v2", &bytes)
}

fn append_digest_material(bytes: &mut Vec<u8>, digest: ProofDigest) {
    bytes.push(match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    });
    bytes.extend_from_slice(&digest.bytes);
}

fn append_len_prefixed_bytes(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(
        &u64::try_from(value.len())
            .expect("native request digest field exceeds canonical u64 framing")
            .to_be_bytes(),
    );
    bytes.extend_from_slice(value);
}

fn trust_vc_request_has_only_clean_cic_certificates(
    module: &Module,
    request: &TrustVcNativeRequest,
) -> bool {
    !request.certificates.is_empty()
        && request.certificates.iter().all(|certificate_ref| {
            module.proof_certificates.iter().any(|certificate| {
                certificate.lineage_ref() == *certificate_ref
                    && matches!(certificate.evidence, trust_ir::ProofEvidence::CleanCic { .. })
            })
        })
}

fn trust_vc_evidence_bundle_for_request(
    request: &TrustVcNativeRequest,
    trust_ir_module_digest: ProofDigest,
) -> TrustVcNativeEvidenceBundle {
    let mut artifacts = request
        .certificates
        .iter()
        .map(|certificate| {
            NativeEvidenceArtifact::new(
                trust_vc_certificate_import_artifact_name(certificate),
                NativeEvidenceArtifactKind::TrustVcCertificateImport,
                certificate.evidence_digest,
            )
        })
        .collect::<Vec<_>>();
    if let Some(replay) = &request.provenance.replay
        && let Some(transcript_digest) = replay.transcript_digest
    {
        artifacts.push(NativeEvidenceArtifact::new(
            format!("trust_vc-request-{}-replay-transcript", request.id.index()),
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
    }

    TrustVcNativeEvidenceBundle {
        request: request.id,
        mode: request.mode,
        obligations: request.obligations.clone(),
        verifier: request.provenance.expected_verifier.clone(),
        solvers: request.provenance.solvers.clone(),
        replay: request
            .provenance
            .replay
            .clone()
            .expect("TrustVc request provenance always carries replay identity"),
        trust_ir_module_digest,
        request_digest: NativeVerificationRequest::TrustVc(request.clone()).stable_digest(),
        artifacts,
    }
}

fn trust_vc_certificate_import_artifact_name(
    certificate: &trust_ir::ProofCertificateRef,
) -> String {
    format!(
        "trust_vc-certificate-import-proof-{}-{}-{}",
        certificate.obligation.index(),
        certificate.prover,
        proof_digest_hex(certificate.evidence_digest)
    )
}

fn proof_digest_hex(digest: ProofDigest) -> String {
    let mut hex = String::with_capacity(digest.bytes.len() * 2);
    for byte in digest.bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

fn request_obligations(
    module: &Module,
    owns: impl Fn(&trust_ir::ProofObligation) -> bool,
) -> Vec<ProofId> {
    module
        .proof_obligations
        .iter()
        .filter(|obligation| owns(obligation))
        .map(|obligation| obligation.id)
        .collect()
}

fn trust_vc_owns_obligation(kind: &ObligationKind) -> bool {
    matches!(kind, ObligationKind::MemorySafety | ObligationKind::RefinementType)
}

fn trust_mc_owns_obligation(kind: &ObligationKind) -> bool {
    // Trust (trust-ir-spine item T1): the new routing-grade panic-class kinds
    // (`ArithmeticSafety`, `BoundsCheck`) are panic-freedom obligations — trust-mc
    // owns them exactly as it owns `PanicFreedom`, preserving current routing.
    matches!(
        kind,
        ObligationKind::TranslationValidation
            | ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
            | ObligationKind::PanicFreedom
            | ObligationKind::ArithmeticSafety
            | ObligationKind::BoundsCheck
    )
}

#[cfg(test)]
mod tests {
    use serde_json::json;
    use trust_ir::{
        Block, BlockId, FuncTy, Function, Inst, InstrNode,
        NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION, ProofEvidence, ProofFormula, ProofObligation,
        ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
        PublicObligationIdentity, Ty, ValueId,
    };

    use super::*;

    fn digest(seed: u8) -> ProofDigest {
        ProofDigest::sha256([seed; 32])
    }

    #[test]
    fn native_mc_requests_declare_native_execution_without_imports_or_slicing() {
        let bundle = native_verification_bundle_from_module(
            native_request_module_without_trust_vc_lane(),
            digest(0x35),
            FuncId::new(0),
        )
        .expect("native bundle builds");
        let mut requests = Vec::new();
        for request in &bundle.requests {
            let NativeVerificationRequest::TrustMc(request) = request else {
                continue;
            };
            requests.push(request.obligations.clone());
            assert_eq!(request.mode, TrustMcVerificationMode::Chc);
            assert_eq!(request.options.memory_model, TrustMcMemoryModel::TrustIrPlaces);
            assert_eq!(
                request.options.arithmetic_model,
                TrustMcArithmeticModel::FixedWidthBitvectors
            );
            assert_eq!(request.options.chc.engine, TrustMcChcEngine::NativePdr);
            assert_eq!(request.options.chc.invariant_source, TrustMcInvariantSource::None);
            assert!(request.options.chc.pdr.enabled);
            assert_eq!(request.options.chc.pdr.max_frames, None);
            assert_eq!(request.options.chc.pdr.generalization, TrustMcPdrGeneralization::Cubes);
            assert!(request.options.chc.emit_horn_clauses);
            assert_eq!(request.options.slicing, TrustMcSlicingMode::None);
        }
        assert_eq!(
            requests,
            vec![vec![ProofId::new(1)], vec![ProofId::new(2)], vec![ProofId::new(3)]],
            "each primary request must declare the executed profile"
        );
        let NativeVerificationRequest::TrustWp(alternative) = &bundle.requests[3] else {
            panic!("the body-aware WP fallback remains a separate request");
        };
        assert_eq!(alternative.obligations, [ProofId::new(3)]);
    }

    #[test]
    fn monomorphization_authority_digest_frames_semantic_fields() {
        fn legacy_unframed_payload(module: &str, function: FuncId, source_item: &str) -> Vec<u8> {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(module.as_bytes());
            bytes.push(0);
            bytes.extend_from_slice(&function.index().to_le_bytes());
            bytes.extend_from_slice(source_item.as_bytes());
            bytes
        }

        fn framed_identity_payload(module: &str, function: FuncId, source_item: &str) -> Vec<u8> {
            let mut bytes = Vec::new();
            append_len_prefixed_bytes(&mut bytes, module.as_bytes());
            bytes.extend_from_slice(&function.index().to_be_bytes());
            append_len_prefixed_bytes(&mut bytes, source_item.as_bytes());
            bytes
        }

        // These distinct tuples collided under the former NUL-delimited payload.
        let left = (Module::new("a"), FuncId::new(98), "cdef");
        let right = (Module::new("a\0b"), FuncId::new(0x6463_0000), "ef");
        assert_eq!(
            legacy_unframed_payload(&left.0.name, left.1, left.2),
            legacy_unframed_payload(&right.0.name, right.1, right.2),
            "the regression fixture must exercise the former ambiguous framing"
        );
        assert_ne!(
            framed_identity_payload(&left.0.name, left.1, left.2),
            framed_identity_payload(&right.0.name, right.1, right.2),
            "canonical field framing itself must separate the formerly colliding tuples"
        );

        let left_digest =
            native_monomorphization_digest(left.0.stable_digest(), &left.0.name, left.1, left.2);
        let right_digest = native_monomorphization_digest(
            right.0.stable_digest(),
            &right.0.name,
            right.1,
            right.2,
        );
        assert_eq!(left_digest.algorithm, ProofDigestAlgorithm::Sha256);
        assert_eq!(right_digest.algorithm, ProofDigestAlgorithm::Sha256);
        assert_ne!(
            left_digest, right_digest,
            "monomorphization authority must distinguish different semantic tuples"
        );

        let mut i32_instance = Module::new("same_item_module");
        i32_instance.types.push(Ty::I32);
        let mut i64_instance = Module::new("same_item_module");
        i64_instance.types.push(Ty::I64);
        assert_eq!(i32_instance.name, i64_instance.name);
        assert_ne!(
            i32_instance.stable_digest(),
            i64_instance.stable_digest(),
            "the semantic-change fixture must alter canonical typed module identity"
        );
        assert_ne!(
            native_monomorphization_digest(
                i32_instance.stable_digest(),
                &i32_instance.name,
                FuncId::new(0),
                "generic_item",
            ),
            native_monomorphization_digest(
                i64_instance.stable_digest(),
                &i64_instance.name,
                FuncId::new(0),
                "generic_item",
            ),
            "same-name, same-index monomorphizations with different typed modules must not share proof authority"
        );
    }

    fn native_request_module() -> Module {
        let mut module = native_request_module_without_source_metadata();
        attach_obligation_source_metadata(&mut module);
        module
    }

    /// `native_request_module()` minus its trust_vc (`MemorySafety`) lane.
    ///
    /// trust-ir now binds proof admission to replayed evidence: the fixture's
    /// `Discharged` MemorySafety obligation carries an opaque `LeanProof`
    /// certificate that no in-process validator can replay, so bundle
    /// validation fail-closes on it (`TrustVcCertificateNotDischarged`) and
    /// the builder can no longer return a bundle containing that lane.
    /// Happy-path tests build from this module; the trust_vc lane itself is
    /// pinned via the exact fail-closed error in
    /// `native_bundle_builder_emits_only_typed_trust_vc_and_trust_mc_requests`.
    pub(super) fn native_request_module_without_trust_vc_lane() -> Module {
        let mut module = native_request_module();
        let removed = module.proof_obligations.remove(0);
        assert!(
            matches!(removed.kind, ObligationKind::MemorySafety),
            "fixture obligation 0 is the trust_vc memory-safety lane"
        );
        module.proof_certificates.clear();
        module
    }
    fn native_request_module_without_source_metadata() -> Module {
        let mut module = Module::new("trust_native_request_bundle");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "checked_add", ft, BlockId::new(0))
            .with_producer(trust_ir::Producer::TrustIr);
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
            ],
        });
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::MemorySafety,
                ProofStatus::Discharged,
                "Trust MIR place projection stays in bounds",
            )
            .with_formula(ProofFormula::trust_types_json(
                r#"{"Predicate":"mir_place_in_bounds","args":["checked_add"]}"#,
                "(mir_place_in_bounds checked_add)",
                "Bool",
            )),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::TranslationValidation,
                ProofStatus::Pending,
                "Trust MIR to TrustIr lowering preserves checked_add",
            )
            .with_formula(ProofFormula::smtlib2(
                "(= (rust_mir.checked_add lhs rhs) (trust_ir.checked_add lhs rhs))",
                "Bool",
            )),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(2),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "checked_add arguments satisfy verifier preconditions",
            )
            .with_formula(ProofFormula::smtlib2("(and (i32 lhs) (i32 rhs))", "Bool")),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(3),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "checked_add result satisfies contract postcondition",
            )
            .with_formula(ProofFormula::smtlib2("(i32 result)", "Bool")),
        );

        module.proof_certificates.push(trust_ir::ProofCertificate {
            obligation: ProofId::new(0),
            prover: "trust_vc".to_string(),
            evidence: ProofEvidence::LeanProof("exact TrustVc.MIR.place_projection_sound".into()),
            // v41: no native evidence bundle to project a coverage assurance from.
            assurance: None,
        });

        module
    }

    fn kernel_certified_native_bundle_module() -> Module {
        let mut module = Module::new("trust_native_kernel_bundle");
        let file =
            module.intern_file("src/kernel_bundle.rs").expect("Module::intern_file: test fixture");
        let function_id = FuncId::new(0);
        let ft = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(function_id, "kernel_checked", ft, BlockId::new(0))
            .with_producer(trust_ir::Producer::TrustIr);
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: Vec::new(),
            body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
        });
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        let obligations = [
            (
                ObligationKind::Postcondition,
                ProofStatus::Discharged,
                "kernel-certified contract",
                ProofFormula::smtlib2("(>= 5 0)", "Bool"),
                "trust_ir-native-trust-vc-request-0-proof-0",
            ),
            (
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "trust-mc panic freedom",
                ProofFormula::smtlib2("true", "Bool"),
                "trust_ir-native-trust-mc-request-1-proof-1",
            ),
            (
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "trust-mc postcondition",
                ProofFormula::smtlib2("true", "Bool"),
                "trust_ir-native-trust-mc-request-2-proof-2",
            ),
        ];
        for (index, (kind, status, description, formula, public_id)) in
            obligations.into_iter().enumerate()
        {
            let proof = ProofId::new(index as u32);
            module.proof_obligations.push(
                ProofObligation::new(proof, kind, status, description)
                    .with_formula(formula)
                    .with_function(function_id)
                    .with_source(
                        ProofObligationSourceIdentity::new(
                            format!("kernel-native-bundle:source:{index}"),
                            format!("kernel-native-bundle:assertion:{index}"),
                        )
                        .with_range(ProofObligationSourceRange {
                            file,
                            start_line: 10 + index as u32,
                            start_col: 1,
                            end_line: 10 + index as u32,
                            end_col: 2,
                        })
                        .with_public(PublicObligationIdentity {
                            obligation_id: public_id.to_string(),
                            semantic_digest: digest(0x90 + index as u8),
                        }),
                    ),
            );
        }
        let certificate = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
            &module.proof_obligations[0],
            "trust-vc",
        )
        .expect("ground tautology is kernel-certified");
        module.proof_certificates.push(certificate);
        module
    }

    fn attach_obligation_source_metadata(module: &mut Module) {
        let file = module.intern_file("src/lib.rs").expect("Module::intern_file: test fixture");
        for obligation in &mut module.proof_obligations {
            let native_assertion_id = 40 + obligation.id.index();
            let line = 100 + obligation.id.index();
            obligation.function = Some(FuncId::new(0));
            obligation.source = Some(
                ProofObligationSourceIdentity::new(
                    format!("trust-native-request:checked_add:{}", obligation.id.index()),
                    format!("trust-assertion:checked_add:{}", obligation.id.index()),
                )
                .with_range(ProofObligationSourceRange {
                    file,
                    start_line: line,
                    start_col: 9,
                    end_line: line,
                    end_col: 19,
                })
                .with_public(PublicObligationIdentity {
                    obligation_id: format!(
                        "trust-native-request:checked_add:public:{}",
                        obligation.id.index()
                    ),
                    semantic_digest: digest(0x80_u8.saturating_add(obligation.id.index() as u8)),
                }),
            );
            obligation.formula =
                Some(obligation_source_formula(obligation.id, native_assertion_id, line));
        }
    }

    fn obligation_source_formula(
        obligation: ProofId,
        native_assertion_id: u32,
        line: u32,
    ) -> ProofFormula {
        ProofFormula {
            schema: TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
            payload: json!({
                "source_id": format!("trust-native-request:checked_add:{}", obligation.index()),
                "assertion_id": format!("trust-assertion:checked_add:{}", obligation.index()),
                "native_assertion_id": native_assertion_id,
                "span": {
                    "file": "src/lib.rs",
                    "line_start": line,
                    "col_start": 9,
                    "line_end": line,
                    "col_end": 19,
                },
            })
            .to_string(),
            smtlib: None,
            sort: None,
            // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
            bindings: Vec::new(),
        }
    }

    #[test]
    fn native_bundle_accepts_explicit_mir_compatibility_provenance() {
        let module = native_request_module_without_trust_vc_lane();
        assert!(
            module
                .functions
                .iter()
                .all(|function| function.producer.as_ref() == Some(&Producer::TrustIr))
        );

        let bundle = native_verification_bundle_from_module(module, digest(0x21), FuncId::new(0))
            .expect("an explicitly MIR-produced module remains admissible");

        assert_eq!(bundle.producer, NativeBundleProducer::TrustIr);
        assert!(matches!(bundle.input, NativeAdapterInput::RustMir { .. }));
    }

    #[test]
    fn pending_give_back_without_ground_formula_emits_no_trust_wp_request() {
        let mut module = native_request_module_without_source_metadata();
        module.proof_obligations.clear();
        module.proof_certificates.clear();
        let file =
            module.intern_file("src/give_back.rs").expect("Module::intern_file: test fixture");
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::GiveBackRefinement,
                ProofStatus::Pending,
                "mutable-reference give-back candidate",
            )
            .with_function(FuncId::new(0))
            .with_source(
                ProofObligationSourceIdentity::new("give-back:source", "give-back:assertion")
                    .with_range(ProofObligationSourceRange {
                        file,
                        start_line: 1,
                        start_col: 1,
                        end_line: 1,
                        end_col: 2,
                    })
                    .with_public(PublicObligationIdentity {
                        obligation_id: "give-back:public".to_string(),
                        semantic_digest: digest(0x24),
                    }),
            ),
        );

        let error = native_verification_bundle_from_module(module, digest(0x25), FuncId::new(0))
            .expect_err("a structural Pending give-back without a formula must not mint a request");
        assert_eq!(error, NativeVerificationBundleBuildError::EmptyRequests);
    }

    #[test]
    fn native_bundle_rejects_legacy_source_digest_authority() {
        let legacy = ProofDigest::trust_ir_stable("legacy-source-authority", b"source");
        let error = native_verification_bundle_from_module(
            native_request_module_without_trust_vc_lane(),
            legacy,
            FuncId::new(0),
        )
        .expect_err("legacy source digests must not cross the native authority boundary");

        assert_eq!(
            error,
            NativeVerificationBundleBuildError::NonAuthoritativeSourceDigest {
                algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            }
        );
    }

    #[test]
    fn native_bundle_rejects_direct_producer_despite_injected_obligations() {
        let mut module = native_request_module();
        module.functions[0].producer = Some(Producer::TRust);
        assert!(
            !module.proof_obligations.is_empty(),
            "the direct module must exercise the provenance gate, not the empty-obligation guard"
        );

        let error = native_verification_bundle_from_module(module, digest(0x23), FuncId::new(0))
            .expect_err(
                "a direct Trust frontend module must not be relabelled as MIR compatibility",
            );

        assert_eq!(
            error,
            NativeVerificationBundleBuildError::NonMirCompatibilityProducer {
                function: FuncId::new(0),
                producer: Some(Producer::TRust),
            }
        );
    }

    #[test]
    fn native_bundle_builder_preserves_primaries_and_adds_typed_wp_alternatives() {
        // trust_vc lane: the builder still plans the typed TrustVc request
        // (id 0, ImportProofCertificates) carrying the module's certificate for
        // the MemorySafety obligation — but trust-ir's replayed-evidence
        // authority gate rejects the fixture's opaque `LeanProof` certificate,
        // so the builder's internal validation fail-closes. Pinning the EXACT
        // single error proves both that the typed TrustVc request was emitted
        // (request id 0, the module certificate, the trust_vc prover) and that
        // everything else about the planned requests was admissible.
        let module = native_request_module();
        let trust_vc_certificate = module.proof_certificates[0].lineage_ref();
        assert_eq!(trust_vc_certificate.obligation, ProofId::new(0));
        let trust_vc_module_digest = module.stable_digest();
        let error = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect_err("unreplayable Discharged trust_vc evidence must fail closed");
        let NativeVerificationBundleBuildError::Validation(errors) = error else {
            panic!("expected native bundle validation failure, got {error:?}");
        };
        assert_eq!(
            errors.len(),
            1,
            "only the trust_vc replay-authority gate may reject the planned bundle: {errors:?}"
        );
        assert!(
            matches!(
                &errors[0],
                NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                    request: NativeRequestId(0),
                    obligation: ProofId(0),
                    prover,
                    status: ProofStatus::Discharged,
                } if prover == &trust_vc_certificate.prover
            ),
            "the typed TrustVc request must carry the module certificate: {errors:?}"
        );

        // trust_vc provenance: the request planner's provenance identity stays
        // pinned directly, since the unreplayable lane can no longer be
        // observed through a validated bundle.
        let module = native_request_module();
        let mut compiler_facts = NativeCompilerFacts::default();
        populate_compiler_facts_for_module(
            &mut compiler_facts,
            &module,
            FuncId::new(0),
            trust_vc_module_digest,
        )
        .expect("full fixture has exact compiler facts");
        let trust_vc_provenance = trust_vc_request_provenance(
            &module,
            &compiler_facts,
            digest(0x31),
            trust_vc_module_digest,
            &[ProofId::new(0)],
        );
        assert_eq!(trust_vc_provenance.expected_verifier.name, "trust_vc");
        assert_eq!(
            trust_vc_provenance.expected_verifier.version.as_deref(),
            Some(TRUST_VC_NATIVE_REQUEST_INTERFACE_VERSION)
        );
        assert_eq!(
            trust_vc_provenance.expected_verifier.revision.as_deref(),
            Some(TRUST_VC_NATIVE_REQUEST_INTERFACE_REVISION)
        );
        assert!(!trust_vc_provenance.solvers.is_empty());
        assert_eq!(
            trust_vc_provenance.solvers[0].version.as_deref(),
            Some(TRUST_VC_LEAN_SOLVER_INTERFACE_VERSION)
        );
        assert_eq!(trust_vc_provenance.replay_context.atoms.len(), 1);
        assert_eq!(trust_vc_provenance.replay_context.atoms[0].obligation, Some(ProofId::new(0)));

        // TrustMC lane: with the unreplayable TrustVC lane removed, the
        // planned bundle is admissible end to end and every ordinary contract
        // kind is routed to TrustMC. No TrustWP request is emitted.
        let module = native_request_module_without_trust_vc_lane();
        let trust_ir_module_digest = module.stable_digest();
        let bundle = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect("native bundle builds");

        assert_eq!(bundle.schema_version, NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION);
        assert_eq!(bundle.producer, NativeBundleProducer::TrustIr);
        assert_eq!(
            bundle.trust_ir_module_digest, trust_ir_module_digest,
            "the bundle builder must derive authority from the completed canonical module"
        );
        assert!(matches!(
            bundle.input,
            NativeAdapterInput::RustMir { body_digest } if body_digest == digest(0x31)
        ));
        assert_eq!(bundle.provenance.producer_version, TRUST_NATIVE_REQUEST_COMPILER_VERSION);
        assert_eq!(bundle.provenance.source_language, NativeSourceLanguage::Rust);
        assert_eq!(bundle.provenance.source_digest, Some(digest(0x31)));
        assert_eq!(
            bundle.provenance.toolchain,
            vec![
                NativeToolIdentity::new("TrustIr")
                    .with_version(TRUST_NATIVE_REQUEST_COMPILER_VERSION)
                    .with_revision(TRUST_NATIVE_REQUEST_COMPILER_REVISION)
            ]
        );
        assert_eq!(bundle.lineage.nodes[0].transform.stage, ProofTransformStage::TrustIrLowering);
        assert_eq!(bundle.lineage.nodes[0].transform.producer, "TrustIr");
        assert_eq!(
            bundle
                .module
                .function_by_id(FuncId::new(0))
                .and_then(|function| function.producer.as_ref()),
            Some(&trust_ir::Producer::TrustIr),
            "MIR compatibility functions and their native bundle must carry TrustIr provenance"
        );
        assert_eq!(bundle.compiler_facts.monomorphizations.len(), 1);
        assert_eq!(bundle.compiler_facts.monomorphizations[0].id, NativeMonomorphizationId::new(0));
        assert_eq!(bundle.compiler_facts.monomorphizations[0].function, Some(FuncId::new(0)));
        assert_eq!(bundle.compiler_facts.monomorphizations[0].source_item, "checked_add");
        assert!(bundle.compiler_facts.obligation_sources.iter().all(|source| {
            source.monomorphization == Some(NativeMonomorphizationId::new(0))
                && source.facts
                    == vec![NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(
                        0,
                    ))]
        }));
        assert_eq!(
            bundle.lineage.nodes[0].replay.as_ref().map(|replay| replay.engine.as_str()),
            Some("Trust.native-admission")
        );
        assert!(bundle.lineage.nodes[0].replay.as_ref().is_some_and(|replay| {
            replay.invocation.contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
        }));
        assert_eq!(bundle.requests.len(), 4);
        assert!(
            bundle.evidence_bundles.is_empty(),
            "request planning must not manufacture verifier result evidence"
        );

        match &bundle.requests[0] {
            NativeVerificationRequest::TrustMc(request) => {
                assert_eq!(request.id, NativeRequestId::new(0));
                assert_eq!(request.mode, TrustMcVerificationMode::Chc);
                assert_eq!(request.function, FuncId::new(0));
                assert_eq!(request.obligations, vec![ProofId::new(1)]);
                assert!(request.options.chc.emit_horn_clauses);
                assert_eq!(request.provenance.expected_verifier.name, "trust_mc");
                assert_eq!(
                    request.provenance.expected_verifier.version.as_deref(),
                    Some(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                );
                assert_eq!(
                    request.provenance.expected_verifier.revision.as_deref(),
                    Some(TRUST_NATIVE_REQUEST_TRANSFORM_VERSION)
                );
                assert!(request.provenance.replay.as_ref().is_some_and(|replay| {
                    replay.invocation.contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                }));
                assert!(!request.provenance.solvers.is_empty());
                assert_eq!(request.provenance.replay_context.atoms.len(), 1);
                assert_eq!(
                    request.provenance.replay_context.atoms[0].obligation,
                    Some(ProofId::new(1))
                );
            }
            other => panic!("expected TrustMc request, got {other:?}"),
        }
        match &bundle.requests[1] {
            NativeVerificationRequest::TrustMc(request) => {
                assert_eq!(request.id, NativeRequestId::new(1));
                assert_eq!(request.mode, TrustMcVerificationMode::Chc);
                assert_eq!(request.function, FuncId::new(0));
                assert_eq!(request.obligations, vec![ProofId::new(2)]);
                assert!(request.options.chc.emit_horn_clauses);
                assert_eq!(request.provenance.expected_verifier.name, "trust_mc");
                assert!(!request.provenance.solvers.is_empty());
                assert_eq!(request.provenance.replay_context.atoms.len(), 1);
                assert_eq!(
                    request.provenance.replay_context.atoms[0].obligation,
                    Some(ProofId::new(2))
                );
            }
            other => panic!("expected second TrustMc request, got {other:?}"),
        }
        match &bundle.requests[2] {
            NativeVerificationRequest::TrustMc(request) => {
                assert_eq!(request.id, NativeRequestId::new(2));
                assert_eq!(request.mode, TrustMcVerificationMode::Chc);
                assert_eq!(request.function, FuncId::new(0));
                assert_eq!(request.obligations, vec![ProofId::new(3)]);
                assert!(request.options.chc.emit_horn_clauses);
                assert_eq!(request.provenance.expected_verifier.name, "trust_mc");
                assert!(!request.provenance.solvers.is_empty());
                assert_eq!(request.provenance.replay_context.atoms.len(), 1);
            }
            other => panic!("expected third TrustMc request, got {other:?}"),
        }
        let NativeVerificationRequest::TrustWp(alternative) = &bundle.requests[3] else {
            panic!("one body-aware postcondition alternative follows stable primary request ids");
        };
        assert_eq!(alternative.id, NativeRequestId::new(3));
        assert_eq!(alternative.function, FuncId::new(0));
        assert_eq!(alternative.obligations, [ProofId::new(3)]);
        assert_eq!(alternative.mode, TrustWpVerificationMode::WeakestPrecondition);
        assert!(alternative.provenance.replay_context.atoms.is_empty());

        bundle.validate().expect("native bundle validates");
    }

    #[test]
    fn kernel_certified_contract_routes_to_trust_vc_with_typed_import_evidence() {
        let module = kernel_certified_native_bundle_module();
        let certificate_ref = module.proof_certificates[0].lineage_ref();
        let bundle = native_verification_bundle_from_module(module, digest(0x42), FuncId::new(0))
            .expect("kernel-certified native bundle builds");

        assert_eq!(bundle.requests.len(), 4);
        let NativeVerificationRequest::TrustVc(trust_vc) = &bundle.requests[0] else {
            panic!("CleanCic-certified contract must route to TrustVc import");
        };
        assert_eq!(trust_vc.id, NativeRequestId::new(0));
        assert_eq!(trust_vc.obligations, vec![ProofId::new(0)]);
        assert_eq!(trust_vc.certificates, vec![certificate_ref.clone()]);
        assert!(matches!(bundle.requests[1], NativeVerificationRequest::TrustMc(_)));
        assert!(matches!(bundle.requests[2], NativeVerificationRequest::TrustMc(_)));
        let NativeVerificationRequest::TrustWp(alternative) = &bundle.requests[3] else {
            panic!("only the unproved postcondition receives a WP alternative");
        };
        assert_eq!(alternative.obligations, [ProofId::new(2)]);

        assert_eq!(bundle.evidence_bundles.len(), 1);
        let NativeEvidenceBundle::TrustVc(evidence) = &bundle.evidence_bundles[0] else {
            panic!("only the kernel-replayed TrustVc import may mint planner evidence");
        };
        assert_eq!(evidence.request, trust_vc.id);
        assert_eq!(evidence.obligations, trust_vc.obligations);
        assert_eq!(evidence.trust_ir_module_digest, bundle.trust_ir_module_digest);
        assert_eq!(
            evidence.request_digest,
            NativeVerificationRequest::TrustVc(trust_vc.clone()).stable_digest()
        );
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.kind == NativeEvidenceArtifactKind::TrustVcCertificateImport
                && artifact.digest == certificate_ref.evidence_digest
        }));
        assert!(
            evidence
                .artifacts
                .iter()
                .any(|artifact| artifact.kind == NativeEvidenceArtifactKind::ReplayTranscript)
        );
        bundle.validate().expect("kernel-certified evidence remains replay-valid");
    }

    /// The writer records NO coverage row, and trust-ir-build agrees that `None`
    /// is the only honest value for the certificate it carries: the row the
    /// writer declines to record (`Unbounded`, citing the TrustVc import request
    /// that carries the certificate) is left UNDETERMINED by
    /// `coverage_assurance_report` itself — its admission rule
    /// (`undetermined() == 0`) would refuse it, and trust-vc's release admission
    /// refuses it as `CertificateCoverageUndetermined`. The oracle here is the
    /// upstream rule, not a mirror of it.
    #[test]
    fn kernel_certified_import_records_no_coverage_and_upstream_leaves_the_row_undetermined() {
        use trust_ir::proof::{CoverageAssurance, CoverageBound};

        let bundle = native_verification_bundle_from_module(
            kernel_certified_native_bundle_module(),
            digest(0x42),
            FuncId::new(0),
        )
        .expect("kernel-certified native bundle builds");
        assert!(
            bundle
                .module
                .proof_certificates
                .iter()
                .all(|certificate| certificate.assurance.is_none()),
            "the writer must leave every coverage row NOT RECORDED"
        );
        let report = trust_ir_build::coverage_assurance_report(&bundle.module, Some(&bundle));
        assert!(report.is_checked(), "{}", report.summary());
        assert_eq!(report.recorded(), 0);
        assert!(report.errors().is_empty(), "{:?}", report.errors());

        // The row the writer declines to record.
        let mut probe = bundle.clone();
        let NativeVerificationRequest::TrustVc(import) = &probe.requests[0] else {
            panic!("the CleanCic certificate rides the TrustVc import request");
        };
        assert_eq!(import.mode, TrustVcVerificationMode::ImportProofCertificates);
        assert_eq!(import.obligations, vec![probe.module.proof_certificates[0].obligation]);
        let request_digest = probe.requests[0].stable_digest();
        probe.module.proof_certificates[0].assurance =
            Some(CoverageAssurance { bound: CoverageBound::Unbounded, request_digest });
        // Re-point only the header so the report reaches the per-row checks.
        // The requests still bind the PRE-row module digest through their
        // replay transcripts: the digest cycle the writer's doc names.
        probe.trust_ir_module_digest = probe.module.stable_digest();
        assert_ne!(probe.trust_ir_module_digest, bundle.trust_ir_module_digest);
        let report = trust_ir_build::coverage_assurance_report(&probe.module, Some(&probe));
        assert!(report.is_checked(), "{}", report.summary());
        assert!(report.errors().is_empty(), "{:?}", report.errors());
        assert_eq!(report.recorded(), 1);
        assert_eq!(report.agreed(), 0, "a TrustVc import request establishes no bound");
        assert_eq!(report.undetermined(), 1, "{}", report.summary());
    }

    /// A certificate that arrives with a coverage row already recorded cites a
    /// request this writer has not minted yet — and never can, since every
    /// request it mints binds the module digest that covers the row. Refused by
    /// name at the writer, before any request exists.
    #[test]
    fn a_certificate_arriving_with_a_coverage_row_is_refused_by_name() {
        use trust_ir::proof::{CoverageAssurance, CoverageBound};

        for bound in [
            CoverageBound::Unbounded,
            CoverageBound::UnwindBounded { depth: 1 },
            CoverageBound::ModelBounded { size: 4 },
            CoverageBound::Unrecorded,
        ] {
            let mut module = kernel_certified_native_bundle_module();
            let obligation = module.proof_certificates[0].obligation;
            module.proof_certificates[0].assurance =
                Some(CoverageAssurance { bound, request_digest: digest(0x77) });
            let error =
                native_verification_bundle_from_module(module, digest(0x42), FuncId::new(0))
                    .expect_err("a pre-recorded coverage row must not cross the writer");
            assert_eq!(
                error,
                NativeVerificationBundleBuildError::PreRecordedCoverageAssurance { obligation },
                "bound {bound:?}"
            );
        }
    }

    #[test]
    fn defined_narrowing_cast_never_enters_native_request_inventory() {
        let mut module =
            crate::lower::lower_to_trust_ir(&crate::parity::tests::cast_overflow_narrowing())
                .expect("defined narrowing cast lowers");

        assert!(
            module.proof_obligations.is_empty(),
            "a total Rust `as` cast must not mint a module obligation: {:?}",
            module.proof_obligations
        );

        // Add one unrelated, genuine request unit so the bundle planner runs.
        // Every request must contain only that unit; a resurrected cast-range
        // obligation would appear as a second TrustMc request and fail this pin.
        let proof = ProofId::new(0);
        let source_file =
            module.intern_file("src/lib.rs").expect("Module::intern_file: test fixture");
        module.proof_obligations.push(
            ProofObligation::new(
                proof,
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "independent request sentinel",
            )
            .with_formula(obligation_source_formula(proof, 77, 12))
            .with_function(FuncId::new(0))
            .with_source(
                ProofObligationSourceIdentity::new(
                    "trust-native-request:sentinel",
                    "trust-assertion:sentinel",
                )
                .with_range(ProofObligationSourceRange {
                    file: source_file,
                    start_line: 12,
                    start_col: 0,
                    end_line: 12,
                    end_col: 0,
                })
                .with_public(PublicObligationIdentity {
                    obligation_id: "trust-native-request:sentinel:public".to_string(),
                    semantic_digest: digest(0x91),
                }),
            ),
        );
        let bundle = native_verification_bundle_from_module(module, digest(0x41), FuncId::new(0))
            .expect("sentinel native bundle builds");

        assert_eq!(bundle.requests.len(), 1, "only the sentinel request is planned");
        let NativeVerificationRequest::TrustMc(request) = &bundle.requests[0] else {
            panic!("panic-freedom sentinel must route to TrustMc");
        };
        assert_eq!(request.obligations, vec![proof]);
        assert_eq!(bundle.module.proof_obligations.len(), 1);
        assert_eq!(bundle.module.proof_obligations[0].description, "independent request sentinel");
    }

    #[test]
    fn native_bundle_rejects_requested_obligations_without_source_assertion_metadata() {
        let err = native_verification_bundle_from_module(
            native_request_module_without_source_metadata(),
            digest(0x31),
            FuncId::new(0),
        )
        .expect_err("unannotated requested obligations must fail closed");
        assert_eq!(
            err,
            NativeVerificationBundleBuildError::MissingObligationSource(ProofId::new(0))
        );
    }

    #[test]
    fn trust_vc_metadata_only_memory_unit_does_not_create_certificate_import() {
        let mut module = native_request_module();
        module.proof_certificates.clear();
        module.proof_obligations[0].formula = Some(ProofFormula {
            schema: TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
            payload: json!({
                "source_id": "trust-native-request:checked_add:0",
                "assertion_id": "trust-assertion:checked_add:0",
                "native_assertion_id": 40,
                "span": {
                    "file": "src/lib.rs",
                    "line_start": 100,
                    "col_start": 9,
                    "line_end": 100,
                    "col_end": 19,
                },
                "trust_vc.mir_memory.proof_unit": {
                    "unit_id": "metadata-only",
                    "obligations": [{"id": "memory"}],
                },
            })
            .to_string(),
            smtlib: None,
            sort: None,
            // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
            bindings: Vec::new(),
        });

        let err = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect_err("metadata-only TrustVc memory payload must fail closed");
        let NativeVerificationBundleBuildError::Validation(errors) = err else {
            panic!("expected native bundle validation failure, got {err:?}");
        };
        assert!(
            errors.iter().any(|error| matches!(
                error,
                NativeVerificationBundleError::MissingTrustVcEvidenceForObligation {
                    request: NativeRequestId(0),
                    obligation: ProofId(0),
                }
            )),
            "metadata-only trust_vc.mir_memory.proof_unit must not become proof-grade import evidence: {errors:?}"
        );
    }

    #[test]
    fn native_bundle_uses_lowered_obligation_source_metadata() {
        let mut module = native_request_module_without_trust_vc_lane();
        let proof_obligation = module
            .proof_obligations
            .iter_mut()
            .find(|obligation| obligation.id == ProofId::new(2))
            .expect("precondition fixture");
        proof_obligation.formula = Some(ProofFormula {
            schema: TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
            payload: json!({
                "source_id": "trust-contract:test::checked_add:requires:0",
                "assertion_id": "trust-assertion:trust-contract:test::checked_add:requires:0",
                "native_assertion_id": 41,
                "span": {
                    "file": "src/lib.rs",
                    "line_start": 17,
                    "col_start": 9,
                    "line_end": 17,
                    "col_end": 19,
                },
            })
            .to_string(),
            smtlib: None,
            sort: None,
            // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
            bindings: Vec::new(),
        });
        proof_obligation.source = Some(
            ProofObligationSourceIdentity::new(
                "trust-contract:test::checked_add:requires:0",
                "trust-assertion:trust-contract:test::checked_add:requires:0",
            )
            .with_range(ProofObligationSourceRange {
                file: 0,
                start_line: 17,
                start_col: 9,
                end_line: 17,
                end_col: 19,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "public:test::checked_add:requires:0".to_string(),
                semantic_digest: digest(0xa2),
            }),
        );

        let bundle = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect("native bundle builds");
        let source =
            bundle.obligation_source(ProofId::new(2)).expect("obligation source is recorded");

        assert_eq!(
            source.assertion_id,
            Some(NativeAssertionId::new(trust_types::stable_u32_id(
                b"trust-assertion:trust-contract:test::checked_add:requires:0"
            )))
        );
        assert_eq!(source.public_obligation_id, "public:test::checked_add:requires:0");
        assert_eq!(source.span, Some(SourceSpan { file: 0, line: 17, col: 9 }));
        bundle.validate().expect("native bundle validates");
    }

    #[test]
    fn native_bundle_rejects_public_obligation_identity_aliases() {
        let mut module = native_request_module();
        let first_public_id = "trust-native-request:checked_add:public:0";
        module.proof_obligations[1]
            .source
            .as_mut()
            .expect("embedded source")
            .public
            .as_mut()
            .expect("embedded public identity")
            .obligation_id = first_public_id.to_string();

        let err = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect_err("one public proof unit must not alias two native obligations");
        let NativeVerificationBundleBuildError::Validation(errors) = err else {
            panic!("expected native bundle validation failure, got {err:?}");
        };
        assert!(errors.iter().any(|error| matches!(
            error,
            NativeVerificationBundleError::DuplicatePublicObligationSource {
                public_obligation_id,
                first_obligation: ProofId(0),
                duplicate_obligation: ProofId(1),
            } if public_obligation_id == first_public_id
        )));
    }

    #[test]
    fn native_request_json_uses_upstream_variant_shape() {
        // The unreplayable trust_vc lane can no longer cross the builder's
        // fail-closed validation (see
        // `native_bundle_builder_emits_only_typed_trust_vc_and_trust_mc_requests`
        // for the exact-error pin), so the upstream JSON variant shape is
        // asserted on the lanes the builder can return; the TrustVc provenance
        // JSON shape is pinned below straight from the request planner.
        let module = native_request_module_without_trust_vc_lane();
        let bundle = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect("native bundle builds");
        let json = serde_json::to_value(&bundle).expect("bundle serializes");

        assert_eq!(json["schema_version"], json!(NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION));
        assert_eq!(json["producer"], json!("TrustIr"));
        assert!(json["input"]["RustMir"]["body_digest"].is_object());
        assert_eq!(json["requests"].as_array().map(Vec::len), Some(4));
        assert_eq!(json["compiler_facts"]["monomorphizations"].as_array().map(Vec::len), Some(1));
        assert_eq!(
            json["compiler_facts"]["obligation_sources"][0]["facts"].as_array().map(Vec::len),
            Some(1)
        );
        assert_eq!(json["requests"][0]["TrustMc"]["mode"], json!("Chc"));
        assert_eq!(json["requests"][1]["TrustMc"]["mode"], json!("Chc"));
        assert_eq!(json["requests"][2]["TrustMc"]["mode"], json!("Chc"));
        assert_eq!(json["requests"][0]["TrustMc"]["obligations"], json!([1]));
        assert_eq!(json["requests"][1]["TrustMc"]["obligations"], json!([2]));
        assert_eq!(json["requests"][2]["TrustMc"]["obligations"], json!([3]));
        assert_eq!(json["requests"][0]["TrustMc"]["options"]["chc"]["emit_horn_clauses"], true);
        assert_eq!(json["requests"][1]["TrustMc"]["options"]["chc"]["emit_horn_clauses"], true);
        assert_eq!(
            json["requests"][0]["TrustMc"]["provenance"]["expected_verifier"]["name"],
            "trust_mc"
        );
        assert_eq!(
            json["requests"][1]["TrustMc"]["provenance"]["expected_verifier"]["name"],
            "trust_mc"
        );
        assert_eq!(
            json["requests"][0]["TrustMc"]["provenance"]["expected_verifier"]["version"],
            TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION
        );
        assert!(
            json["requests"][0]["TrustMc"]["provenance"]["replay"]["invocation"]
                .as_str()
                .is_some_and(|invocation| invocation
                    .contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION))
        );
        assert_eq!(
            json["requests"][2]["TrustMc"]["provenance"]["expected_verifier"]["name"],
            "trust_mc"
        );
        assert_eq!(json["requests"][3]["TrustWp"]["id"], json!(3));
        assert_eq!(json["requests"][3]["TrustWp"]["function"], json!(0));
        assert_eq!(json["requests"][3]["TrustWp"]["obligations"], json!([3]));

        // TrustVc provenance JSON shape, pinned from the planner directly.
        let module = native_request_module();
        let trust_vc_module_digest = module.stable_digest();
        let mut compiler_facts = NativeCompilerFacts::default();
        populate_compiler_facts_for_module(
            &mut compiler_facts,
            &module,
            FuncId::new(0),
            trust_vc_module_digest,
        )
        .expect("full fixture has exact compiler facts");
        let trust_vc_provenance = serde_json::to_value(trust_vc_request_provenance(
            &module,
            &compiler_facts,
            digest(0x31),
            trust_vc_module_digest,
            &[ProofId::new(0)],
        ))
        .expect("trust_vc provenance serializes");
        assert_eq!(trust_vc_provenance["expected_verifier"]["name"], "trust_vc");
        assert_eq!(
            trust_vc_provenance["expected_verifier"]["version"],
            TRUST_VC_NATIVE_REQUEST_INTERFACE_VERSION
        );
        assert_eq!(
            trust_vc_provenance["expected_verifier"]["revision"],
            TRUST_VC_NATIVE_REQUEST_INTERFACE_REVISION
        );
        assert_eq!(
            trust_vc_provenance["replay_context"]["atoms"].as_array().map(Vec::len),
            Some(1)
        );
    }

    #[test]
    fn native_bundle_rejects_trust_mc_unsupported_semantics_in_request_provenance() {
        let mut module = native_request_module();
        module.proof_obligations[1].formula = Some(ProofFormula {
            schema: TRUST_OBLIGATION_SOURCE_SCHEMA.to_string(),
            payload: json!({
                "source_id": "trust-native-request:checked_add:1",
                "assertion_id": "trust-assertion:checked_add:1",
                "native_assertion_id": 41,
                "span": {
                    "file": "src/lib.rs",
                    "line_start": 101,
                    "col_start": 9,
                    "line_end": 101,
                    "col_end": 19,
                },
                "trust_native_admission": {
                    "status": "unsupported_semantics",
                    "detail": "pointer provenance semantics are not modeled by native TrustMc"
                }
            })
            .to_string(),
            smtlib: None,
            sort: None,
            // v41: no clause bindings — an empty table reads as UNBINDABLE, never as a wildcard.
            bindings: Vec::new(),
        });

        let err = native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
            .expect_err("unsupported TrustMc semantics must fail closed at bundle validation");
        let NativeVerificationBundleBuildError::Validation(errors) = err else {
            panic!("expected native bundle validation failure, got {err:?}");
        };
        assert!(
            errors.iter().any(|error| matches!(
                error,
                NativeVerificationBundleError::UnsupportedNativeRequestMode {
                    request: NativeRequestId(1),
                    reason: NativeUnsupportedModeReason::UnsupportedVerifierMode,
                    detail,
                } if detail.contains(TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION)
                    && detail.contains("pointer provenance semantics")
            )),
            "TrustMc unsupported semantics must be preserved in request provenance: {errors:?}"
        );
    }

    #[test]
    fn native_bundle_validation_rejects_mismatched_requests() {
        let module = native_request_module_without_trust_vc_lane();
        let mut bundle =
            native_verification_bundle_from_module(module, digest(0x31), FuncId::new(0))
                .expect("native bundle builds");

        let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[0] else {
            panic!("expected TrustMc request");
        };
        request.function = FuncId::new(99);
        request.obligations.push(ProofId::new(99));

        let errors = bundle.validate().expect_err("invalid request references are rejected");
        assert!(errors.iter().any(|error| {
            matches!(
                error,
                NativeVerificationBundleError::MissingFunction {
                    request: NativeRequestId(0),
                    function: FuncId(99),
                }
            )
        }));
        assert!(errors.iter().any(|error| {
            matches!(
                error,
                NativeVerificationBundleError::UnknownRequestObligation {
                    request: NativeRequestId(0),
                    obligation: ProofId(99),
                }
            )
        }));
    }

    /// `native_request_module_without_trust_vc_lane()` with a SECOND owning
    /// body, and the postcondition row re-scoped onto it.
    ///
    /// This is the shape the bundled-member gap produces: one module, two
    /// bodies, and an obligation inventory that is no longer about the subject
    /// alone. Nothing here generates a member VC — the row is simply relabelled
    /// — which is exactly the property under test: can the planner EMIT a
    /// well-formed bundle for it.
    fn two_owner_module() -> (Module, FuncId, FuncId) {
        let mut module = native_request_module_without_trust_vc_lane();
        let root = FuncId::new(0);
        let member = FuncId::new(1);
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(member, "checked_neg", ft, BlockId::new(0))
            .with_producer(trust_ir::Producer::TrustIr);
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
        });
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        let postcondition = module
            .proof_obligations
            .iter_mut()
            .find(|obligation| matches!(obligation.kind, ObligationKind::Postcondition))
            .expect("fixture carries a postcondition row");
        postcondition.function = Some(member);
        (module, root, member)
    }

    #[test]
    fn multi_owner_bundle_scopes_requests_lineage_and_monomorphizations_per_owner() {
        let (module, root, member) = two_owner_module();
        let member_obligations: Vec<ProofId> = module
            .proof_obligations
            .iter()
            .filter(|obligation| obligation.function == Some(member))
            .map(|obligation| obligation.id)
            .collect();
        assert_eq!(member_obligations.len(), 1, "fixture re-scopes exactly one row");

        let root_digest = digest(0x61);
        let member_digest = digest(0x62);
        // The builder validates the bundle before returning it, so `Ok` here IS
        // the statement that a two-body module produces a bundle the trust-ir
        // validator accepts — request/obligation function agreement, lineage
        // source binding and compiler-fact uniqueness included.
        let bundle = native_verification_bundle_from_module_owners(
            module,
            &[
                NativeBundleOwner { function: root, source_digest: root_digest },
                NativeBundleOwner { function: member, source_digest: member_digest },
            ],
        )
        .expect("a two-owner module builds a valid native bundle");

        // Lineage: one lowering node per body, each attesting ITS OWN source
        // digest, joined by a composition node that is the sole manifest root.
        assert_eq!(bundle.lineage.nodes.len(), 3);
        assert_eq!(bundle.lineage.nodes[0].source_module, root_digest);
        assert_eq!(bundle.lineage.nodes[1].source_module, member_digest);
        assert_eq!(bundle.lineage.nodes[1].obligations, member_obligations);
        assert_eq!(bundle.lineage.nodes[2].transform.stage, ProofTransformStage::Composition);
        assert_eq!(
            bundle.lineage.nodes[2].depends_on,
            vec![ProofLineageId::new(0), ProofLineageId::new(1)]
        );
        assert_eq!(bundle.lineage.roots, vec![ProofLineageId::new(2)]);

        // Compiler facts: one monomorphization per owner, and every obligation
        // source cites the fact for the body it is actually about.
        assert_eq!(bundle.compiler_facts.monomorphizations.len(), 2);
        assert_eq!(bundle.compiler_facts.monomorphizations[0].function, Some(root));
        assert_eq!(bundle.compiler_facts.monomorphizations[1].function, Some(member));
        assert_ne!(
            bundle.compiler_facts.monomorphizations[0].stable_digest,
            bundle.compiler_facts.monomorphizations[1].stable_digest
        );
        for source in &bundle.compiler_facts.obligation_sources {
            let expected = if source.function == Some(member) {
                NativeMonomorphizationId::new(1)
            } else {
                NativeMonomorphizationId::new(0)
            };
            assert_eq!(source.monomorphization, Some(expected));
        }

        // Primary requests remain owner-major; alternatives retain the same
        // exact owner and proof-obligation scope.
        let request_functions: Vec<Option<FuncId>> =
            bundle.requests.iter().map(NativeVerificationRequest::function).collect();
        assert_eq!(request_functions.iter().filter(|f| **f == Some(member)).count(), 2);
        assert_eq!(
            bundle
                .requests
                .iter()
                .filter(|request| {
                    matches!(request, NativeVerificationRequest::TrustMc(_))
                        && request.function() == Some(member)
                })
                .count(),
            1
        );
        assert_eq!(
            bundle
                .requests
                .iter()
                .filter(|request| {
                    matches!(request, NativeVerificationRequest::TrustWp(_))
                        && request.function() == Some(member)
                })
                .count(),
            1
        );
        assert!(request_functions.iter().any(|f| *f == Some(root)));
        for request in &bundle.requests {
            let owner = request.function().expect("every emitted request names its body");
            for obligation in request.obligations() {
                let source = bundle
                    .compiler_facts
                    .obligation_source(*obligation)
                    .expect("every request obligation has an exact source");
                assert_eq!(source.function, Some(owner));
            }
        }
    }

    /// The single-owner path is the pre-existing one, unchanged.
    ///
    /// This is the inertness gate for the whole per-owner change: with one
    /// owner the planner must produce the SAME bundle it produced before, so
    /// nothing about a normal compilation moves. Serializing both sides
    /// compares every field, not the handful an assertion list would name.
    #[test]
    fn single_owner_owners_path_is_byte_identical_to_the_root_scoped_path() {
        let legacy = native_verification_bundle_from_module(
            native_request_module_without_trust_vc_lane(),
            digest(0x31),
            FuncId::new(0),
        )
        .expect("native bundle builds");
        let owners = native_verification_bundle_from_module_owners(
            native_request_module_without_trust_vc_lane(),
            &[NativeBundleOwner { function: FuncId::new(0), source_digest: digest(0x31) }],
        )
        .expect("native bundle builds through the owners entry point");

        assert_eq!(legacy.lineage.nodes.len(), 1, "one owner emits no composition join");
        assert_eq!(legacy.lineage.roots, vec![ProofLineageId::new(0)]);
        assert_eq!(legacy.compiler_facts.monomorphizations.len(), 1);
        assert_eq!(
            serde_json::to_value(&legacy).expect("bundle serializes"),
            serde_json::to_value(&owners).expect("bundle serializes")
        );
    }

    #[test]
    fn owner_list_is_fail_closed_on_emptiness_duplication_and_foreign_rows() {
        assert_eq!(
            native_verification_bundle_from_module_owners(
                native_request_module_without_trust_vc_lane(),
                &[],
            )
            .expect_err("an owner-less bundle is refused"),
            NativeVerificationBundleBuildError::EmptyOwners
        );

        let duplicate = NativeBundleOwner { function: FuncId::new(0), source_digest: digest(0x31) };
        assert_eq!(
            native_verification_bundle_from_module_owners(
                native_request_module_without_trust_vc_lane(),
                &[duplicate, duplicate],
            )
            .expect_err("a repeated owner is refused"),
            NativeVerificationBundleBuildError::DuplicateOwner(FuncId::new(0))
        );

        // The member body exists in the module, but is NOT declared an owner:
        // its row must still abort the builder rather than ride on the root's
        // monomorphization fact.
        let (module, root, member) = two_owner_module();
        let error = native_verification_bundle_from_module_owners(
            module,
            &[NativeBundleOwner { function: root, source_digest: digest(0x61) }],
        )
        .expect_err("an undeclared owner's row is refused");
        assert!(
            matches!(
                error,
                NativeVerificationBundleBuildError::ObligationFunctionMismatch {
                    expected,
                    actual: Some(actual),
                    ..
                } if expected == root && actual == member
            ),
            "unexpected error: {error:?}"
        );
    }

    #[test]
    fn wave488_obligation_by_id_and_admission_fast_reject_match_oracle() {
        let mut module = native_request_module_without_trust_vc_lane();
        for (idx, ob) in module.proof_obligations.iter().enumerate() {
            assert_eq!(obligation_by_id(&module, ob.id).map(|o| o.id), Some(ob.id));
            let _ = idx;
        }
        if module.proof_obligations.len() >= 2 {
            module.proof_obligations.swap(0, 1);
            for ob in &module.proof_obligations {
                assert_eq!(obligation_by_id(&module, ob.id).map(|o| o.id), Some(ob.id));
            }
        }
        assert!(obligation_by_id(&module, ProofId::new(99_999)).is_none());

        let payloads = [
            r#"{"formula":{"Bool":false},"source":{"source_id":"s"}}"#,
            r#"{"trust_native_admission":{"status":"unsupported","detail":"custom reason"}}"#,
            r#"{"trust_native_admission":{"unsupported_semantics_status":"unsupported_semantics","detail":"   "}}"#,
            r#"{"trust_native_admission":{"status":"supported"}}"#,
            r#"{"\u0074rust_native_admission":{"status":"unsupported","detail":"escaped key"}}"#,
            r#"{"trust_native_admission":{"status":123}}"#,
        ];
        for (i, payload) in payloads.into_iter().enumerate() {
            let mut ob = module.proof_obligations[0].clone();
            ob.id = ProofId::new(i as u32);
            ob.formula = Some(trust_ir::ProofFormula {
                schema: "trust.test".into(),
                payload: payload.to_string(),
                smtlib: None,
                sort: None,
                bindings: Vec::new(),
            });
            let oracle = serde_json::from_str::<serde_json::Value>(payload).ok().and_then(|v| {
                let admission = v.get("trust_native_admission")?;
                let status = admission
                    .get("unsupported_semantics_status")
                    .or_else(|| admission.get("status"))
                    .and_then(serde_json::Value::as_str)?;
                if status != "unsupported" && status != "unsupported_semantics" {
                    return None;
                }
                let detail = admission
                    .get("detail")
                    .and_then(serde_json::Value::as_str)
                    .filter(|d| !d.trim().is_empty())
                    .unwrap_or("TrustMc native admission contract marked unsupported semantics");
                Some(NativeUnsupportedMode::new(
                    NativeUnsupportedModeReason::UnsupportedVerifierMode,
                    format!("{}: {}", TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION, detail),
                ))
            });
            assert_eq!(trust_mc_unsupported_semantics_mode(&ob), oracle, "payload={payload}");
        }
    }
}

//! Trust native verifier request planning over upstream TrustIr request types.
//!
//! The schema types live in `trust_ir`; this bridge only decides how a lowered
//! Trust module is split into TrustVc, TrustMc, and TrustWp request variants.

use thiserror::Error;
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
    ProofTransformStage, SourceSpan, TrustMcChcOptions, TrustMcNativeRequest,
    TrustMcRequestOptions, TrustMcVerificationMode, TrustVcNativeEvidenceBundle,
    TrustVcNativeRequest, TrustVcRequestOptions, TrustVcVerificationMode, TrustWpNativeRequest,
    TrustWpRequestOptions, TrustWpVerificationMode,
};

#[cfg(test)]
use crate::lower::TRUST_OBLIGATION_SOURCE_SCHEMA;

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
    #[error("native verification bundle validation failed")]
    Validation(Vec<NativeVerificationBundleError>),
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
/// - TrustVc owns memory-safety certificate import/merge work.
/// - TrustMc owns CHC-oriented translation/precondition/panic obligations.
/// - TrustWp owns deductive contract and translation obligations.
///
/// This planner does not manufacture solver-result evidence. It emits one
/// narrow TrustVc import-evidence row only when every certificate in that
/// request is a typed `CleanCic` certificate. Bundle validation then replays
/// each exact certificate in-process; an opaque `LeanProof`, public
/// `Discharged` label, or mixed certificate request can never cross this
/// boundary as evidence.
pub fn native_verification_bundle_from_module(
    module: Module,
    source_digest: ProofDigest,
    function: FuncId,
) -> Result<NativeVerificationBundle, NativeVerificationBundleBuildError> {
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
    require_mir_compatibility_producers(&module, function)?;
    let trust_ir_module_digest = module.stable_digest();
    if trust_ir_module_digest.algorithm != ProofDigestAlgorithm::Sha256 {
        return Err(NativeVerificationBundleBuildError::NonAuthoritativeModuleDigest {
            algorithm: trust_ir_module_digest.algorithm,
        });
    }

    let root = ProofLineageId::new(0);
    let mut lineage_node = ProofLineageNode::new(
        root,
        ProofTransform::new(
            ProofTransformStage::TrustIrLowering,
            "rustc-mir-to-trust_ir",
            "TrustIr",
            TRUST_NATIVE_REQUEST_TRANSFORM_VERSION,
        ),
        source_digest,
        trust_ir_module_digest,
    );
    lineage_node.obligations =
        module.proof_obligations.iter().map(|obligation| obligation.id).collect();
    lineage_node.certificates =
        module.proof_certificates.iter().map(ProofCertificate::lineage_ref).collect();
    lineage_node.replay = Some(trust_mc_native_admission_replay_identity(
        source_digest,
        trust_ir_module_digest,
        &lineage_node.obligations,
    ));

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![root],
    };
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        trust_ir_module_digest,
        module,
        lineage,
    );
    bundle.provenance.producer_version = TRUST_NATIVE_REQUEST_COMPILER_VERSION.to_string();
    bundle.provenance.source_language = NativeSourceLanguage::Rust;
    bundle.provenance.source_digest = Some(source_digest);
    bundle.provenance.toolchain = vec![trust_ir_bridge_tool_identity()];
    populate_compiler_facts_for_module(
        &mut bundle.compiler_facts,
        &bundle.module,
        function,
        trust_ir_module_digest,
    )?;

    // Trust (kernel-replay routing): an obligation whose module certificate is
    // CleanCic is ALREADY kernel-proved — route it to the trust_vc
    // certificate-import request (whose validation replays the certificate
    // in-process under trust-ir's clean-expr authority) regardless of kind,
    // and exclude it from the trust_mc/trust_wp solve lanes so a native
    // engine is never asked to re-derive a kernel-checked proof. Kind-based
    // ownership is unchanged for everything else, keeping request-id order
    // (trust_vc, then trust_mc, then trust_wp) stable.
    let has_clean_cic_certificate = |id: trust_ir::ProofId| {
        bundle.module.proof_certificates.iter().any(|certificate| {
            certificate.obligation == id
                && matches!(certificate.evidence, trust_ir::ProofEvidence::CleanCic { .. })
        })
    };
    let trust_vc_obligations = request_obligations(&bundle.module, |obligation| {
        trust_vc_owns_obligation(&obligation.kind) || has_clean_cic_certificate(obligation.id)
    });
    let trust_mc_obligations = request_obligations(&bundle.module, |obligation| {
        trust_mc_owns_obligation(&obligation.kind) && !has_clean_cic_certificate(obligation.id)
    });
    let trust_wp_obligations = request_obligations(&bundle.module, |obligation| {
        trust_wp_owns_obligation(&obligation.kind) && !has_clean_cic_certificate(obligation.id)
    });

    let mut next_request_id = 0;
    if !trust_vc_obligations.is_empty() {
        let trust_vc_set =
            trust_vc_obligations.iter().copied().collect::<std::collections::BTreeSet<_>>();
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
            source_digest,
            trust_ir_module_digest,
            &trust_vc_obligations,
        );
        let request_id = NativeRequestId::new(next_request_id);
        let request = TrustVcNativeRequest {
            id: request_id,
            mode: TrustVcVerificationMode::ImportProofCertificates,
            obligations: trust_vc_obligations,
            certificates,
            lineage_roots: vec![root],
            options: TrustVcRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance,
        };
        let evidence_bundle =
            trust_vc_request_has_only_clean_cic_certificates(&bundle.module, &request)
                .then(|| trust_vc_evidence_bundle_for_request(&request, trust_ir_module_digest));
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
            source_digest,
            trust_ir_module_digest,
            &trust_mc_obligations,
        );
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(next_request_id),
            mode: TrustMcVerificationMode::Chc,
            function,
            obligations: trust_mc_obligations,
            lineage_roots: vec![root],
            options: trust_mc_chc_request_options(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance,
        }));
        next_request_id += 1;
    }
    if !trust_wp_obligations.is_empty() {
        let provenance = trust_wp_request_provenance(
            &bundle.module,
            &bundle.compiler_facts,
            source_digest,
            trust_ir_module_digest,
            &trust_wp_obligations,
        );
        bundle.requests.push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
            id: NativeRequestId::new(next_request_id),
            mode: TrustWpVerificationMode::WeakestPrecondition,
            function,
            obligations: trust_wp_obligations,
            lineage_roots: vec![root],
            options: TrustWpRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance,
        }));
    }

    if bundle.requests.is_empty() {
        return Err(NativeVerificationBundleBuildError::EmptyRequests);
    }
    bundle.validate().map_err(NativeVerificationBundleBuildError::Validation)?;
    Ok(bundle)
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

fn trust_ir_bridge_tool_identity() -> NativeToolIdentity {
    NativeToolIdentity::new("TrustIr")
        .with_version(TRUST_NATIVE_REQUEST_COMPILER_VERSION)
        .with_revision(TRUST_NATIVE_REQUEST_COMPILER_REVISION)
}

fn populate_compiler_facts_for_module(
    compiler_facts: &mut NativeCompilerFacts,
    module: &Module,
    function: FuncId,
    trust_ir_module_digest: ProofDigest,
) -> Result<(), NativeVerificationBundleBuildError> {
    let monomorphization = native_monomorphization_fact(module, function, trust_ir_module_digest);
    let monomorphization_id = monomorphization.id;
    compiler_facts.monomorphizations = vec![monomorphization];
    compiler_facts.obligation_sources =
        obligation_sources_for_module(module, function, monomorphization_id)?;
    Ok(())
}

fn native_monomorphization_fact(
    module: &Module,
    function: FuncId,
    trust_ir_module_digest: ProofDigest,
) -> NativeMonomorphizationFact {
    let source_item = module
        .function_by_id(function)
        .map(|function| function.name.clone())
        .unwrap_or_else(|| format!("function#{}", function.index()));
    NativeMonomorphizationFact {
        id: NativeMonomorphizationId::new(0),
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

fn obligation_sources_for_module(
    module: &Module,
    function: FuncId,
    monomorphization: NativeMonomorphizationId,
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
            if obligation.function != Some(function) {
                return Err(NativeVerificationBundleBuildError::ObligationFunctionMismatch {
                    obligation: obligation.id,
                    expected: function,
                    actual: obligation.function,
                });
            }
            Ok(NativeObligationSource {
                obligation: obligation.id,
                public_obligation_id: public.obligation_id.clone(),
                function: obligation.function,
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

fn native_obligation_cause(kind: &ObligationKind) -> NativeObligationCause {
    match kind {
        ObligationKind::Precondition => NativeObligationCause::Precondition,
        ObligationKind::Postcondition => NativeObligationCause::Postcondition,
        ObligationKind::LoopInvariant => NativeObligationCause::Assert,
        ObligationKind::TypeInvariant | ObligationKind::RefinementType => {
            NativeObligationCause::Assert
        }
        ObligationKind::MemorySafety => NativeObligationCause::BorrowCheck,
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

fn trust_mc_chc_request_options() -> TrustMcRequestOptions {
    TrustMcRequestOptions {
        chc: TrustMcChcOptions { emit_horn_clauses: true, ..TrustMcChcOptions::default() },
        ..TrustMcRequestOptions::default()
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

fn trust_wp_request_provenance(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    source_digest: ProofDigest,
    trust_ir_module_digest: ProofDigest,
    obligations: &[ProofId],
) -> NativeRequestProvenance {
    NativeRequestProvenance::trust_wp(NativeToolIdentity::new("trust_wp"))
        .with_solver(NativeToolIdentity::new("ay"))
        .with_replay(
            // Wire-format engine/invocation labels: the canonical spelling is
            // the hyphenated `trust-wp-core.…` — it is what trust-wp-core's
            // native pure replay reports as its solver engine
            // (`proof_result_metadata_for_obligation`) and what the trust-wp
            // verifier's fail-closed result gate compares against
            // (`expected \`trust-wp-core.native-pure-replay\``). The
            // underscore `trust_wp-core.…` form was a blanket identifier
            // rename leaking into a string literal. (The schema constant
            // `trust_wp.native-pure-replay.v1` is the deliberate underscore
            // exception; it is unrelated to this engine label.)
            ProofReplayIdentity::new(
                "trust-wp-core.native-pure-replay",
                "trust-wp-core native-bundle --wp",
            )
            .with_transcript_digest(native_replay_transcript_digest(
                "trust_wp",
                source_digest,
                trust_ir_module_digest,
                obligations,
            )),
        )
        .with_replay_context(native_replay_context(module, compiler_facts, obligations))
}

fn native_replay_context(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    obligations: &[ProofId],
) -> NativeReplayContext {
    let mut context = NativeReplayContext::default();
    for (index, obligation_id) in obligations.iter().enumerate() {
        let Some(obligation) =
            module.proof_obligations.iter().find(|obligation| obligation.id == *obligation_id)
        else {
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
        let Some(obligation) =
            module.proof_obligations.iter().find(|obligation| obligation.id == *obligation_id)
        else {
            continue;
        };
        if let Some(unsupported) = trust_mc_unsupported_semantics_mode(obligation) {
            context = context.with_unsupported_mode(unsupported);
        }
    }
    context
}

fn trust_mc_unsupported_semantics_mode(
    obligation: &trust_ir::ProofObligation,
) -> Option<NativeUnsupportedMode> {
    let formula = obligation.formula.as_ref()?;
    let value: serde_json::Value = serde_json::from_str(&formula.payload).ok()?;
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
    matches!(kind, ObligationKind::MemorySafety)
}

fn trust_mc_owns_obligation(kind: &ObligationKind) -> bool {
    // Trust (trust-ir-spine item T1): the new routing-grade panic-class kinds
    // (`ArithmeticSafety`, `BoundsCheck`) are panic-freedom obligations — trust-mc
    // owns them exactly as it owns `PanicFreedom`, preserving current routing.
    matches!(
        kind,
        ObligationKind::TranslationValidation
            | ObligationKind::Precondition
            | ObligationKind::PanicFreedom
            | ObligationKind::ArithmeticSafety
            | ObligationKind::BoundsCheck
    )
}

fn trust_wp_owns_obligation(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
            | ObligationKind::TypeInvariant
            | ObligationKind::RefinementType
            | ObligationKind::TranslationValidation
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
    /// `native_bundle_builder_emits_typed_trust_vc_trust_mc_trust_wp_requests`.
    fn native_request_module_without_trust_vc_lane() -> Module {
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
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(function);

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
        });

        module
    }

    fn kernel_certified_three_suite_module() -> Module {
        let mut module = Module::new("trust_native_kernel_three_suite_bundle");
        let file = module.intern_file("src/kernel_three_suite.rs");
        let function_id = FuncId::new(0);
        let ft = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        let mut function = Function::new(function_id, "kernel_checked", ft, BlockId::new(0))
            .with_producer(trust_ir::Producer::TrustIr);
        function.blocks.push(Block {
            id: BlockId::new(0),
            params: Vec::new(),
            body: vec![InstrNode::new(Inst::Return { values: Vec::new() })],
        });
        module.add_function(function);

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
                "trust-wp postcondition",
                ProofFormula::new("TrustWpPureExprV1", "true"),
                "trust_ir-native-trust-wp-request-2-proof-2",
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
                            format!("kernel-three-suite:source:{index}"),
                            format!("kernel-three-suite:assertion:{index}"),
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
        let file = module.intern_file("src/lib.rs");
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
                "public_obligation_id": format!(
                    "trust-native-request:checked_add:public:{}",
                    obligation.index()
                ),
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
    fn native_bundle_builder_emits_typed_trust_vc_trust_mc_trust_wp_requests() {
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

        // trust_mc + trust_wp lanes: with the unreplayable trust_vc lane
        // removed, the planned bundle is admissible end to end.
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
        assert_eq!(bundle.requests.len(), 3);
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
            NativeVerificationRequest::TrustWp(request) => {
                assert_eq!(request.id, NativeRequestId::new(2));
                assert_eq!(request.mode, TrustWpVerificationMode::WeakestPrecondition);
                assert_eq!(request.function, FuncId::new(0));
                assert_eq!(
                    request.obligations,
                    vec![ProofId::new(1), ProofId::new(2), ProofId::new(3)]
                );
                assert!(request.options.emit_verification_conditions);
                assert_eq!(request.provenance.expected_verifier.name, "trust_wp");
                assert!(!request.provenance.solvers.is_empty());
                // Pins the canonical hyphenated engine label that trust-wp's
                // fail-closed native pure replay result gate expects.
                assert_eq!(
                    request.provenance.replay.as_ref().map(|replay| replay.engine.as_str()),
                    Some("trust-wp-core.native-pure-replay")
                );
                assert_eq!(request.provenance.replay_context.atoms.len(), 3);
            }
            other => panic!("expected TrustWp request, got {other:?}"),
        }

        bundle.validate().expect("native bundle validates");
    }

    #[test]
    fn kernel_certified_contract_routes_to_trust_vc_with_typed_import_evidence() {
        let module = kernel_certified_three_suite_module();
        let certificate_ref = module.proof_certificates[0].lineage_ref();
        let bundle = native_verification_bundle_from_module(module, digest(0x42), FuncId::new(0))
            .expect("kernel-certified three-suite bundle builds");

        assert_eq!(bundle.requests.len(), 3);
        let NativeVerificationRequest::TrustVc(trust_vc) = &bundle.requests[0] else {
            panic!("CleanCic-certified contract must route to TrustVc import");
        };
        assert_eq!(trust_vc.id, NativeRequestId::new(0));
        assert_eq!(trust_vc.obligations, vec![ProofId::new(0)]);
        assert_eq!(trust_vc.certificates, vec![certificate_ref.clone()]);
        assert!(matches!(bundle.requests[1], NativeVerificationRequest::TrustMc(_)));
        assert!(matches!(bundle.requests[2], NativeVerificationRequest::TrustWp(_)));

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
        let source_file = module.intern_file("src/lib.rs");
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
                "public_obligation_id": "trust-native-request:checked_add:public:0",
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
                "public_obligation_id": "public:test::checked_add:requires:0",
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
        // `native_bundle_builder_emits_typed_trust_vc_trust_mc_trust_wp_requests`
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
        assert_eq!(json["requests"].as_array().map(Vec::len), Some(3));
        assert_eq!(json["compiler_facts"]["monomorphizations"].as_array().map(Vec::len), Some(1));
        assert_eq!(
            json["compiler_facts"]["obligation_sources"][0]["facts"].as_array().map(Vec::len),
            Some(1)
        );
        assert_eq!(json["requests"][0]["TrustMc"]["mode"], json!("Chc"));
        assert_eq!(json["requests"][1]["TrustMc"]["mode"], json!("Chc"));
        assert_eq!(json["requests"][2]["TrustWp"]["mode"], json!("WeakestPrecondition"));
        assert_eq!(json["requests"][0]["TrustMc"]["obligations"], json!([1]));
        assert_eq!(json["requests"][1]["TrustMc"]["obligations"], json!([2]));
        assert_eq!(json["requests"][2]["TrustWp"]["obligations"], json!([1, 2, 3]));
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
            json["requests"][2]["TrustWp"]["provenance"]["expected_verifier"]["name"],
            "trust_wp"
        );

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
                "public_obligation_id": "trust-native-request:checked_add:public:1",
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
}

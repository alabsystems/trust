//! Identity correspondence at the existing F1 Compiler boundary; no proof authority.

use trust_ir::{
    FuncId, Module, NativeAdapterInput, NativeBundleProducer, NativeRequestId,
    NativeVerificationBundle, ProofDigest, ProofId,
};

use super::{F1Refusal, F1Shipped};

/// One original request's exact function in the compilation input.
/// These are derived identities, never a verdict or a codegen license.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct NativeQuestionFunctionBinding {
    pub request: NativeRequestId,
    pub request_digest: ProofDigest,
    pub function: FuncId,
    pub function_body_digest: ProofDigest,
    pub obligations: Vec<ProofId>,
}

#[derive(Debug, Clone, serde::Serialize)]
pub(super) struct Correspondence {
    pub native_bundle_digest: ProofDigest,
    pub compiled_executable_digest: ProofDigest,
    pub functions: Vec<NativeQuestionFunctionBinding>,
}

/// An ordinary F1 shipping result beside its diagnostic question identities.
/// Only the unchanged output gate authorizes the object. The correspondence
/// checks no solver evidence, grants no source authority, and promotes no row.
#[derive(Debug, Clone)]
pub struct F1NativeQuestionCompilation {
    pub shipped: F1Shipped,
    correspondence: Correspondence,
}

impl F1NativeQuestionCompilation {
    pub(super) fn new(shipped: F1Shipped, correspondence: Correspondence) -> Self {
        Self { shipped, correspondence }
    }

    pub fn native_bundle_digest(&self) -> ProofDigest {
        self.correspondence.native_bundle_digest
    }

    pub fn compiled_executable_digest(&self) -> ProofDigest {
        self.correspondence.compiled_executable_digest
    }

    pub fn functions(&self) -> &[NativeQuestionFunctionBinding] {
        &self.correspondence.functions
    }
}

fn refusal(reason: impl Into<String>) -> F1Refusal {
    F1Refusal::Binding(format!("native question/function digest correspondence: {}", reason.into()))
}

pub(super) fn bind(
    compiled: &Module,
    questions: &NativeVerificationBundle,
) -> Result<Correspondence, F1Refusal> {
    if questions.producer != NativeBundleProducer::TRust
        || !matches!(questions.input, NativeAdapterInput::TrustIrModule)
    {
        return Err(refusal("requires the direct TrustIR question input"));
    }
    // Probe the existing complete wire carrier before any digest API. Neither
    // a partial image nor an unencodable body has an identity to compare.
    for (label, module) in [("question", &questions.module), ("compiled", compiled)] {
        if let Some(error) = trust_ir_build::wire_identity_blocker(module) {
            return Err(refusal(format!("{label} image has no wire identity: {error:?}")));
        }
        let errors = trust_ir_build::validate_module(module);
        if !errors.is_empty() {
            return Err(refusal(format!("invalid {label} image: {errors:?}")));
        }
    }
    questions.validate().map_err(|errors| refusal(format!("invalid native bundle: {errors:?}")))?;
    if questions.requests.is_empty() {
        return Err(refusal("native input contains no requests"));
    }
    // The body digest intentionally does not bind type/global definitions.
    // Retain the existing full executable identity too, without stripping
    // summaries, annotations, target/layout data, or any executable field.
    // Proof sidecars and codegen licenses follow the IR-owned projection.
    let executable = compiled.executable_content_digest_v1();
    if questions.module.executable_content_digest_v1() != executable {
        return Err(refusal("question and compiled executable images differ"));
    }
    let mut functions = Vec::with_capacity(questions.requests.len());
    for request in &questions.requests {
        let function =
            request.function().ok_or_else(|| refusal("request has no function scope"))?;
        if request.obligations().is_empty() {
            return Err(refusal("request has no obligation inventory"));
        }
        let expected = questions.module.function_body_digest(function).map_err(refusal)?;
        let actual = compiled.function_body_digest(function).map_err(refusal)?;
        if expected != actual {
            return Err(refusal(format!(
                "request {} function {} body differs",
                request.id(),
                function
            )));
        }
        if compiled.function_by_id(function).is_none_or(|body| body.is_declaration()) {
            return Err(refusal(format!("request {} owns no compiled body", request.id())));
        }
        functions.push(NativeQuestionFunctionBinding {
            request: request.id(),
            request_digest: request.stable_digest(),
            function,
            function_body_digest: actual,
            obligations: request.obligations().to_vec(),
        });
    }
    Ok(Correspondence {
        native_bundle_digest: questions.stable_digest(),
        compiled_executable_digest: executable,
        functions,
    })
}

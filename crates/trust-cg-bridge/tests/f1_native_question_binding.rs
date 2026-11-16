//! PKG-CV1: exact native questions at F1's actual Compiler consumer.
//! The original fcba4a4db90d THIR capture is unchanged (SHA256
//! 8636e43749140b8492565cede3fa6562dfe6cac991c005de014f92adfa370239).
//! Native WP results remain Trusted; question correspondence grants no proof.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use sha2::{Digest, Sha256};
use trust_cg_bridge::call_event::{FnPlacement, ProducerBody, ProducerModule};
use trust_cg_bridge::compiled_object::RelocationModel;
use trust_cg_bridge::f1_compile::{
    F1CompileConfig, F1CompileInput, F1OptLevel, F1Refusal, F1Target,
    compile_and_verify_trust_ir_module_with_native_questions,
};
use trust_cg_bridge::verify_output::EmitPolicy;
use trust_ir::{Module, NativeVerificationBundle};
use trust_wp_lib::VerifyBundleStatus;
use trust_wp_lib::trust_ir_body::{replay_trust_ir_body_contracts, verify_trust_ir_body_contracts};

fn questions() -> NativeVerificationBundle {
    let captured = include_bytes!("data/direct-shift-mask-shadow.json");
    assert_eq!(
        format!("{:x}", Sha256::digest(captured)),
        "8636e43749140b8492565cede3fa6562dfe6cac991c005de014f92adfa370239",
        "the original compiler capture must remain unchanged"
    );
    let original: serde_json::Value = serde_json::from_slice(captured).unwrap();
    let native = &original["native_wp"];
    assert_eq!(native["status"], "questions");
    assert_eq!(native["authority"], "NONE");
    let bundle: NativeVerificationBundle =
        serde_json::from_value(native["bundle"].clone()).unwrap();
    bundle.validate().unwrap();
    assert!(
        bundle
            .module
            .proof_obligations
            .iter()
            .all(|row| row.status == trust_ir::ProofStatus::Pending)
    );
    assert!(bundle.module.proof_certificates.is_empty());
    bundle
}

fn compile(
    compiled: &Module,
    native: &NativeVerificationBundle,
    policy: EmitPolicy,
) -> Result<trust_cg_bridge::f1_compile::F1NativeQuestionCompilation, F1Refusal> {
    let producer = Arc::new(compiled.clone());
    let producers = [ProducerModule::named_by_symbols(Arc::clone(&producer))];
    let bodies = producer
        .functions
        .iter()
        .filter(|f| !f.is_declaration())
        .map(|f| (f.name.clone(), ProducerBody { producer: 0, func: f.id }))
        .collect::<BTreeMap<_, _>>();
    let placements = producer
        .functions
        .iter()
        .map(|f| (f.name.clone(), FnPlacement::from_scalar_signature(&producer, f).unwrap()))
        .collect::<BTreeMap<_, _>>();
    let config = F1CompileConfig {
        target: F1Target::Aarch64AppleDarwin,
        force_frame_pointers: false,
        opt_level: F1OptLevel::O0,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    compile_and_verify_trust_ir_module_with_native_questions(
        &F1CompileInput {
            m_cg: compiled,
            producers: &producers,
            bodies: &bodies,
            placements: &placements,
            policy,
            config: &config,
        },
        native,
    )
}

#[test]
fn actual_native_questions_and_compiled_function_share_ir_owned_digests() {
    let native = questions();
    let original = native.clone();
    let results = verify_trust_ir_body_contracts(&native).unwrap();
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|row| row.status == VerifyBundleStatus::Verified));
    replay_trust_ir_body_contracts(&native, &results).unwrap();
    let strict = compile(&native.module, &native, EmitPolicy::StrictProvenOnly).unwrap_err();
    assert!(matches!(strict, F1Refusal::Policy(_)), "{strict}");
    assert!(strict.to_string().contains("not closed-[PROVED]"), "{strict}");
    let output = compile(&native.module, &native, EmitPolicy::AllowUnknown).unwrap();
    assert!(!output.shipped.object.is_empty());
    assert_eq!(output.native_bundle_digest(), native.stable_digest());
    assert_eq!(output.compiled_executable_digest(), native.module.executable_content_digest_v1());
    assert_eq!(output.functions().len(), 4);
    for (binding, request) in output.functions().iter().zip(&native.requests) {
        assert_eq!(binding.request, request.id());
        assert_eq!(binding.request_digest, request.stable_digest());
        assert_eq!(Some(binding.function), request.function());
        assert_eq!(binding.obligations, request.obligations());
        assert_eq!(
            binding.function_body_digest,
            native.module.function_body_digest(binding.function).unwrap()
        );
    }
    assert_eq!(native, original);
}

#[test]
fn changed_verified_function_is_refused_even_when_unknown_output_would_ship() {
    let native = questions();
    let results = verify_trust_ir_body_contracts(&native).unwrap();
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|row| row.status == VerifyBundleStatus::Verified));
    replay_trust_ir_body_contracts(&native, &results).unwrap();
    let mut compiled = native.module.clone();
    let node = compiled.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|node| {
            matches!(node.inst, trust_ir::Inst::Const { value: trust_ir::Constant::Int(0), .. })
        })
        .unwrap();
    let trust_ir::Inst::Const { value, .. } = &mut node.inst else { unreachable!() };
    *value = trust_ir::Constant::Int(999);
    assert!(trust_ir_build::validate_module(&compiled).is_empty());
    assert_ne!(
        compiled.function_body_digest(compiled.functions[0].id).unwrap(),
        native.module.function_body_digest(native.module.functions[0].id).unwrap()
    );
    let refusal = compile(&compiled, &native, EmitPolicy::AllowUnknown).unwrap_err();
    assert!(matches!(refusal, F1Refusal::Binding(_)), "{refusal}");
    assert!(refusal.to_string().contains("executable images differ"), "{refusal}");
}

#[test]
fn unchanged_body_does_not_hide_a_changed_module_type_context() {
    let native = questions();
    let mut compiled = native.module.clone();
    compiled.func_types.push(compiled.func_types[0].clone());
    assert!(trust_ir_build::validate_module(&compiled).is_empty());
    assert_eq!(
        compiled.function_body_digest(compiled.functions[0].id).unwrap(),
        native.module.function_body_digest(native.module.functions[0].id).unwrap()
    );
    assert!(matches!(
        compile(&compiled, &native, EmitPolicy::AllowUnknown),
        Err(F1Refusal::Binding(_))
    ));
}

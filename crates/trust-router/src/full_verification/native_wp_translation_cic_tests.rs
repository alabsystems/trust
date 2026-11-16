//! Close the production Root subject with Clean's exact canonical-model proof.
//! The checked mathematics remains unbound and never changes routed evidence.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_olean::semr_native_execution::{
    NativeWpTranslationPacket, UnboundNativeWpTranslationContext,
};
use clean_olean::{ClosedRecheckOptions, load_module_with_deps, reference_base_closed};
use trust_ir_build::clean_kernel::{self, Environment, Expr, Name};

use super::*;
use crate::full_verification::native_trust_ir::check_native_wp_translation_mathematics;

fn packet_constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(&format!("SemRRootUnsignedPacket.{name}")), vec![])
}

fn compile_translation(scratch: &Path, canonical: &Path) {
    let source = clean_olean::test_support::fixture_root().join("semr_unsigned_translation");
    let lean_path = std::env::join_paths([canonical, scratch]).unwrap();
    for module in [
        "SemRNativeUnsignedTranslation",
        "SemRNativeUnsignedFamily",
        "SemRRootUnsignedPacketData",
        "SemRRootUnsignedPacket",
    ] {
        let input = scratch.join(format!("{module}.lean"));
        std::fs::copy(source.join(format!("{module}.lean")), &input).unwrap();
        let output = Command::new(clean_olean::pinned_lean_binary().unwrap())
            .args(["--threads=1", "--tstack=65536"])
            .env("LEAN_PATH", &lean_path)
            .arg("--root")
            .arg(scratch)
            .arg("-o")
            .arg(input.with_extension("olean"))
            .arg(&input)
            .output()
            .unwrap();
        std::fs::write(input.with_extension("stdout"), &output.stdout).unwrap();
        std::fs::write(input.with_extension("stderr"), &output.stderr).unwrap();
        assert!(
            output.status.success(),
            "{module}:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn actual_checked_wp_question_has_a_closed_translation_and_cannot_be_rebound() {
    let (public, native) = unsigned_fixture();
    let original = (public.clone(), native.clone());
    let (evidence, wp) = checked(&public, &native);
    let original_evidence = evidence.clone();
    let admitted = ValidatedNativeBundle::new(&native).unwrap();
    let semantics = validate_module_report(&native.module);
    let subject = native_wp_translation_subject(
        &admitted,
        &semantics,
        &public,
        &public.obligations[0],
        &evidence,
        &wp,
    )
    .unwrap();

    // Construct a valid changed question before the expensive replay. Use
    // the owning factory so its lineage targets the new complete module.
    let mut changed_module = native.module.clone();
    changed_module.functions[0].name.push_str("_retained_metadata_changed");
    let changed_native = native_verification_bundle_from_module(
        changed_module,
        native_trust_ir_digest(1),
        trust_ir::FuncId::new(0),
    )
    .unwrap();
    let changed_admitted = ValidatedNativeBundle::new(&changed_native).unwrap();
    let changed_semantics = validate_module_report(&changed_native.module);
    assert!(changed_semantics.is_ok(), "{:?}", changed_semantics.errors());

    // Compile only the new translation artifact above the canonical cached
    // fixture. The original concrete packet is not an imported premise.
    let canonical = clean_olean::test_support::compiled_fixture_dir("semr_wp");
    let scratch = tempfile::Builder::new().prefix("root-wp-translation-").tempdir().unwrap().keep();
    compile_translation(&scratch, &canonical);
    let mut environment = Environment::for_lean_replay();
    let paths: Vec<PathBuf> =
        vec![canonical, scratch.clone(), clean_olean::require_pinned_lean_lib_path().unwrap()];
    load_module_with_deps(&mut environment, "SemRRootUnsignedPacket", &paths).unwrap();
    let targets: BTreeSet<_> = [
        "SemRRootUnsignedPacket.translation_certificate",
        "SemRRootUnsignedPacket.original_execution",
        "SemRRootUnsignedPacket.full_u64_return",
        "SemRNativeUnsignedFamily.select_return_original_translation",
        "SemRNativeUnsignedTranslation.TranslationCertificate",
        "SemRNativeUnsignedTranslation.certificate_sound",
        "SemRNativeUnsignedTranslation.originalWpTranslation",
        "SemRNativeExecutionClaim.originalExecution",
        "SemRNativeExecutionClaim.originalContractHolds",
        "SemRNativeExecutionClaim.originalExecution_model_iff",
        "SemRNativeExecutionClaim.originalExecution_of_surjective",
        "SemRBooleanClaim.contractTypedEnv",
        "SemRBooleanClaim.checkedText",
        "SemRBooleanClaim.checkedTypedJson",
        "SemR.runBlob",
    ]
    .into_iter()
    .map(Name::from_string)
    .collect();
    let base =
        reference_base_closed(&environment, &targets, &ClosedRecheckOptions::default()).unwrap();
    assert!(base.report.passed() && base.entry_refusals.is_empty(), "{:?}", base.entry_refusals);
    assert!(targets.iter().all(|name| base.admitted.contains(name)));
    assert!(
        base.report.axioms_admitted.iter().all(|name| [
            "Classical.choice",
            "Quot.sound",
            "propext"
        ]
        .contains(&name.as_str()))
    );
    eprintln!(
        "Root exact WP question: {}; artifact {}",
        base.report.verdict_sentence(),
        scratch.display()
    );
    base.kernel()
        .check_closed_term(
            &subject.original.expected_goal(),
            &packet_constant("original_execution"),
        )
        .unwrap();
    let context = UnboundNativeWpTranslationContext::from_reference_base(base).unwrap();
    let packet = NativeWpTranslationPacket {
        context: context.digest(),
        proposed_vc: packet_constant("vcJson"),
        proof: packet_constant("translation_certificate"),
    };
    let mathematics = check_native_wp_translation_mathematics(
        &admitted,
        &semantics,
        &public,
        &public.obligations[0],
        &evidence,
        &wp,
        &context,
        &packet,
    )
    .unwrap();
    assert_eq!(mathematics.mathematics().subject().original, subject.original);
    assert_eq!(mathematics.mathematics().subject().vc_bytes, subject.vc_bytes);
    assert_eq!(mathematics.mathematics().subject().vc_bindings, subject.vc_bindings);

    // Reuse the immutable checked fact without another solver or CIC replay.
    for _ in 0..16 {
        assert!(mathematics.clone().matches(
            &public,
            &native,
            &public.obligations[0],
            &evidence,
            &context
        ));
    }
    let mut changed_public = public.clone();
    let mut bindings: Vec<(String, trust_ir::proof::ClauseBinding)> =
        serde_json::from_str(&changed_public.contracts[0].metadata[0].value).unwrap();
    bindings[3].1.place = trust_ir::proof::ClausePlace::Param { index: 1 };
    changed_public.contracts[0].metadata[0].value = serde_json::to_string(&bindings).unwrap();
    assert!(!mathematics.matches(
        &changed_public,
        &native,
        &changed_public.obligations[0],
        &evidence,
        &context
    ));
    assert!(
        check_native_wp_translation_mathematics(
            &admitted,
            &semantics,
            &changed_public,
            &changed_public.obligations[0],
            &evidence,
            &wp,
            &context,
            &packet,
        )
        .is_err()
    );

    assert!(!mathematics.matches(
        &public,
        &changed_native,
        &public.obligations[0],
        &evidence,
        &context
    ));
    assert!(
        check_native_wp_translation_mathematics(
            &changed_admitted,
            &changed_semantics,
            &public,
            &public.obligations[0],
            &evidence,
            &wp,
            &context,
            &packet,
        )
        .is_err()
    );

    let wrong_proof =
        NativeWpTranslationPacket { proof: packet_constant("full_u64_return"), ..packet.clone() };
    assert!(
        matches!(
            context.check(&subject, &wrong_proof),
            Err(clean_olean::semr_native_execution::NativeExecutionRefusal::Proof(
                clean_kernel::ReferenceRefusal::Kernel(
                    clean_kernel::env::EnvError::TypeCheckFailed {
                        source: clean_kernel::tc::TypeError::TypeMismatch { .. },
                        ..
                    }
                )
            ))
        ),
        "wrong theorem must produce TypeMismatch, not a resource refusal"
    );
    assert!(
        check_native_wp_translation_mathematics(
            &admitted,
            &semantics,
            &public,
            &public.obligations[0],
            &evidence,
            &wp,
            &context,
            &wrong_proof,
        )
        .is_err()
    );
    assert_eq!((public, native), original);
    assert_eq!(evidence, original_evidence, "unbound mathematics cannot promote the routed row");
}

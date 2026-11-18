//! Exercise the production replay with real checked source and the complete
//! production module. Mutation controls retain the positive fixture's proofs.

use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
use clean_compiler::pass_manager::{PipelineConfig, compile_lcnf_to_trust_ir_with_report};
use clean_kernel::{BinderInfo, Expr};

use super::*;

struct Fixture {
    module: Module,
    environment: Environment,
    expected: Vec<(String, Name)>,
    report: TvMintReport,
}

#[test]
fn claim_free_stripping_removes_instruction_channels_without_changing_computation() {
    use trust_ir::proof::ProofContext;
    use trust_ir::{Inst, ProofAnnotation, ProofId, Ty};

    for has_foreign_ids in [false, true] {
        let mut builder = trust_ir_build::ModuleBuilder::new("instruction-proof-stripping");
        let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut function = builder.function("callee", signature);
        let entry = function.create_block();
        let argument = function.add_block_param(entry, Ty::U64);
        function.switch_to_block(entry);
        function.ret(vec![argument]);
        function.build();
        let mut function = builder.function("caller", signature);
        let entry = function.create_block();
        let argument = function.add_block_param(entry, Ty::U64);
        function.switch_to_block(entry);
        let result = function.call(FuncId::new(0), vec![argument]);
        function.ret(vec![result]);
        function.build();
        let mut module = builder.build().expect("typed two-function computational fixture");
        let call = module.functions[1].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, Inst::Call { .. }))
            .unwrap();
        call.proofs.push(ProofAnnotation::Pure);
        call.proof_context = Some(if has_foreign_ids {
            ProofContext { assumes: vec![ProofId::new(0)], establishes: vec![ProofId::new(0)] }
        } else {
            ProofContext::default()
        });
        let computation = |subject: &Module| {
            subject
                .functions
                .iter()
                .flat_map(|function| &function.blocks)
                .flat_map(|block| &block.body)
                .map(|node| (node.inst.clone(), node.results.clone()))
                .collect::<Vec<_>>()
        };
        let before = computation(&module);
        // These synthetic annotations are DATA, never replay evidence. The
        // actual collector still validates and rechecks before stripping.
        strip_for_general(&mut module).expect("stripped computational module validates");
        assert_eq!(computation(&module), before);
        assert!(module.functions.iter().all(|function| {
            function.body_gate == Some(BodyGate::Ungated)
                && function
                    .blocks
                    .iter()
                    .flat_map(|block| &block.body)
                    .all(|node| node.proofs.is_empty() && node.proof_context.is_none())
        }));
    }
}

fn compile(source: &str, names: &[&str]) -> Fixture {
    let mut environment = Environment::with_prelude();
    environment.init_io_ops().expect("initialize the actual Clean prelude");
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let parsed =
        clean_parser::parse_file_with_tactics(source, &patterns).expect("parse the actual source");
    let mut context = clean_elab::FileContext::new();
    for declaration in parsed {
        let processed = clean_elab::preprocess_decl_with_context(&declaration, &mut context);
        let registered = clean_elab::elaborate_decl_and_register_with_context_and_warning(
            &mut environment,
            &processed,
            &mut context,
        )
        .expect("elaborate and kernel-check the actual source");
        assert!(registered.warning.is_none(), "source must require no trust warning");
    }
    let mut declarations = Vec::new();
    let mut expected = Vec::new();
    for name in names {
        let source = Name::from_string(name);
        let declaration = clean_compiler::constant_to_decl(
            &environment,
            environment.get_const(&source).expect("actual source definition"),
        )
        .expect("actual source lowers")
        .expect("computational source");
        expected.push((clean_compiler::emit_trust_ir_link::link_symbol(&declaration.name), source));
        declarations.push(declaration);
    }
    let (module, report) = compile_lcnf_to_trust_ir_with_report(
        &declarations,
        &environment,
        &PipelineConfig::default(),
        &TrustIrConfig {
            runtime_lowering: RuntimeLowering::ExternCalls,
            certify_translation: true,
            ..Default::default()
        },
    )
    .expect("the canonical producer compiles the actual source");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "complete actual producer module: {errors:?}");
    assert!(report.refused.is_empty(), "{report:?}");
    Fixture { module, environment, expected, report }
}

#[test]
fn checked_source_replay_binds_all_widths_and_rejects_transport_mutations() {
    let source = [8, 16, 32, 64]
        .map(|width| {
            format!(
                "def replay{width} (a b c : UInt{width}) : UInt{width} := \
             if (a - b) < c then a + 1 else b\n"
            )
        })
        .concat()
        + "def replayTwin (a b c : UInt8) : UInt8 := if (a - b) < c then a + 1 else b\n";
    let f = compile(&source, &["replay8", "replay16", "replay32", "replay64"]);
    assert_eq!(f.report.certified.len(), 4, "{:#?}", f.report);
    assert_eq!(f.report.source_equations.len(), 4);
    let module_before = f.module.clone();
    let report_before = f.report.clone();
    assert_eq!(recheck(&f.module, &f.environment, &f.expected, &f.report), Ok(4));
    assert_eq!(f.module, module_before, "replay cannot mutate its actual subject");
    assert_eq!(f.report, report_before, "transport data is read-only");

    let reject = |label: &str, report: &TvMintReport| {
        assert!(
            recheck(&f.module, &f.environment, &f.expected, report).is_err(),
            "accepted corrupt transport: {label}"
        );
    };
    let mut changed = f.report.clone();
    changed.source_equations.clear();
    changed.final_module_digest = None;
    reject("all original-source proofs omitted", &changed);
    changed = f.report.clone();
    changed.source_equations.pop();
    reject("one original-source proof omitted", &changed);
    changed = f.report.clone();
    changed.source_equations.push(changed.source_equations[0].clone());
    reject("duplicate original-source theorem", &changed);
    changed = f.report.clone();
    changed.source_equations[0].function = FuncId::new(u32::MAX);
    reject("unmapped emitted function", &changed);
    changed = f.report.clone();
    changed.source_equations[0].source = Name::from_string("replayTwin");
    reject("producer-selected same-valued source", &changed);
    changed = f.report.clone();
    changed.source_equations[0].type_ = Expr::const_str("True");
    reject("different theorem judgment", &changed);
    changed = f.report.clone();
    changed.source_equations[0].value = Expr::const_str("True.intro");
    reject("proof of a different goal", &changed);
    changed = f.report.clone();
    changed.source_equations[0].level_params.push(Name::from_string("unexpectedUniverse"));
    reject("changed theorem universe parameters", &changed);
    changed = f.report.clone();
    changed.source_equations[0].source_closure_digest[0] ^= 1;
    reject("changed source closure", &changed);
    changed = f.report.clone();
    changed.source_equations[0].equation_closure_digest[0] ^= 1;
    reject("changed producer-named theorem closure", &changed);
    changed = f.report.clone();
    changed.source_equations[0].theorem_name = f.expected[0].1.clone();
    reject("theorem colliding with accepted original source", &changed);
    changed = f.report.clone();
    changed.source_equations[0].theorem_name = Name::from_string("renamedProducerTheorem");
    reject("producer theorem renamed without rebinding its closure", &changed);
    changed = f.report.clone();
    changed.final_module_digest = None;
    reject("missing complete-module binding", &changed);
    changed = f.report.clone();
    changed.final_module_digest = Some(Err("unencodable subject".to_string()));
    reject("uncanonical complete-module binding", &changed);
    changed = f.report.clone();
    changed.certified.pop();
    reject("certification label omitted", &changed);
    changed = f.report.clone();
    changed.certified.push(changed.certified[0].clone());
    reject("certification label duplicated", &changed);

    let mut expected = f.expected.clone();
    expected[0].1 = Name::from_string("replayTwin");
    assert!(
        recheck(&f.module, &f.environment, &expected, &f.report).is_err(),
        "the consumer-selected original identity changes the independently derived judgment"
    );
    let mut changed_module = f.module.clone();
    changed_module.name.push_str("-changed");
    assert!(
        recheck(&changed_module, &f.environment, &f.expected, &f.report).is_err(),
        "a theorem transport cannot transfer to a changed complete module"
    );
    changed_module = f.module.clone();
    changed_module.proof_obligations.clear();
    changed_module.proof_certificates.clear();
    assert!(
        recheck(&changed_module, &f.environment, &f.expected, &f.report).is_err(),
        "replay must precede proof-channel stripping"
    );
    assert!(
        !trust_ir_build::validate_module(&changed_module).is_empty(),
        "the old stripping leaves mint-time gates citing removed proof records"
    );
    strip_for_general(&mut changed_module).expect("claim-free publication remains a valid module");
    assert!(changed_module.proof_obligations.is_empty());
    assert!(changed_module.proof_certificates.is_empty());
    assert!(
        changed_module.functions.iter().all(|body| {
            body.proofs.is_empty()
                && body.summary.is_none()
                && body.source_provenance.is_none()
                && if body.is_declaration() {
                    body.body_gate.is_none()
                } else {
                    body.body_gate == Some(BodyGate::Ungated)
                }
        }),
        "validated source equations cannot license claim-free general bodies"
    );

    let mut changed_environment = f.environment.clone();
    let original = f.environment.get_const(&f.expected[0].1).unwrap();
    assert!(changed_environment.forget_decl(&original.name));
    let u8 = Expr::const_str("UInt8");
    changed_environment
        .add_decl(Declaration::Definition {
            name: original.name.clone(),
            level_params: vec![],
            type_: original.type_.clone(),
            value: Expr::lam(
                BinderInfo::Default,
                u8.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    u8.clone(),
                    Expr::lam(BinderInfo::Default, u8, Expr::bvar(0)),
                ),
            ),
            is_reducible: true,
        })
        .expect("a changed same-signature original body itself kernel-checks");
    assert_ne!(
        changed_environment.closure_digest(&original.name).unwrap(),
        f.environment.closure_digest(&original.name).unwrap()
    );
    assert!(
        recheck(&f.module, &changed_environment, &f.expected, &f.report).is_err(),
        "a retained theorem cannot transfer to a changed accepted source environment"
    );
}

#[test]
fn checked_source_replay_preserves_legacy_absence_and_rejects_missing_roots() {
    let f = compile("def replayLegacy (a : UInt64) : UInt64 := a\n", &["replayLegacy"]);
    assert!(f.report.source_equations.is_empty(), "nonconditional source has no such theorem");
    assert_eq!(f.report.final_module_digest, None);
    assert_eq!(recheck(&f.module, &f.environment, &f.expected, &f.report), Ok(0));
    let mut renamed = f.module.clone();
    renamed
        .functions
        .iter_mut()
        .find(|body| body.name == f.expected[0].0)
        .unwrap()
        .name
        .push_str("-renamed");
    let absent = TvMintReport::default();
    assert!(
        recheck(&renamed, &f.environment, &f.expected, &absent).is_err(),
        "uncertified/empty transport cannot hide a renamed original root"
    );
    let mut missing = f.module.clone();
    missing.functions.retain(|body| body.name != f.expected[0].0);
    assert!(
        recheck(&missing, &f.environment, &f.expected, &absent).is_err(),
        "uncertified/empty transport cannot hide a removed original root"
    );
    let mut bodyless = f.module.clone();
    bodyless.proof_obligations.clear();
    bodyless.proof_certificates.clear();
    bodyless.obligation_diagnostics.clear();
    let root = bodyless.functions.iter_mut().find(|body| body.name == f.expected[0].0).unwrap();
    root.blocks.clear();
    root.proofs.clear();
    root.summary = None;
    root.body_gate = None;
    let errors = trust_ir_build::validate_module(&bodyless);
    assert!(errors.is_empty(), "bodyless control must be an otherwise valid module: {errors:?}");
    assert!(
        recheck(&bodyless, &f.environment, &f.expected, &absent).is_err(),
        "a valid external declaration cannot stand in for the expected original definition"
    );
    let mut ambiguous = f.expected.clone();
    ambiguous.push(ambiguous[0].clone());
    assert!(
        recheck(&f.module, &f.environment, &ambiguous, &f.report).is_err(),
        "duplicate externally selected mappings cannot share one body"
    );
}

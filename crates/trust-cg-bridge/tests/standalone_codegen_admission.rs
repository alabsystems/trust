//! Existing standalone kernel mint, exact custody, and unchanged strict object gate.
#![cfg(feature = "clean-codegen")]
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use clean_kernel::Name;
use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanSourceInput,
};
use trust_cg_bridge::call_event::{FnPlacement, ProducerBody, ProducerModule};
use trust_cg_bridge::compiled_object::RelocationModel;
use trust_cg_bridge::f1_compile::{
    F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, StandaloneCodegenAdmission,
    compile_and_verify_trust_ir_module, compile_and_verify_trust_ir_module_with_standalone,
};
use trust_cg_bridge::verify_output::EmitPolicy;
use trust_clean_ir_gate::CodegenRelocation;
use trust_clean_ir_gate::standalone::{
    PublishedStandaloneTrustIrFaithful, admit_standalone_scalar, standalone_codegen_gate_stamp,
};
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{BinOp, Inst, Linkage, Module, Producer, Ty, Visibility};

fn batch(source: &str) -> CheckedLeanSourceBatch {
    CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Main".into(),
            path: "/checked/Main.lean".into(),
            source: source.into(),
        }],
        false,
    )
}
fn subject(
    context: &AcceptedLeanSourceContext<'_>,
) -> (PublishedStandaloneTrustIrFaithful, Module, Module, CodegenRelocation) {
    let name = Name::from_string("add64");
    let plan = trust_clean_origin::emit::plan_standalone_clean_origin_body_for_name(
        context.environment(),
        &name,
    )
    .unwrap();
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
    let original = trust_clean_ir::emit_standalone_clean_origin_function(
        &plan,
        FuncId::new(0),
        FuncTyId::new(0),
    )
    .unwrap();
    let token = admit_standalone_scalar(context, &name, &signature, &original).unwrap();
    let mut published = original.clone();
    published.producer = Some(Producer::Clean);
    let token =
        token.authenticate_published(context, &name, &signature, &original, &published).unwrap();
    let mut source = Module::new("standalone");
    source.func_types.push(signature);
    source.functions.push(published);
    let relocation = CodegenRelocation {
        function_id: FuncId::new(0),
        linkage: Linkage::External,
        visibility: Visibility::Default,
    };
    let mut target = source.clone();
    target.functions[0].linkage = relocation.linkage;
    target.functions[0].visibility = relocation.visibility;
    target.functions[0].body_gate = Some(standalone_codegen_gate_stamp());
    (token, source, target, relocation)
}
fn alter(module: &mut Module) {
    for node in &mut module.functions[0].blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = BinOp::Sub;
            return;
        }
    }
    panic!("no binop")
}
#[test]
fn exact_token_module_bindings_reject_mutations_and_stale_contexts() {
    let checked = batch("def add64 (a b : UInt64) : UInt64 := a + b\n");
    let context = checked.accepted_context().unwrap();
    let (token, source, target, relocation) = subject(&context);
    let accepted = || {
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &target,
            relocation,
        )
    };
    assert!(accepted().is_ok());
    let stale = batch("-- distinct accepted bytes\ndef add64 (a b : UInt64) : UInt64 := a + b\n");
    assert!(
        StandaloneCodegenAdmission::checked(
            &stale.accepted_context().unwrap(),
            &token,
            &source,
            FuncId::new(0),
            &target,
            relocation
        )
        .is_err()
    );
    let mut changed = source.clone();
    alter(&mut changed);
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &changed,
            FuncId::new(0),
            &target,
            relocation
        )
        .is_err()
    );
    let mut changed = target.clone();
    alter(&mut changed);
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &changed,
            relocation
        )
        .is_err()
    );
    let mut changed = target.clone();
    changed.func_types[0].params[0] = Ty::U32;
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &changed,
            relocation
        )
        .is_err()
    );
    let mut changed = target.clone();
    changed.functions[0].calling_conv = trust_ir::CallingConv::C;
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &changed,
            relocation
        )
        .is_err()
    );
    let mut changed = target.clone();
    changed.functions[0].body_gate = None;
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &changed,
            relocation
        )
        .is_err()
    );
    let mut changed = target.clone();
    changed.functions.push(changed.functions[0].clone());
    assert!(
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &changed,
            relocation
        )
        .is_err()
    );
}

#[test]
fn strict_gate_requires_complete_live_custody_and_exact_output_source() {
    let checked = batch("def add64 (a b : UInt64) : UInt64 := a + b\n");
    let context = checked.accepted_context().unwrap();
    let (token, source, target, relocation) = subject(&context);
    let admission = StandaloneCodegenAdmission::checked(
        &context,
        &token,
        &source,
        FuncId::new(0),
        &target,
        relocation,
    )
    .unwrap();
    let producers = vec![ProducerModule::named_by_symbols(Arc::new(source.clone()))];
    let bodies =
        BTreeMap::from([("add64".to_owned(), ProducerBody { producer: 0, func: FuncId::new(0) })]);
    let placements = BTreeMap::from([(
        "add64".to_owned(),
        FnPlacement::from_scalar_signature(&source, &source.functions[0]).unwrap(),
    )]);
    let config = F1CompileConfig {
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O0,
        relocation: RelocationModel::Static,
        force_frame_pointers: false,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    let input = F1CompileInput {
        m_cg: &target,
        producers: &producers,
        bodies: &bodies,
        placements: &placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &config,
    };
    assert!(compile_and_verify_trust_ir_module(&input).is_err(), "a stamp is never permission");
    let shipped = compile_and_verify_trust_ir_module_with_standalone(&input, &[admission]).unwrap();
    assert!(!shipped.object.is_empty());
    assert!(shipped.unclosed.is_empty());
    let admission = || {
        StandaloneCodegenAdmission::checked(
            &context,
            &token,
            &source,
            FuncId::new(0),
            &target,
            relocation,
        )
        .unwrap()
    };
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(&input, &[admission(), admission()])
            .is_err()
    );
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(
            &F1CompileInput { policy: EmitPolicy::AllowUnknown, ..input },
            &[admission()]
        )
        .is_err(),
        "standalone API cannot downgrade strict shipping"
    );
    let mut changed_source = source.clone();
    alter(&mut changed_source);
    let bad_producers = vec![ProducerModule::named_by_symbols(Arc::new(changed_source))];
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(
            &F1CompileInput { producers: &bad_producers, ..input },
            &[admission()]
        )
        .is_err()
    );
    let mut wrong_symbols = producers.clone();
    wrong_symbols[0].symbols.insert(FuncId::new(0), "forged_symbol".into());
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(
            &F1CompileInput { producers: &wrong_symbols, ..input },
            &[admission()]
        )
        .is_err()
    );
    let missing_bindings = BTreeMap::new();
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(
            &F1CompileInput { bodies: &missing_bindings, ..input },
            &[admission()]
        )
        .is_err()
    );
    let mut extra = target.clone();
    let mut f = extra.functions[0].clone();
    f.id = FuncId::new(1);
    f.name = "unearned".into();
    extra.functions.push(f);
    assert!(
        compile_and_verify_trust_ir_module_with_standalone(
            &F1CompileInput { m_cg: &extra, ..input },
            &[admission()]
        )
        .is_err()
    );
}

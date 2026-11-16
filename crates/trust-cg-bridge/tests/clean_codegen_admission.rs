// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual Clean source/kernel admission followed by the shipping Compiler
//! consumer. Mutations exercise the compiled body and its output-gate source.

#![cfg(feature = "clean-codegen")]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use trust_certify::clean_island::CleanIslandSession;
use trust_cg_bridge::call_event::{FnPlacement, ProducerBody, ProducerModule};
use trust_cg_bridge::compiled_object::RelocationModel;
use trust_cg_bridge::f1_compile::{
    CleanCodegenAdmission, F1CompileConfig, F1CompileInput, F1OptLevel, F1Refusal, F1Target,
    compile_and_verify_trust_ir_module, compile_and_verify_trust_ir_module_with_clean,
};
use trust_cg_bridge::verify_output::EmitPolicy;
use trust_clean_ir_gate::{
    CodegenRelocation, PublishedTrustIrFaithful, admit_clean_origin, clean_carrier_gate_stamp,
};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{BinOp, Inst, Linkage, Module, Producer, Visibility};

fn subject() -> (PublishedTrustIrFaithful, Module, Module, CodegenRelocation) {
    subject_body("a + b")
}

fn subject_body(body: &str) -> (PublishedTrustIrFaithful, Module, Module, CodegenRelocation) {
    let mut session = CleanIslandSession::new();
    let outcome = session.check(&format!("def sum (a b : UInt64) : UInt64 := {body}"));
    assert!(!outcome.is_rejected(), "source must kernel-check: {outcome:?}");
    let environment = session.environment().expect("accepted source");
    let plan = plan_clean_origin_body(environment, "sum").expect("source plan");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
    let mut emitted =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("SSA emission");
    emitted.display_path = Some("sum".into());
    emitted.name = "_RNvCs0_7fixture3sum".into();
    let token = admit_clean_origin(environment, &plan, 4, "m::sum", &signature, &emitted)
        .expect("kernel carrier gate");
    let mut published = emitted.clone();
    published.producer = Some(Producer::Clean);
    published.body_gate = Some(clean_carrier_gate_stamp());
    let entry = token
        .authenticate_published("sum", 4, "m::sum", &signature, &emitted, &published)
        .expect("authenticated publication");
    let mut source = Module::new("clean_subject");
    source.func_types.push(signature);
    source.functions.push(published);
    let relocation = CodegenRelocation {
        function_id: FuncId::new(0),
        linkage: Linkage::External,
        visibility: Visibility::Default,
    };
    let mut codegen = source.clone();
    codegen.functions[0].linkage = relocation.linkage;
    codegen.functions[0].visibility = relocation.visibility;
    (entry, source, codegen, relocation)
}

struct Case {
    module: Module,
    producers: Vec<ProducerModule>,
    bodies: BTreeMap<String, ProducerBody>,
    placements: BTreeMap<String, FnPlacement>,
    config: F1CompileConfig,
}

impl Case {
    fn new(source: &Module, module: Module) -> Self {
        let function = &source.functions[0];
        Self {
            placements: BTreeMap::from([(
                function.name.clone(),
                FnPlacement::from_scalar_signature(source, function).expect("scalar placement"),
            )]),
            bodies: BTreeMap::from([(
                function.name.clone(),
                ProducerBody { producer: 0, func: function.id },
            )]),
            producers: vec![ProducerModule::named_by_symbols(Arc::new(source.clone()))],
            module,
            config: F1CompileConfig {
                target: F1Target::Aarch64AppleDarwin,
                opt_level: F1OptLevel::O0,
                relocation: RelocationModel::Static,
                force_frame_pointers: false,
                never_inline: BTreeSet::new(),
                upstream_mir_lane: false,
            },
        }
    }

    fn input(&self) -> F1CompileInput<'_> {
        F1CompileInput {
            m_cg: &self.module,
            producers: &self.producers,
            bodies: &self.bodies,
            placements: &self.placements,
            policy: EmitPolicy::StrictProvenOnly,
            config: &self.config,
        }
    }
}

fn subtract(module: &mut Module) {
    for node in &mut module.functions[0].blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = BinOp::Sub;
            return;
        }
    }
    panic!("fixture has no arithmetic instruction");
}

fn boundary(result: Result<trust_cg_bridge::f1_compile::F1Shipped, F1Refusal>, variant: &str) {
    let F1Refusal::Boundary(rows) = result.expect_err("must refuse before compilation") else {
        panic!("expected the admission boundary");
    };
    assert!(rows.iter().any(|r| r.variant == variant), "{rows:?}");
}

#[test]
fn a_real_carrier_permission_reaches_compiler_and_the_unchanged_strict_gate() {
    for body in ["a + b", "a", "7", "(a + b) * (a - b)"] {
        let (entry, source, module, relocation) = subject_body(body);
        let mut case = Case::new(&source, module);
        for target in [F1Target::Aarch64AppleDarwin, F1Target::Aarch64UnknownLinuxGnu] {
            for model in [RelocationModel::Static, RelocationModel::Pic] {
                case.config.target = target;
                case.config.relocation = model;
                let admission = CleanCodegenAdmission::checked(
                    &entry,
                    &source,
                    FuncId::new(0),
                    &case.module,
                    relocation,
                )
                .expect("third binding");
                let shipped =
                    compile_and_verify_trust_ir_module_with_clean(&case.input(), &[admission])
                        .unwrap_or_else(|why| panic!("{body} on {target:?}/{model:?}: {why}"));
                assert!(!shipped.object.is_empty());
                assert!(shipped.unclosed.is_empty());
            }
        }
    }
}

#[test]
fn stamps_and_omitted_admissions_stay_refused_even_with_the_feature_enabled() {
    let (_, source, module, _) = subject();
    let case = Case::new(&source, module);
    boundary(compile_and_verify_trust_ir_module(&case.input()), "CleanOriginBelowCodegenGate");
    boundary(
        compile_and_verify_trust_ir_module_with_clean(&case.input(), &[]),
        "CleanOriginBelowCodegenGate",
    );
}

#[test]
fn changed_codegen_and_changed_output_gate_sources_are_both_refused() {
    for change_codegen in [false, true] {
        let (entry, source, module, relocation) = subject();
        let admission =
            CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &module, relocation)
                .expect("third binding");
        let mut case = Case::new(&source, module);
        if change_codegen {
            subtract(&mut case.module);
        } else {
            subtract(Arc::make_mut(&mut case.producers[0].module));
        }
        boundary(
            compile_and_verify_trust_ir_module_with_clean(&case.input(), &[admission]),
            "CleanAdmissionMismatch",
        );
    }
}

#[test]
fn a_valid_clean_permission_cannot_license_a_rust_body_with_a_copied_stamp() {
    let (entry, source, module, relocation) = subject();
    let admission =
        CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &module, relocation)
            .expect("third binding");
    let mut case = Case::new(&source, module);
    let mut forged = case.module.functions[0].clone();
    forged.id = FuncId::new(1);
    forged.name.push_str("_forged");
    forged.producer = Some(Producer::TRust);
    case.module.functions.push(forged);
    boundary(
        compile_and_verify_trust_ir_module_with_clean(&case.input(), &[admission]),
        "CleanAuthorityOnOtherProducer",
    );
}

#[test]
fn actual_module_signatures_and_producer_selectors_are_rechecked_at_compile_time() {
    for change in 0..4 {
        let (entry, source, module, relocation) = subject();
        let admission =
            CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &module, relocation)
                .expect("third binding");
        let mut case = Case::new(&source, module);
        match change {
            0 => case.module.func_types[0].returns[0] = trust_ir::Ty::U32,
            1 => {
                Arc::make_mut(&mut case.producers[0].module).func_types[0].returns[0] =
                    trust_ir::Ty::U32;
            }
            2 => case.bodies.values_mut().next().expect("binding").producer = 99,
            3 => {
                case.producers[0].symbols.insert(FuncId::new(0), "other_symbol".into());
            }
            _ => unreachable!(),
        }
        boundary(
            compile_and_verify_trust_ir_module_with_clean(&case.input(), &[admission]),
            "CleanAdmissionMismatch",
        );
    }
}

#[test]
fn a_valid_permission_does_not_cover_another_clean_body_or_a_duplicate_entry() {
    let (entry, source, module, relocation) = subject();
    let first =
        CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &module, relocation)
            .expect("third binding");
    let second =
        CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &module, relocation)
            .expect("third binding");
    let mut case = Case::new(&source, module);
    boundary(
        compile_and_verify_trust_ir_module_with_clean(&case.input(), &[first, second]),
        "CleanAdmissionMismatch",
    );
    let admission =
        CleanCodegenAdmission::checked(&entry, &source, FuncId::new(0), &case.module, relocation)
            .expect("third binding");
    let mut copied = case.module.functions[0].clone();
    copied.id = FuncId::new(1);
    copied.name.push_str("_copy");
    case.module.functions.push(copied);
    boundary(
        compile_and_verify_trust_ir_module_with_clean(&case.input(), &[admission]),
        "CleanOriginBelowCodegenGate",
    );
}

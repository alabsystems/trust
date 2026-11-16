// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual original Module/object fixture as independently supplied CURRENT
//! input data. No new TCX/compiler/SDK, physical ABI or source-grade claim.
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use trust_ir::inst::BinOp;
use trust_ir::value::FuncId;
use trust_ir::{Constant, Inst, Module};

use super::*;
use crate::call_event::{FnPlacement, ProducerBody, ProducerModule};
use crate::compiled_object::RelocationModel;
use crate::f1_compile::{F1CompileConfig, F1OptLevel, F1Target};
use crate::verify_output::EmitPolicy;

const MODULE: &[u8] =
    include_bytes!("../../../../tests/fixtures/direct_ir_observation/original-module.bin");
const OBJECT: &[u8] =
    include_bytes!("../../../../tests/fixtures/direct_ir_observation/final-object.o");

struct Current {
    module: Arc<Module>,
    producers: Vec<ProducerModule>,
    bodies: BTreeMap<String, ProducerBody>,
    placements: BTreeMap<String, FnPlacement>,
    symbol: String,
}
impl Current {
    fn actual(literal: u64, renamed: bool) -> Self {
        let mut module = trust_ir::binary::deserialize_module(MODULE).unwrap();
        let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
            panic!("actual fixture literal")
        };
        *value = Constant::Int(i128::from(literal));
        if renamed {
            module.functions[0].name = "renamed_program_scalar".into();
        }
        Self::from_module(module)
    }
    fn from_module(module: Module) -> Self {
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let placement = FnPlacement::from_scalar_signature(&module, &module.functions[0]).unwrap();
        let symbol = module.functions[0].name.clone();
        let module = Arc::new(module);
        Self {
            producers: vec![ProducerModule::named_by_symbols(module.clone())],
            bodies: [(symbol.clone(), ProducerBody { producer: 0, func: FuncId::new(0) })]
                .into_iter()
                .collect(),
            placements: [(symbol.clone(), placement)].into_iter().collect(),
            module,
            symbol,
        }
    }
    fn input(&self) -> CerInput<'_> {
        CerInput {
            m_cg: &self.module,
            producers: &self.producers,
            bodies: &self.bodies,
            placements: &self.placements,
            object: OBJECT,
            relocation_model: RelocationModel::Static,
        }
    }
}
fn configuration(level: F1OptLevel) -> CompilerCaptureConfig {
    CompilerCaptureConfig::expected(
        &F1CompileConfig {
            target: F1Target::Aarch64AppleDarwin,
            opt_level: level,
            relocation: RelocationModel::Static,
            force_frame_pointers: false,
            never_inline: BTreeSet::new(),
            upstream_mir_lane: false,
        },
        EmitPolicy::AllowUnknown,
    )
    .unwrap()
}
fn directory() -> std::path::PathBuf {
    std::env::var_os("TRUST_SCALAR_PROGRAM_COHORT")
        .expect("exact fixed program cohort required")
        .into()
}

#[test]
fn current_input_constructs_actual_program_and_replays_only_fixed_three_claims() {
    let environment = CanonicalScalarProgramEnvironment::open(&directory()).unwrap();
    let cfg = configuration(F1OptLevel::O3);
    let mut fixtures = Vec::new();
    for (literal, renamed) in [(0, false), (8, true), (u64::MAX, false), (7, false)] {
        let current = Current::actual(literal, renamed);
        let capture = CompilerInputCapture::capture(&current.input(), cfg.clone()).unwrap();
        let checked = capture
            .bind_original_scalar_program_mathematics(
                &current.input(),
                &cfg,
                &current.symbol,
                &environment,
            )
            .unwrap();
        let bytes = checked.packet().to_bytes().unwrap();
        let packet = OriginalScalarProgramPacket::from_bytes(&bytes).unwrap();
        let replay = capture
            .replay_original_scalar_program_mathematics(
                &current.input(),
                &cfg,
                &current.symbol,
                &environment,
                &packet,
            )
            .unwrap();
        assert_eq!(checked.claims(), replay.claims());
        assert_eq!(checked.proofs(), replay.proofs());
        assert_eq!(checked.claims().len(), 3);
        assert_eq!(packet.subject.literal, literal);
        assert_eq!(packet.subject.symbol, current.symbol);
        fixtures.push((current, capture, packet));
    }
    let (zero, capture, packet) = &fixtures[0];
    for change in 0..6 {
        let mut bad = packet.clone();
        match change {
            0 => bad.context.0[0] ^= 1,
            1 => bad.cohort_sha256 = "0".repeat(64),
            2 => bad.subject.literal = 8,
            3 => bad.capture_sha256 = "0".repeat(64),
            4 => bad.schema = "other".into(),
            _ => bad.proofs[2] = Vec::new(),
        }
        assert!(
            capture
                .replay_original_scalar_program_mathematics(
                    &zero.input(),
                    &cfg,
                    &zero.symbol,
                    &environment,
                    &bad
                )
                .is_err()
        );
    }
    // Preserve correct independent subject/capture/context and change proof
    // DATA only. A resource refusal never counts as semantic rejection.
    let mut wrong_literal = packet.clone();
    wrong_literal.proofs = fixtures[1].2.proofs.clone();
    let literal_error = capture
        .replay_original_scalar_program_mathematics(
            &zero.input(),
            &cfg,
            &zero.symbol,
            &environment,
            &wrong_literal,
        )
        .unwrap_err();
    // This universally quantified host goal must refuse. Only an observed
    // TypeMismatch counts as semantic rejection; the independent closed
    // wrong-literal/world/stop controls carry that semantic requirement.
    let literal_type_mismatch = literal_error.contains("TypeMismatch");
    let mut wrong_kind = packet.clone();
    wrong_kind.proofs.swap(0, 1);
    let kind_error = capture
        .replay_original_scalar_program_mathematics(
            &zero.input(),
            &cfg,
            &zero.symbol,
            &environment,
            &wrong_kind,
        )
        .unwrap_err();
    assert!(kind_error.contains("TypeMismatch"), "actual claim-kind rebind result: {kind_error}");
    assert!(
        capture
            .replay_original_scalar_program_mathematics(
                &zero.input(),
                &configuration(F1OptLevel::O0),
                &zero.symbol,
                &environment,
                packet
            )
            .is_err()
    );
    assert!(
        capture
            .replay_original_scalar_program_mathematics(
                &fixtures[1].0.input(),
                &cfg,
                &fixtures[1].0.symbol,
                &environment,
                packet
            )
            .is_err()
    );
    let mut wire: serde_json::Value = serde_json::from_slice(&packet.to_bytes().unwrap()).unwrap();
    wire["expected_program"] = "caller-selected".into();
    assert!(OriginalScalarProgramPacket::from_bytes(&serde_json::to_vec(&wire).unwrap()).is_err());
    // Valid IR outside the actual scalar profile stays refused before proof
    // construction. It is not a source-UB refutation or a kernel mismatch.
    let mut sub = zero.module.as_ref().clone();
    let Inst::BinOp { op, .. } = &mut sub.functions[0].blocks[0].body[1].inst else {
        panic!("actual fixture binop")
    };
    *op = BinOp::Sub;
    let sub = Current::from_module(sub);
    let sub_capture = CompilerInputCapture::capture(&sub.input(), cfg.clone()).unwrap();
    assert!(
        sub_capture
            .bind_original_scalar_program_mathematics(&sub.input(), &cfg, &sub.symbol, &environment)
            .is_err()
    );
    println!(
        "SCALAR_PROGRAM_CURRENT positives=4 replay=4 binding_refusals=6 claim_kind_TypeMismatch=1 literal_rebind_TypeMismatch={literal_type_mismatch} current_config=1 current_input=1 packet_model_selector=1 semantic_Sub_refusal=1; captured IR/model construction only,no frontend/ABI/grade"
    );
}

#[test]
fn fixed_program_environment_refuses_missing_and_changed_module_bytes() {
    let root = tempfile::tempdir().unwrap();
    assert!(CanonicalScalarProgramEnvironment::open(root.path()).is_err());
    let source = directory();
    let module = source.join("MiniRustU64ProgramFromBytes.olean");
    let mut bytes = std::fs::read(module).unwrap();
    bytes[0] ^= 1;
    std::fs::write(root.path().join("MiniRustU64ProgramFromBytes.olean"), bytes).unwrap();
    assert!(CanonicalScalarProgramEnvironment::open(root.path()).is_err());
    println!(
        "SCALAR_PROGRAM_CONTEXT missing=1 changed=1 refused; no raw environment/model constructor"
    );
}

// Copyright 2026 Andrew Yates | Apache-2.0
//! Non-authorizing input-data fixture: exact actual original THIR Module and
//! retained diagnostic object, independently selected (never decoded capture
//! as its own reference). This is NOT a new Compiler/TCX/SDK or FnAbi run.
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use clean_kernel::{Expr, Name};
use trust_ir::value::FuncId;
use trust_ir::{Constant, Inst, Module};

use super::*;
use crate::call_event::{FnPlacement, ProducerBody, ProducerModule};
use crate::compiled_object::RelocationModel;
use crate::f1_compile::{F1CompileConfig, F1CompileInput, F1OptLevel, F1Target};
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
}
impl Current {
    fn actual() -> Self {
        let m = trust_ir::binary::deserialize_module(MODULE).unwrap();
        assert_eq!(trust_ir::binary::serialize_module(&m).unwrap(), MODULE);
        Self::from_module(m)
    }
    fn from_module(m: Module) -> Self {
        assert!(trust_ir_build::validate_module(&m).is_empty());
        // Request placement DATA only, not a rustc FnAbi capability or proof.
        let p = FnPlacement::from_scalar_signature(&m, &m.functions[0]).unwrap();
        let symbol = m.functions[0].name.clone();
        let module = Arc::new(m);
        Self {
            producers: vec![ProducerModule::named_by_symbols(module.clone())],
            module,
            bodies: [(symbol.clone(), ProducerBody { producer: 0, func: FuncId::new(0) })]
                .into_iter()
                .collect(),
            placements: [(symbol, p)].into_iter().collect(),
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
fn configuration() -> CompilerCaptureConfig {
    // Independently specified CURRENT REQUEST data, not a historical assertion
    // that this retained diagnostic object was compiled under these flags.
    CompilerCaptureConfig::expected(
        &F1CompileConfig {
            target: F1Target::Aarch64AppleDarwin,
            opt_level: F1OptLevel::O3,
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
    std::env::var_os("TRUST_CANONICAL_SCALAR_COHORT")
        .expect("exact owned fixed cohort required")
        .into()
}

#[test]
fn actual_original_input_binds_and_replays_only_fixed_scalar_claims() {
    let current = Current::actual();
    let cfg = configuration();
    let capture = CompilerInputCapture::capture(&current.input(), cfg.clone()).unwrap();
    let env = CanonicalScalarEnvironment::open(&directory()).unwrap();
    let checked =
        capture.bind_original_scalar_mathematics(&current.input(), &cfg, "addition", &env).unwrap();
    let wire = checked.packet().to_bytes().unwrap();
    let packet = OriginalScalarPacket::from_bytes(&wire).unwrap();
    let replay = capture
        .replay_original_scalar_mathematics(&current.input(), &cfg, "addition", &env, &packet)
        .unwrap();
    assert_eq!(replay.mathematics().subject().module_bytes, MODULE);
    assert_eq!(replay.mathematics().subject().literal, 7);
    assert_eq!(replay.mathematics().claims().len(), 3);
    assert_eq!(replay.mathematics().proofs().len(), 3);
    if let Some(out) = std::env::var_os("TRUST_CANONICAL_SCALAR_OUTPUT") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("packet.json"), &wire).unwrap();
        std::fs::write(out.join("capture.json"), capture.to_bytes().unwrap()).unwrap();
        std::fs::write(out.join("module.bin"), MODULE).unwrap();
    }
    let mut cases = 0;
    for edit in 0..7 {
        let mut bad = packet.clone();
        match edit {
            0 => bad.context.0[0] ^= 1,
            1 => bad.cohort_sha256 = "0".repeat(64),
            2 => bad.subject.literal = 8,
            3 => bad.capture_sha256 = "0".repeat(64),
            4 => bad.subject.function = 1,
            5 => {
                bad.proofs[1] =
                    encode_clean_expr_dag_v2(&Expr::const_(Name::from_string("True.intro"), vec![]))
                        .unwrap()
            }
            _ => bad.proofs[2] = Vec::new(),
        }
        assert!(
            capture
                .replay_original_scalar_mathematics(&current.input(), &cfg, "addition", &env, &bad)
                .is_err(),
            "packet mutation{edit}"
        );
        cases += 1;
    }
    // A genuine different valid original Module does not inherit the retained
    // seven-subject proof, even after all non-authoritative subject hashes and
    // capture data are freshly rebound. Its own possible NoBad is NOT refuted.
    let mut changed = (*current.module).clone();
    let Inst::Const { value: Constant::Int(n), .. } =
        &mut changed.functions[0].blocks[0].body[0].inst
    else {
        panic!("literal")
    };
    *n = 8;
    let other = Current::from_module(changed);
    assert!(
        capture
            .replay_original_scalar_mathematics(&other.input(), &cfg, "addition", &env, &packet)
            .is_err()
    );
    let other_capture = CompilerInputCapture::capture(&other.input(), cfg.clone()).unwrap();
    let (expected, snapshot) =
        other_capture.current_scalar_input(&other.input(), &cfg, "addition").unwrap();
    let mut rebound = packet;
    rebound.subject = expected.binding;
    rebound.capture_sha256 = snapshot;
    let reason = other_capture
        .replay_original_scalar_mathematics(&other.input(), &cfg, "addition", &env, &rebound)
        .unwrap_err();
    assert!(
        !reason.contains("packet/current original input"),
        "must reach checked mathematics: {reason}"
    );
    println!(
        "CANONICAL_SCALAR_CAPTURE positive=1 replay=1 packet_refusals={cases} changed_current=1 rebound_actual_module=1; data-only,noTCX,noFnAbi,noSourceNoUB,noGrade"
    );
}

#[test]
fn fixed_scalar_constructor_refuses_missing_and_changed_context() {
    let original = directory();
    let empty = tempfile::tempdir().unwrap();
    assert!(CanonicalScalarEnvironment::open(empty.path()).is_err());
    let partial = tempfile::tempdir().unwrap();
    // Only a byte-identical root is insufficient: the complete fixed import
    // cohort must be present and matched, then FULL checked.
    std::fs::copy(
        original.join("U64AdditionConsumer.olean"),
        partial.path().join("U64AdditionConsumer.olean"),
    )
    .unwrap();
    assert!(CanonicalScalarEnvironment::open(partial.path()).is_err());
    let wrong = tempfile::tempdir().unwrap();
    let mut bytes = std::fs::read(original.join("U64AdditionConsumer.olean")).unwrap();
    bytes[88] ^= 1;
    std::fs::write(wrong.path().join("U64AdditionConsumer.olean"), bytes).unwrap();
    assert!(CanonicalScalarEnvironment::open(wrong.path()).is_err());
    println!(
        "CANONICAL_SCALAR_CONTEXT missing=1 partial=1 changed=1 refused; no raw-context constructor"
    );
}

#[test]
fn fresh_current_literal_and_names_receive_their_own_checked_mathematics() {
    let mut m = trust_ir::binary::deserialize_module(MODULE).unwrap();
    m.name = "fresh_current_module_8".into();
    m.functions[0].name = "current_symbol_π_8".into();
    let Inst::Const { value: Constant::Int(value), .. } =
        &mut m.functions[0].blocks[0].body[0].inst
    else {
        panic!("actual U64 Const")
    };
    *value = 8;
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let original_bytes = trust_ir::binary::ModuleBinaryPlan::new(&m).to_vec().unwrap();
    assert_eq!(trust_ir::binary::deserialize_module(&original_bytes).unwrap(), m);
    let current = Current::from_module(m);
    let cfg = configuration();
    let input = F1CompileInput {
        m_cg: &current.module,
        producers: &current.producers,
        bodies: &current.bodies,
        placements: &current.placements,
        policy: EmitPolicy::AllowUnknown,
        config: &F1CompileConfig {
            target: F1Target::Aarch64AppleDarwin,
            opt_level: F1OptLevel::O3,
            relocation: RelocationModel::Static,
            force_frame_pointers: false,
            never_inline: Default::default(),
            upstream_mir_lane: false,
        },
    };
    let expected = ExpectedScalarInput::from_compile_input(&input, "current_symbol_π_8").unwrap();
    assert_eq!(expected.module_bytes(), original_bytes);
    assert_eq!(expected.literal(), 8);
    assert_eq!(expected.symbol(), "current_symbol_π_8");
    let capture = CompilerInputCapture::capture(&current.input(), cfg.clone()).unwrap();
    let env = CanonicalScalarEnvironment::open(&directory()).unwrap();
    let checked = capture
        .bind_original_scalar_mathematics(&current.input(), &cfg, "current_symbol_π_8", &env)
        .unwrap();
    assert_eq!(checked.mathematics().subject().module_bytes, original_bytes);
    assert_eq!(checked.mathematics().subject().literal, 8);
    let packet = OriginalScalarPacket::from_bytes(&checked.packet().to_bytes().unwrap()).unwrap();
    let replay = capture
        .replay_original_scalar_mathematics(
            &current.input(),
            &cfg,
            "current_symbol_π_8",
            &env,
            &packet,
        )
        .unwrap();
    assert_eq!(replay.mathematics().subject(), checked.mathematics().subject());
    if let Some(out) = std::env::var_os("TRUST_CANONICAL_SCALAR_OUTPUT") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("fresh8-module.bin"), &original_bytes).unwrap();
        std::fs::write(out.join("fresh8-packet.json"), packet.to_bytes().unwrap()).unwrap();
        std::fs::write(out.join("fresh8-capture.json"), capture.to_bytes().unwrap()).unwrap();
    }
    println!(
        "GENERIC_CANONICAL_SCALAR actual_F1_expected=1 fresh_literal8=1 complete_module_and_symbol=1 three_kernel_claims=1 retained_replay=1; input mathematics only,noSourceNoUB,noGrade"
    );
}

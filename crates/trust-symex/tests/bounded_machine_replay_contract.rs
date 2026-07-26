use trust_symex::{
    BinaryMachineInstructionEvidence, BinaryMachineReplayAttestationStatus,
    BinaryMachineReplayBackend, BinaryMachineReplayBoundaryEvidence,
    BinaryMachineReplayBoundaryKind, BinaryMachineReplayBoundarySemantics,
    BinaryMachineReplayByteRangeDiagnosticKind, BinaryMachineReplayByteRangeEvidence,
    BinaryMachineReplayCapability, BinaryMachineReplayCapabilityEvidence,
    BinaryMachineReplayConfig, BinaryMachineReplayEffectDiagnosticKind,
    BinaryMachineReplayEffectEvidence, BinaryMachineReplayEffectKind, BinaryMachineReplayReport,
    BinaryMachineReplayRequest, BinaryMachineReplayResult, BinaryMachineReplayStatus, BinaryOrigin,
    BinaryReplayConfig, BinaryReplayInput, BinaryReplayRequirement, BinaryReplayTarget,
    BinaryWitness, BinaryWitnessProgramPoint, BinaryWitnessProvenance, BinaryWitnessRecord,
    BinaryWitnessRecordSource, BinaryWitnessTraceStep, BinaryWitnessValue,
    BoundedMachineCodeArchitecture, BoundedMachineCodeImage, BoundedMachineCodeReplayBackend,
    BoundedMachineCodeSegmentPermissions, replay_binary_counterexample_with_machine_replay,
    replay_machine_witness, replay_solver_dispatch_counterexample,
    replay_solver_dispatch_counterexample_with_machine_replay,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryFactSubject,
    BinaryOrigin as TrustBinaryOrigin, BinarySelectedImageIdentity, BinaryStackBase,
    BinaryStorageLocation, Counterexample, CounterexampleTrace, CounterexampleValue, Formula,
    ProofCertificateStatus, ProofStrength, ReplayStatus, SolverDispatchRecord,
    SolverDispatchStatus, SolverQuerySemantics, SourceSpan, TraceStep, VcKind,
    VerificationCondition, VerificationResult,
};

use std::collections::BTreeMap;

const AARCH64_NOP_ENCODING: u32 = 0xd503_201f;
const AARCH64_NOP_BYTES: [u8; 4] = [0x1f, 0x20, 0x03, 0xd5];
const AARCH64_YIELD_BYTES: [u8; 4] = [0x3f, 0x20, 0x03, 0xd5];
const AARCH64_B_PLUS_8_ENCODING: u32 = 0x1400_0002;
const AARCH64_B_PLUS_8_BYTES: [u8; 4] = [0x02, 0x00, 0x00, 0x14];
const AARCH64_BL_PLUS_8_ENCODING: u32 = 0x9400_0002;
const AARCH64_BL_PLUS_8_BYTES: [u8; 4] = [0x02, 0x00, 0x00, 0x94];
const AARCH64_BR_X16_ENCODING: u32 = 0xd61f_0200;
const AARCH64_BR_X16_BYTES: [u8; 4] = [0x00, 0x02, 0x1f, 0xd6];
const AARCH64_BLR_X8_ENCODING: u32 = 0xd63f_0100;
const AARCH64_BLR_X8_BYTES: [u8; 4] = [0x00, 0x01, 0x3f, 0xd6];
const AARCH64_RET_ENCODING: u32 = 0xd65f_03c0;
const AARCH64_RET_BYTES: [u8; 4] = [0xc0, 0x03, 0x5f, 0xd6];
const AARCH64_SVC0_ENCODING: u32 = 0xd400_0001;
const AARCH64_SVC0_BYTES: [u8; 4] = [0x01, 0x00, 0x00, 0xd4];
const AARCH64_HVC0_ENCODING: u32 = 0xd400_0002;
const AARCH64_HVC0_BYTES: [u8; 4] = [0x02, 0x00, 0x00, 0xd4];
const AARCH64_BRK1_ENCODING: u32 = 0xd420_0020;
const AARCH64_BRK1_BYTES: [u8; 4] = [0x20, 0x00, 0x20, 0xd4];
const AARCH64_DMB_ISH_ENCODING: u32 = 0xd503_3b9f;
const AARCH64_DMB_ISH_BYTES: [u8; 4] = [0x9f, 0x3b, 0x03, 0xd5];
const AARCH64_CBZ_WZR_PLUS_8_ENCODING: u32 = 0x3400_005f;
const AARCH64_CBZ_WZR_PLUS_8_BYTES: [u8; 4] = [0x5f, 0x00, 0x00, 0x34];
const AARCH64_CBNZ_WZR_PLUS_8_ENCODING: u32 = 0x3500_005f;
const AARCH64_CBNZ_WZR_PLUS_8_BYTES: [u8; 4] = [0x5f, 0x00, 0x00, 0x35];
const AARCH64_MOVZ_X0_42_ENCODING: u32 = 0xd280_0540;
const AARCH64_MOVZ_X0_42_BYTES: [u8; 4] = [0x40, 0x05, 0x80, 0xd2];
const AARCH64_ADD_X0_X1_X2_ENCODING: u32 = 0x8b02_0020;
const AARCH64_ADD_X0_X1_X2_BYTES: [u8; 4] = [0x20, 0x00, 0x02, 0x8b];
const AARCH64_SUB_X0_X1_X2_ENCODING: u32 = 0xcb02_0020;
const AARCH64_SUB_X0_X1_X2_BYTES: [u8; 4] = [0x20, 0x00, 0x02, 0xcb];
const AARCH64_STR_X0_X1_ENCODING: u32 = 0xf900_0020;
const AARCH64_STR_X0_X1_BYTES: [u8; 4] = [0x20, 0x00, 0x00, 0xf9];
const AARCH64_LDR_X2_X1_ENCODING: u32 = 0xf940_0022;
const AARCH64_LDR_X2_X1_BYTES: [u8; 4] = [0x22, 0x00, 0x40, 0xf9];
const AARCH64_STP_X29_X30_SP_PRE_DEC16_ENCODING: u32 = 0xa9bf_7bfd;
const AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES: [u8; 4] = [0xfd, 0x7b, 0xbf, 0xa9];
const AARCH64_LDP_X29_X30_SP_POST_INC16_ENCODING: u32 = 0xa8c1_7bfd;
const AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES: [u8; 4] = [0xfd, 0x7b, 0xc1, 0xa8];
const X86_64_NOP_ENCODING: u32 = 0x90;
const X86_64_NOP_BYTES: [u8; 1] = [0x90];
const X86_64_MOVABS_RAX_IMM64_ENCODING: u32 = 0xb8;
const X86_64_MOVABS_RAX_IMM64_BYTES: [u8; 10] =
    [0x48, 0xb8, 0x78, 0x56, 0x34, 0x12, 0x00, 0x00, 0x00, 0x00];
const X86_64_MOV_PTR_RAX_RAX_ENCODING: u32 = 0x89;
const X86_64_MOV_PTR_RAX_RAX_BYTES: [u8; 3] = [0x48, 0x89, 0x00];
const X86_64_MOV_RCX_PTR_RAX_ENCODING: u32 = 0x89;
const X86_64_MOV_RCX_PTR_RAX_BYTES: [u8; 3] = [0x48, 0x8b, 0x08];
const X86_64_PUSH_RAX_ENCODING: u32 = 0x50;
const X86_64_PUSH_RAX_BYTES: [u8; 1] = [0x50];
const X86_64_POP_RCX_ENCODING: u32 = 0x59;
const X86_64_POP_RCX_BYTES: [u8; 1] = [0x59];
const X86_64_CALL_0X401010_ENCODING: u32 = 0xe8;
const X86_64_CALL_0X401010_BYTES: [u8; 5] = [0xe8, 0x0b, 0x00, 0x00, 0x00];
const X86_64_CALL_RAX_ENCODING: u32 = 0xff;
const X86_64_CALL_RAX_BYTES: [u8; 2] = [0xff, 0xd0];
const X86_64_CALL_PTR_RAX_ENCODING: u32 = 0xff;
const X86_64_CALL_PTR_RAX_BYTES: [u8; 2] = [0xff, 0x10];
const X86_64_RET_ENCODING: u32 = 0xc3;
const X86_64_RET_BYTES: [u8; 1] = [0xc3];
const X86_64_INT3_BYTES: [u8; 1] = [0xcc];
const TEST_ARTIFACT_SHA256: &str =
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
const TEST_SELECTED_IMAGE_SHA256: &str =
    "04ca88f2b88d606239021d6eb03752f117e3f73fb022df93dbe99ab93edf368b";
const X86_64_LOAD_FIXTURE_PATH: &str = "tests/fixtures/binary_decomp/x86_64-load-elf.hex";
const X86_64_LOAD_FIXTURE_HEX: &str =
    include_str!("../../../tests/fixtures/binary_decomp/x86_64-load-elf.hex");
const X86_64_LOAD_FIXTURE_SHA256: &str =
    "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000";
const X86_64_LOAD_ENTRY: u64 = 0x400000;
const X86_64_LOAD_TEXT_FILE_OFFSET: u64 = 0x78;
const X86_64_LOAD_INSTRUCTION_BYTES: [u8; 3] = [0x48, 0x8b, 0x07];
const X86_64_LOAD_NOP_BYTES: [u8; 1] = [0x90];
const X86_64_LOAD_MEMORY_ADDRESS: u64 = 0x2000;
const X86_64_LOAD_MEMORY_VALUE: u128 = 0x1122_3344_5566_7788;

fn test_artifact_digest() -> BinaryArtifactDigest {
    BinaryArtifactDigest::sha256(TEST_ARTIFACT_SHA256)
}

fn test_selected_image() -> BinarySelectedImageIdentity {
    BinarySelectedImageIdentity {
        file_offset: 0,
        file_size: 0x1000,
        sha256: TEST_SELECTED_IMAGE_SHA256.to_string(),
    }
}

fn offset_test_selected_image() -> BinarySelectedImageIdentity {
    BinarySelectedImageIdentity {
        file_offset: 4,
        file_size: 0x1000,
        sha256: TEST_SELECTED_IMAGE_SHA256.to_string(),
    }
}

fn test_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(test_artifact_digest()),
        selected_image: Some(test_selected_image()),
    }
}

fn instruction(
    address: u64,
    size: u8,
    encoding: u32,
    bytes: impl Into<Vec<u8>>,
) -> TrustBinaryOrigin {
    TrustBinaryOrigin {
        binary_path: Some("contract.bin".to_owned()),
        function_entry: Some(0x401000),
        instruction_address: address,
        instruction_size: Some(size),
        encoding: Some(encoding),
        instruction_bytes: bytes.into(),
        source: None,
    }
}

fn aarch64_nop(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_NOP_ENCODING, AARCH64_NOP_BYTES)
}

fn aarch64_b_plus_8(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_B_PLUS_8_ENCODING, AARCH64_B_PLUS_8_BYTES)
}

fn aarch64_bl_plus_8(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_BL_PLUS_8_ENCODING, AARCH64_BL_PLUS_8_BYTES)
}

fn aarch64_br_x16(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_BR_X16_ENCODING, AARCH64_BR_X16_BYTES)
}

fn aarch64_blr_x8(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_BLR_X8_ENCODING, AARCH64_BLR_X8_BYTES)
}

fn aarch64_ret(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_RET_ENCODING, AARCH64_RET_BYTES)
}

fn aarch64_svc0(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_SVC0_ENCODING, AARCH64_SVC0_BYTES)
}

fn aarch64_hvc0(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_HVC0_ENCODING, AARCH64_HVC0_BYTES)
}

fn aarch64_brk1(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_BRK1_ENCODING, AARCH64_BRK1_BYTES)
}

fn aarch64_dmb_ish(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_DMB_ISH_ENCODING, AARCH64_DMB_ISH_BYTES)
}

fn aarch64_cbz_wzr_plus_8(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_CBZ_WZR_PLUS_8_ENCODING, AARCH64_CBZ_WZR_PLUS_8_BYTES)
}

fn aarch64_cbnz_wzr_plus_8(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_CBNZ_WZR_PLUS_8_ENCODING, AARCH64_CBNZ_WZR_PLUS_8_BYTES)
}

fn aarch64_movz_x0_42(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_MOVZ_X0_42_ENCODING, AARCH64_MOVZ_X0_42_BYTES)
}

fn aarch64_add_x0_x1_x2(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_ADD_X0_X1_X2_ENCODING, AARCH64_ADD_X0_X1_X2_BYTES)
}

fn aarch64_sub_x0_x1_x2(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_SUB_X0_X1_X2_ENCODING, AARCH64_SUB_X0_X1_X2_BYTES)
}

fn aarch64_str_x0_x1(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_STR_X0_X1_ENCODING, AARCH64_STR_X0_X1_BYTES)
}

fn aarch64_ldr_x2_x1(address: u64) -> TrustBinaryOrigin {
    instruction(address, 4, AARCH64_LDR_X2_X1_ENCODING, AARCH64_LDR_X2_X1_BYTES)
}

fn aarch64_stp_x29_x30_sp_pre_dec16(address: u64) -> TrustBinaryOrigin {
    instruction(
        address,
        4,
        AARCH64_STP_X29_X30_SP_PRE_DEC16_ENCODING,
        AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES,
    )
}

fn aarch64_ldp_x29_x30_sp_post_inc16(address: u64) -> TrustBinaryOrigin {
    instruction(
        address,
        4,
        AARCH64_LDP_X29_X30_SP_POST_INC16_ENCODING,
        AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES,
    )
}

fn x86_64_nop(address: u64) -> TrustBinaryOrigin {
    instruction(address, 1, X86_64_NOP_ENCODING, X86_64_NOP_BYTES)
}

fn x86_64_movabs_rax_imm64(address: u64) -> TrustBinaryOrigin {
    instruction(address, 10, X86_64_MOVABS_RAX_IMM64_ENCODING, X86_64_MOVABS_RAX_IMM64_BYTES)
}

fn x86_64_mov_ptr_rax_rax(address: u64) -> TrustBinaryOrigin {
    instruction(address, 3, X86_64_MOV_PTR_RAX_RAX_ENCODING, X86_64_MOV_PTR_RAX_RAX_BYTES)
}

fn x86_64_mov_rcx_ptr_rax(address: u64) -> TrustBinaryOrigin {
    instruction(address, 3, X86_64_MOV_RCX_PTR_RAX_ENCODING, X86_64_MOV_RCX_PTR_RAX_BYTES)
}

fn x86_64_push_rax(address: u64) -> TrustBinaryOrigin {
    instruction(address, 1, X86_64_PUSH_RAX_ENCODING, X86_64_PUSH_RAX_BYTES)
}

fn x86_64_pop_rcx(address: u64) -> TrustBinaryOrigin {
    instruction(address, 1, X86_64_POP_RCX_ENCODING, X86_64_POP_RCX_BYTES)
}

fn x86_64_call_0x401010(address: u64) -> TrustBinaryOrigin {
    instruction(address, 5, X86_64_CALL_0X401010_ENCODING, X86_64_CALL_0X401010_BYTES)
}

fn x86_64_call_rax(address: u64) -> TrustBinaryOrigin {
    instruction(address, 2, X86_64_CALL_RAX_ENCODING, X86_64_CALL_RAX_BYTES)
}

fn x86_64_call_ptr_rax(address: u64) -> TrustBinaryOrigin {
    instruction(address, 2, X86_64_CALL_PTR_RAX_ENCODING, X86_64_CALL_PTR_RAX_BYTES)
}

fn x86_64_ret(address: u64) -> TrustBinaryOrigin {
    instruction(address, 1, X86_64_RET_ENCODING, X86_64_RET_BYTES)
}

fn checked_in_x86_64_load_fixture_bytes() -> Vec<u8> {
    decode_hex_fixture(X86_64_LOAD_FIXTURE_HEX)
}

fn decode_hex_fixture(hex: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut high = None;
    for ch in hex.chars().filter(|ch| !ch.is_whitespace()) {
        let nibble = ch.to_digit(16).unwrap_or_else(|| panic!("invalid fixture hex digit {ch}"));
        if let Some(prev) = high.take() {
            bytes.push(((prev << 4) | nibble) as u8);
        } else {
            high = Some(nibble);
        }
    }
    assert!(high.is_none(), "fixture hex must contain complete bytes");
    bytes
}

fn checked_in_x86_64_load_selected_image() -> BinarySelectedImageIdentity {
    BinarySelectedImageIdentity {
        file_offset: 0,
        file_size: checked_in_x86_64_load_fixture_bytes().len() as u64,
        sha256: X86_64_LOAD_FIXTURE_SHA256.to_owned(),
    }
}

fn checked_in_x86_64_load_instruction_origin(
    address: u64,
    _file_offset: u64,
    bytes: impl Into<Vec<u8>>,
) -> TrustBinaryOrigin {
    let bytes = bytes.into();
    TrustBinaryOrigin {
        binary_path: Some(X86_64_LOAD_FIXTURE_PATH.to_owned()),
        function_entry: Some(X86_64_LOAD_ENTRY),
        instruction_address: address,
        instruction_size: Some(bytes.len() as u8),
        encoding: None,
        instruction_bytes: bytes,
        source: Some(SourceSpan::binary_address(address)),
    }
}

fn assert_canonical_sha256_digest(value: &str) {
    assert_eq!(value.len(), 64, "digest should be lowercase SHA-256 hex: {value}");
    assert!(
        value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "digest should be lowercase SHA-256 hex: {value}"
    );
}

fn straight_line_witness(origins: Vec<TrustBinaryOrigin>) -> BinaryWitness {
    BinaryWitness {
        has_execution_trace: true,
        raw_trace_steps: origins.len(),
        trace: origins
            .into_iter()
            .enumerate()
            .map(|(step, origin)| BinaryWitnessTraceStep {
                step: step as u32,
                program_point: Some(BinaryWitnessProgramPoint {
                    raw: format!("bb{step}@0x{:x}", origin.instruction_address),
                    block: Some(step),
                    origin: Some(origin),
                }),
                assignments: Vec::new(),
            })
            .collect(),
        provenance: BinaryWitnessProvenance {
            artifact_digest: Some(test_artifact_digest()),
            selected_image: Some(test_selected_image()),
            ..BinaryWitnessProvenance::default()
        },
        ..BinaryWitness::default()
    }
}

fn register_trace_record(
    name: &str,
    bit_width: u32,
    value: u128,
    program_point: Option<BinaryWitnessProgramPoint>,
) -> BinaryWitnessRecord {
    BinaryWitnessRecord {
        source: BinaryWitnessRecordSource::TraceAssignment,
        raw_name: name.to_owned(),
        value: BinaryWitnessValue {
            typed: Some(CounterexampleValue::Uint(value)),
            raw: format!("0x{value:x}"),
        },
        subject: BinaryFactSubject::Register {
            function: "contract".to_owned(),
            register: name.to_owned(),
        },
        storage: BinaryStorageLocation::Register {
            name: name.to_owned(),
            bit_width: Some(bit_width),
        },
        function: None,
        local_index: None,
        program_point,
    }
}

fn stack_trace_record(
    offset: i64,
    size_bytes: u32,
    value: u128,
    program_point: Option<BinaryWitnessProgramPoint>,
) -> BinaryWitnessRecord {
    BinaryWitnessRecord {
        source: BinaryWitnessRecordSource::TraceAssignment,
        raw_name: format!("stack:sp{offset:+}"),
        value: BinaryWitnessValue {
            typed: Some(CounterexampleValue::Uint(value)),
            raw: format!("0x{value:x}"),
        },
        subject: BinaryFactSubject::Memory { name: None, address: None },
        storage: BinaryStorageLocation::Stack {
            base: BinaryStackBase::StackPointer,
            offset,
            size_bytes: Some(size_bytes),
        },
        function: None,
        local_index: None,
        program_point,
    }
}

fn memory_trace_record(
    name: &str,
    address: u64,
    size_bytes: u32,
    value: u128,
    program_point: Option<BinaryWitnessProgramPoint>,
) -> BinaryWitnessRecord {
    BinaryWitnessRecord {
        source: BinaryWitnessRecordSource::TraceAssignment,
        raw_name: name.to_owned(),
        value: BinaryWitnessValue {
            typed: Some(CounterexampleValue::Uint(value)),
            raw: format!("0x{value:x}"),
        },
        subject: BinaryFactSubject::Memory { name: Some(name.to_owned()), address: Some(address) },
        storage: BinaryStorageLocation::Memory {
            address: Formula::BitVec { value: address as i128, width: 64 },
            size_bytes: Some(size_bytes),
        },
        function: None,
        local_index: None,
        program_point,
    }
}

fn bind_dummy_model_assignment(witness: &mut BinaryWitness) {
    let program_point = witness.trace.first().and_then(|step| step.program_point.clone());
    let trace_record = register_trace_record("X0", 64, 1, program_point);
    let mut model_record = trace_record.clone();
    model_record.source = BinaryWitnessRecordSource::ModelAssignment;
    model_record.program_point = None;
    witness.raw_model_assignments = 1;
    witness.provenance.model_assignment_names.push("X0".to_owned());
    witness.records.push(model_record);
    witness.records.push(trace_record.clone());
    if let Some(first_step) = witness.trace.first_mut() {
        first_step.assignments.push(trace_record);
    }
}

fn x86_push_pop_stack_witness(step1_rsp: u128, step1_stack_value: u128) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const PUSHED: u128 = 0x1122_3344_5566_7788;

    let mut witness = straight_line_witness(vec![
        x86_64_push_rax(0x401000),
        x86_64_pop_rcx(0x401001),
        x86_64_nop(0x401002),
    ]);
    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step0.clone()));
    witness.trace[0].assignments.push(register_trace_record("RAX", 64, PUSHED, step0));

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record("RSP", 64, step1_rsp, step1.clone()));
    witness.trace[1].assignments.push(stack_trace_record(0, 8, step1_stack_value, step1));

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step2.clone()));
    witness.trace[2].assignments.push(register_trace_record("RCX", 64, PUSHED, step2));
    witness
}

fn x86_call_ret_stack_witness(include_return_slot_witness: bool) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const CALL_FRAME_SP: u128 = 0x1ff8;
    const RETURN_ADDRESS: u128 = 0x401005;

    let mut witness = straight_line_witness(vec![
        x86_64_call_0x401010(0x401000),
        x86_64_ret(0x401010),
        x86_64_nop(RETURN_ADDRESS as u64),
    ]);

    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step0));

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record(
        "RSP",
        64,
        CALL_FRAME_SP,
        step1.clone(),
    ));
    if include_return_slot_witness {
        witness.trace[1].assignments.push(stack_trace_record(0, 8, RETURN_ADDRESS, step1));
    }

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step2));
    witness
}

fn x86_indirect_call_ret_stack_witness(include_target_witness: bool) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const CALL_FRAME_SP: u128 = 0x1ff8;
    const TARGET_ADDRESS: u128 = 0x401010;
    const RETURN_ADDRESS: u128 = 0x401002;

    let mut witness = straight_line_witness(vec![
        x86_64_call_rax(0x401000),
        x86_64_ret(TARGET_ADDRESS as u64),
        x86_64_nop(RETURN_ADDRESS as u64),
    ]);

    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step0.clone()));
    if include_target_witness {
        witness.trace[0].assignments.push(register_trace_record("RAX", 64, TARGET_ADDRESS, step0));
    }

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record(
        "RSP",
        64,
        CALL_FRAME_SP,
        step1.clone(),
    ));
    witness.trace[1].assignments.push(stack_trace_record(0, 8, RETURN_ADDRESS, step1));

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step2));
    witness
}

fn x86_memory_indirect_call_ret_stack_witness(
    include_target_memory_witness: bool,
) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const CALL_FRAME_SP: u128 = 0x1ff8;
    const TARGET_POINTER: u128 = 0x3000;
    const TARGET_ADDRESS: u128 = 0x401010;
    const RETURN_ADDRESS: u128 = 0x401002;

    let mut witness = straight_line_witness(vec![
        x86_64_call_ptr_rax(0x401000),
        x86_64_ret(TARGET_ADDRESS as u64),
        x86_64_nop(RETURN_ADDRESS as u64),
    ]);

    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step0.clone()));
    witness.trace[0].assignments.push(register_trace_record(
        "RAX",
        64,
        TARGET_POINTER,
        step0.clone(),
    ));
    if include_target_memory_witness {
        witness.trace[0].assignments.push(memory_trace_record(
            "call_target_ptr",
            TARGET_POINTER as u64,
            8,
            TARGET_ADDRESS,
            step0,
        ));
    }

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record(
        "RSP",
        64,
        CALL_FRAME_SP,
        step1.clone(),
    ));
    witness.trace[1].assignments.push(stack_trace_record(0, 8, RETURN_ADDRESS, step1));

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("RSP", 64, STACK_TOP, step2));
    witness
}

fn aarch64_call_ret_stack_witness(include_return_slot_witness: bool) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const FRAME_SP: u128 = 0x1ff0;
    const RETURN_ADDRESS: u128 = 0x401004;

    let mut witness = straight_line_witness(vec![
        aarch64_bl_plus_8(0x401000),
        aarch64_stp_x29_x30_sp_pre_dec16(0x401008),
        aarch64_ldp_x29_x30_sp_post_inc16(0x40100c),
        aarch64_ret(0x401010),
        aarch64_nop(RETURN_ADDRESS as u64),
    ]);

    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("SP", 64, STACK_TOP, step0));

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record("SP", 64, STACK_TOP, step1.clone()));
    witness.trace[1].assignments.push(register_trace_record("X30", 64, RETURN_ADDRESS, step1));

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("SP", 64, FRAME_SP, step2.clone()));
    if include_return_slot_witness {
        witness.trace[2].assignments.push(stack_trace_record(8, 8, RETURN_ADDRESS, step2));
    }

    let step3 = witness.trace[3].program_point.clone();
    witness.trace[3].assignments.push(register_trace_record("SP", 64, STACK_TOP, step3.clone()));
    witness.trace[3].assignments.push(register_trace_record("X30", 64, RETURN_ADDRESS, step3));

    let step4 = witness.trace[4].program_point.clone();
    witness.trace[4].assignments.push(register_trace_record("SP", 64, STACK_TOP, step4));
    witness
}

fn aarch64_indirect_call_ret_stack_witness(
    include_target_witness: bool,
    include_return_slot_witness: bool,
) -> BinaryWitness {
    const STACK_TOP: u128 = 0x2000;
    const FRAME_SP: u128 = 0x1ff0;
    const TARGET_ADDRESS: u128 = 0x401008;
    const RETURN_ADDRESS: u128 = 0x401004;

    let mut witness = straight_line_witness(vec![
        aarch64_blr_x8(0x401000),
        aarch64_stp_x29_x30_sp_pre_dec16(TARGET_ADDRESS as u64),
        aarch64_ldp_x29_x30_sp_post_inc16(0x40100c),
        aarch64_ret(0x401010),
        aarch64_nop(RETURN_ADDRESS as u64),
    ]);

    let step0 = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(register_trace_record("SP", 64, STACK_TOP, step0.clone()));
    if include_target_witness {
        witness.trace[0].assignments.push(register_trace_record("X8", 64, TARGET_ADDRESS, step0));
    }

    let step1 = witness.trace[1].program_point.clone();
    witness.trace[1].assignments.push(register_trace_record("SP", 64, STACK_TOP, step1.clone()));
    witness.trace[1].assignments.push(register_trace_record("X30", 64, RETURN_ADDRESS, step1));

    let step2 = witness.trace[2].program_point.clone();
    witness.trace[2].assignments.push(register_trace_record("SP", 64, FRAME_SP, step2.clone()));
    if include_return_slot_witness {
        witness.trace[2].assignments.push(stack_trace_record(8, 8, RETURN_ADDRESS, step2));
    }

    let step3 = witness.trace[3].program_point.clone();
    witness.trace[3].assignments.push(register_trace_record("SP", 64, STACK_TOP, step3.clone()));
    witness.trace[3].assignments.push(register_trace_record("X30", 64, RETURN_ADDRESS, step3));

    let step4 = witness.trace[4].program_point.clone();
    witness.trace[4].assignments.push(register_trace_record("SP", 64, STACK_TOP, step4));
    witness
}

fn aarch64_indirect_branch_witness(include_target_witness: bool) -> BinaryWitness {
    const TARGET_ADDRESS: u128 = 0x401020;

    let mut witness =
        straight_line_witness(vec![aarch64_br_x16(0x401000), aarch64_nop(TARGET_ADDRESS as u64)]);
    if include_target_witness {
        let step0 = witness.trace[0].program_point.clone();
        witness.trace[0].assignments.push(register_trace_record("X16", 64, TARGET_ADDRESS, step0));
    }
    witness
}

fn image(
    architecture: BoundedMachineCodeArchitecture,
    instructions: impl IntoIterator<Item = (u64, Vec<u8>)>,
) -> BoundedMachineCodeImage {
    let mut image = BoundedMachineCodeImage::new(architecture)
        .with_artifact_digest(test_artifact_digest())
        .with_selected_image(test_selected_image());
    for (address, bytes) in instructions {
        image.insert_instruction_at_file_offset(
            address,
            test_instruction_file_offset(address),
            bytes,
        );
    }
    image
}

fn test_instruction_file_offset(address: u64) -> u64 {
    address.saturating_sub(0x401000)
}

fn image_with_identity(
    artifact_digest: Option<BinaryArtifactDigest>,
    selected_image: Option<BinarySelectedImageIdentity>,
) -> BoundedMachineCodeImage {
    let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64);
    if let Some(artifact_digest) = artifact_digest {
        image = image.with_artifact_digest(artifact_digest);
    }
    if let Some(selected_image) = selected_image {
        image = image.with_selected_image(selected_image);
    }
    image.insert_instruction_at_file_offset(0x401000, 0, AARCH64_NOP_BYTES);
    image
}

fn checked_in_x86_64_load_replay_input(
    origins: Vec<TrustBinaryOrigin>,
    selected_image: BinarySelectedImageIdentity,
) -> BinaryReplayInput {
    let mut step0_assignments = BTreeMap::new();
    step0_assignments.insert("RDI".to_owned(), format!("0x{X86_64_LOAD_MEMORY_ADDRESS:x}"));
    step0_assignments.insert(
        format!("mem[0x{X86_64_LOAD_MEMORY_ADDRESS:x}:8]"),
        format!("0x{X86_64_LOAD_MEMORY_VALUE:x}"),
    );
    let trace = CounterexampleTrace::new(vec![TraceStep {
        step: 0,
        assignments: step0_assignments,
        program_point: Some(format!("bb0@0x{X86_64_LOAD_ENTRY:x}")),
    }]);
    let counterexample = Counterexample::with_trace(
        vec![
            ("RDI".to_owned(), CounterexampleValue::Uint(X86_64_LOAD_MEMORY_ADDRESS as u128)),
            (
                format!("mem[0x{X86_64_LOAD_MEMORY_ADDRESS:x}:8]"),
                CounterexampleValue::Uint(X86_64_LOAD_MEMORY_VALUE),
            ),
        ],
        trace,
    );

    BinaryReplayInput::new(counterexample)
        .with_artifact_digest(BinaryArtifactDigest::sha256(X86_64_LOAD_FIXTURE_SHA256))
        .with_selected_image(selected_image)
        .with_instruction_provenance(origins)
        .with_verification_condition(VerificationCondition {
            kind: VcKind::Assertion { message: "checked-in x86_64 load replay witness".to_owned() },
            function: "trust_fixture_x86_load".into(),
            location: SourceSpan::binary_address(X86_64_LOAD_ENTRY),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .require_selected_image_identity()
}

fn checked_in_x86_64_load_backend(
    selected_image: BinarySelectedImageIdentity,
) -> BoundedMachineCodeReplayBackend {
    let fixture_bytes = checked_in_x86_64_load_fixture_bytes();
    let mut image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::X86_64)
        .with_image(X86_64_LOAD_FIXTURE_PATH)
        .with_artifact_digest(BinaryArtifactDigest::sha256(X86_64_LOAD_FIXTURE_SHA256))
        .with_selected_image(selected_image)
        .with_selected_image_bytes(&fixture_bytes);
    image.insert_segment(
        X86_64_LOAD_ENTRY,
        fixture_bytes.len() as u64,
        BoundedMachineCodeSegmentPermissions::rx(),
    );
    image.insert_segment(X86_64_LOAD_MEMORY_ADDRESS, 8, BoundedMachineCodeSegmentPermissions::rw());
    image.insert_instruction_at_file_offset(
        X86_64_LOAD_ENTRY,
        X86_64_LOAD_TEXT_FILE_OFFSET,
        X86_64_LOAD_INSTRUCTION_BYTES,
    );
    BoundedMachineCodeReplayBackend::new(image)
}

fn assert_unsupported_control_flow_report(
    report: &BinaryMachineReplayReport,
    address: u64,
    expected_bytes: &[u8],
    expected_flow: &str,
    expected_reason: &str,
) {
    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].step, Some(0));
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, address);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes.as_slice(),
        expected_bytes
    );
    assert!(report.reason.contains("unsupported"));
    assert!(report.reason.contains(expected_reason), "{}", report.reason);
    assert!(report.reason.contains(expected_flow), "{}", report.reason);
    assert!(report.reason.contains(&format!("0x{address:x}")), "{}", report.reason);
    assert!(report.reason.contains("step 0"), "{}", report.reason);
    assert!(report.reason.contains("expected trace length 1"), "{}", report.reason);
}

#[derive(Debug, Clone)]
struct AddressOnlyReplayBackend {
    origin: TrustBinaryOrigin,
}

impl BinaryMachineReplayBackend for AddressOnlyReplayBackend {
    fn replay(&self, _request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        BinaryMachineReplayResult::replayed(
            "address-only",
            vec![BinaryMachineInstructionEvidence::new(self.origin.clone())],
        )
        .with_artifact_digest(test_artifact_digest())
    }
}

#[derive(Debug, Clone)]
struct CapabilityReplayBackend {
    origin: TrustBinaryOrigin,
    capability_evidence: BinaryMachineReplayCapabilityEvidence,
}

impl BinaryMachineReplayBackend for CapabilityReplayBackend {
    fn replay(&self, _request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        BinaryMachineReplayResult::replayed(
            "capability",
            vec![BinaryMachineInstructionEvidence { origin: self.origin.clone(), step: Some(0) }],
        )
        .with_capability_evidence(vec![self.capability_evidence.clone()])
        .with_artifact_digest(test_artifact_digest())
    }
}

#[derive(Debug, Clone)]
struct EffectlessReplayBackend {
    origin: TrustBinaryOrigin,
}

impl BinaryMachineReplayBackend for EffectlessReplayBackend {
    fn replay(&self, _request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        let instruction =
            BinaryMachineInstructionEvidence { origin: self.origin.clone(), step: Some(0) };
        BinaryMachineReplayResult::replayed("effectless", vec![instruction.clone()])
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image())
            .with_byte_range_evidence(vec![BinaryMachineReplayByteRangeEvidence::new(
                instruction.origin.instruction_address,
                instruction.step,
                test_instruction_file_offset(instruction.origin.instruction_address),
                instruction.origin.instruction_bytes.len() as u64,
                instruction.origin.instruction_bytes,
            )])
    }
}

#[derive(Debug, Clone)]
struct GenericMemoryEffectReplayBackend {
    origin: TrustBinaryOrigin,
    kind: BinaryMachineReplayEffectKind,
}

impl BinaryMachineReplayBackend for GenericMemoryEffectReplayBackend {
    fn replay(&self, _request: &BinaryMachineReplayRequest<'_>) -> BinaryMachineReplayResult {
        let instruction =
            BinaryMachineInstructionEvidence { origin: self.origin.clone(), step: Some(0) };
        let effect = BinaryMachineReplayEffectEvidence::new(
            self.kind,
            "AArch64",
            instruction.origin.instruction_address,
            "mock backend consumed generic scalar memory effect witness",
        )
        .with_step(instruction.step)
        .with_witness_step(instruction.step)
        .with_subject("memory_access#0:8B");

        BinaryMachineReplayResult::replayed("generic-memory-effect", vec![instruction.clone()])
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image())
            .with_effect_evidence(vec![effect])
            .with_byte_range_evidence(vec![BinaryMachineReplayByteRangeEvidence::new(
                instruction.origin.instruction_address,
                instruction.step,
                test_instruction_file_offset(instruction.origin.instruction_address),
                instruction.origin.instruction_bytes.len() as u64,
                instruction.origin.instruction_bytes,
            )])
    }
}

fn traced_counterexample(address: u64) -> Counterexample {
    let mut trace_assignments = BTreeMap::new();
    trace_assignments.insert("_local0".to_string(), "1".to_string());
    Counterexample::with_trace(
        vec![("_local0".into(), CounterexampleValue::Int(1))],
        CounterexampleTrace::new(vec![TraceStep {
            step: 0,
            assignments: trace_assignments,
            program_point: Some(format!("bb0@0x{address:x}")),
        }]),
    )
}

fn sat_dispatch_with_witness() -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: "sat-vc0".to_string(),
        function: Some("sym.main".to_string()),
        origin: Some(aarch64_nop(0x401000)),
        solver: "ay".to_string(),
        status: SolverDispatchStatus::Sat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(VerificationResult::Failed {
            solver: "ay".into(),
            time_ms: 1,
            counterexample: Some(traced_counterexample(0x401000)),
        }),
        binary_artifact_digest_identity: Some(test_artifact_digest_identity()),
        ..Default::default()
    }
}

fn unsat_dispatch_with_certificate(certificate: ProofCertificateStatus) -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: "unsat-vc0".to_string(),
        function: Some("sym.main".to_string()),
        origin: Some(aarch64_nop(0x401000)),
        solver: "ay".to_string(),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        certificate,
        ..Default::default()
    }
}

fn unknown_dispatch() -> SolverDispatchRecord {
    SolverDispatchRecord {
        id: "unknown-vc0".to_string(),
        function: Some("sym.main".to_string()),
        origin: Some(aarch64_nop(0x401000)),
        solver: "ay".to_string(),
        status: SolverDispatchStatus::Unknown,
        query_semantics: SolverQuerySemantics::Unknown,
        result: Some(VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 1,
            reason: "unsupported theory".to_string(),
        }),
        ..Default::default()
    }
}

#[test]
fn exact_machine_replay_requires_observed_instruction_bytes() {
    let origin = x86_64_nop(0x401000);
    let mut observed = origin.clone();
    observed.instruction_bytes.clear();
    let witness = straight_line_witness(vec![origin]);
    let backend = AddressOnlyReplayBackend { origin: observed };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert!(report.reason.contains("exact observed instruction bytes"));
}

#[test]
fn exact_machine_replay_requires_normalized_witness_instruction_bytes() {
    let origin = x86_64_nop(0x401000);
    let mut expected = origin.clone();
    expected.instruction_bytes.clear();
    let witness = straight_line_witness(vec![expected]);
    let backend = AddressOnlyReplayBackend { origin };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert!(report.reason.contains("normalized witness provenance"));
    assert!(report.reason.contains("exact normalized instruction-byte provenance"));
}

#[test]
fn bounded_machine_mapped_aarch64_straight_line_replay_reports_replayed() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000), aarch64_nop(0x401004)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec()), (0x401004, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(
        report.observed_instruction_trace[1].origin.instruction_bytes,
        AARCH64_NOP_BYTES.to_vec()
    );
}

#[test]
fn bounded_machine_replay_producer_fails_closed_without_canonical_identity_evidence() {
    let mut witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    witness.provenance.requires_selected_image_identity = true;
    let noncanonical_artifact =
        BinaryArtifactDigest::sha256(TEST_ARTIFACT_SHA256.to_ascii_uppercase());
    let mut noncanonical_selected_image = test_selected_image();
    noncanonical_selected_image.sha256 =
        TEST_SELECTED_IMAGE_SHA256.to_ascii_uppercase().to_string();

    let missing_root = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(image_with_identity(
            None,
            Some(test_selected_image()),
        )),
    );
    assert_eq!(missing_root.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(missing_root.trust_types_status, ReplayStatus::NotAttempted);
    assert_eq!(missing_root.expected_artifact_digest, Some(test_artifact_digest()));
    assert_eq!(missing_root.observed_artifact_digest, None);
    assert_eq!(missing_root.observed_selected_image, Some(test_selected_image()));
    assert!(missing_root.reason.contains("omitted root binary artifact digest"));
    assert!(!missing_root.source_backprop_replay_ready());

    let invalid_root = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(image_with_identity(
            Some(noncanonical_artifact.clone()),
            Some(test_selected_image()),
        )),
    );
    assert_eq!(invalid_root.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(invalid_root.observed_artifact_digest, Some(noncanonical_artifact));
    assert!(invalid_root.reason.contains("root binary artifact digest is not canonical"));
    assert!(!invalid_root.source_backprop_replay_ready());

    let missing_selected = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(image_with_identity(
            Some(test_artifact_digest()),
            None,
        )),
    );
    assert_eq!(missing_selected.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert!(missing_selected.matched_artifact_digest);
    assert_eq!(missing_selected.expected_selected_image, Some(test_selected_image()));
    assert_eq!(missing_selected.observed_selected_image, None);
    assert!(missing_selected.reason.contains("omitted selected-image digest/range"));
    assert!(!missing_selected.source_backprop_replay_ready());

    let invalid_selected = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(image_with_identity(
            Some(test_artifact_digest()),
            Some(noncanonical_selected_image.clone()),
        )),
    );
    assert_eq!(invalid_selected.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert!(invalid_selected.matched_artifact_digest);
    assert_eq!(invalid_selected.observed_selected_image, Some(noncanonical_selected_image));
    assert!(invalid_selected.reason.contains("selected-image digest/range is not canonical"));
    assert!(!invalid_selected.source_backprop_replay_ready());
}

#[test]
fn bounded_machine_mapped_aarch64_scalar_replay_advances_by_exact_sizes() {
    let witness = straight_line_witness(vec![
        aarch64_movz_x0_42(0x401000),
        aarch64_add_x0_x1_x2(0x401004),
        aarch64_sub_x0_x1_x2(0x401008),
    ]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_MOVZ_X0_42_BYTES.to_vec()),
            (0x401004, AARCH64_ADD_X0_X1_X2_BYTES.to_vec()),
            (0x401008, AARCH64_SUB_X0_X1_X2_BYTES.to_vec()),
        ],
    ))
    .with_max_instructions(3);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    let expected_addresses = [0x401000, 0x401004, 0x401008];
    assert_eq!(
        report
            .expected_instruction_trace
            .iter()
            .map(|origin| origin.instruction_address)
            .collect::<Vec<_>>(),
        expected_addresses.to_vec()
    );
    assert_eq!(report.observed_instruction_trace.len(), 3);

    let expected_bytes = [
        AARCH64_MOVZ_X0_42_BYTES.to_vec(),
        AARCH64_ADD_X0_X1_X2_BYTES.to_vec(),
        AARCH64_SUB_X0_X1_X2_BYTES.to_vec(),
    ];
    for (idx, evidence) in report.observed_instruction_trace.iter().enumerate() {
        assert_eq!(evidence.step, Some(idx as u32));
        assert_eq!(evidence.origin.instruction_address, expected_addresses[idx]);
        assert_eq!(evidence.origin.instruction_size, Some(4));
        assert_eq!(evidence.origin.instruction_bytes, expected_bytes[idx]);
    }
    for pair in report.observed_instruction_trace.windows(2) {
        let previous = &pair[0].origin;
        let next = &pair[1].origin;
        assert_eq!(
            next.instruction_address,
            previous.instruction_address
                + u64::from(previous.instruction_size.expect("observed instruction size"))
        );
    }
}

#[test]
fn bounded_machine_mapped_aarch64_store_then_load_replay_reports_replayed() {
    let witness =
        straight_line_witness(vec![aarch64_str_x0_x1(0x401000), aarch64_ldr_x2_x1(0x401004)]);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_STR_X0_X1_BYTES.to_vec()),
            (0x401004, AARCH64_LDR_X2_X1_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x8, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x0, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert!(report.matched_effect_evidence, "{report:?}");
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_STR_X0_X1_BYTES.to_vec()
    );
    assert_eq!(
        report.observed_instruction_trace[1].origin.instruction_bytes,
        AARCH64_LDR_X2_X1_BYTES.to_vec()
    );

    let write = report
        .effect_evidence
        .iter()
        .find(|evidence| {
            evidence.kind == BinaryMachineReplayEffectKind::MemoryWrite && evidence.step == Some(0)
        })
        .expect("STR must consume concrete scalar memory-write evidence");
    assert_eq!(write.subject.as_deref(), Some("memory_access#0:8B"));
    let write_access = write.memory_access.expect("memory write must carry concrete range");
    assert_eq!(write_access.address, 0);
    assert_eq!(write_access.width_bytes, 8);

    let read = report
        .effect_evidence
        .iter()
        .find(|evidence| {
            evidence.kind == BinaryMachineReplayEffectKind::MemoryRead && evidence.step == Some(1)
        })
        .expect("LDR must consume concrete scalar memory-read evidence");
    assert_eq!(read.subject.as_deref(), Some("memory_access#0:8B"));
    let read_access = read.memory_access.expect("memory read must carry concrete range");
    assert_eq!(read_access.address, 0);
    assert_eq!(read_access.width_bytes, 8);

    let json = serde_json::to_value(&report).expect("serialize replay report");
    let effect_json = json["effect_evidence"]
        .as_array()
        .expect("effect evidence array")
        .iter()
        .find(|entry| entry["kind"] == "memory_write" && entry["step"] == serde_json::json!(0))
        .expect("serialized memory-write evidence");
    assert_eq!(effect_json["memory_access"]["address"], serde_json::json!(0));
    assert_eq!(effect_json["memory_access"]["width_bytes"], serde_json::json!(8));
}

#[test]
fn bounded_machine_mapped_aarch64_conditional_branch_taken_replay_reports_replayed() {
    let witness =
        straight_line_witness(vec![aarch64_cbz_wzr_plus_8(0x401000), aarch64_nop(0x401008)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_CBZ_WZR_PLUS_8_BYTES.to_vec()), (0x401008, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_capability_evidence);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(report.capability_evidence.len(), 1);
    assert_eq!(
        report.capability_evidence[0].capability,
        BinaryMachineReplayCapability::ConditionalBranch
    );
    assert_eq!(report.capability_evidence[0].instruction_address, 0x401000);
    assert_eq!(report.capability_evidence[0].step, Some(0));
    assert!(
        report.capability_evidence[0].validation.contains("conditional branch"),
        "{:?}",
        report.capability_evidence[0]
    );
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_CBZ_WZR_PLUS_8_BYTES.to_vec()
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401008);
}

#[test]
fn bounded_machine_mapped_aarch64_conditional_branch_fallthrough_replay_reports_replayed() {
    let witness =
        straight_line_witness(vec![aarch64_cbnz_wzr_plus_8(0x401000), aarch64_nop(0x401004)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_CBNZ_WZR_PLUS_8_BYTES.to_vec()),
            (0x401004, AARCH64_NOP_BYTES.to_vec()),
        ],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_CBNZ_WZR_PLUS_8_BYTES.to_vec()
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401004);
}

#[test]
fn bounded_machine_supported_sequence_requires_exact_bytes_and_sizes_for_replay() {
    let witness = straight_line_witness(vec![
        aarch64_movz_x0_42(0x401000),
        aarch64_add_x0_x1_x2(0x401004),
        aarch64_sub_x0_x1_x2(0x401008),
    ]);
    let exact_backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_MOVZ_X0_42_BYTES.to_vec()),
            (0x401004, AARCH64_ADD_X0_X1_X2_BYTES.to_vec()),
            (0x401008, AARCH64_SUB_X0_X1_X2_BYTES.to_vec()),
        ],
    ));

    let exact_report =
        replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &exact_backend);

    assert_eq!(exact_report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(exact_report.trust_types_status, ReplayStatus::Replayed);
    assert!(exact_report.matched_instruction_trace);
    assert_eq!(exact_report.observed_instruction_trace.len(), 3);

    let byte_mismatch_backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_MOVZ_X0_42_BYTES.to_vec()),
            (0x401004, AARCH64_SUB_X0_X1_X2_BYTES.to_vec()),
            (0x401008, AARCH64_SUB_X0_X1_X2_BYTES.to_vec()),
        ],
    ));

    let byte_mismatch_report = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &byte_mismatch_backend,
    );

    assert_eq!(byte_mismatch_report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(byte_mismatch_report.trust_types_status, ReplayStatus::Spurious);
    assert_ne!(byte_mismatch_report.trust_types_status, ReplayStatus::Replayed);
    assert!(!byte_mismatch_report.matched_instruction_trace);
    assert!(byte_mismatch_report.reason.contains("instruction bytes"));

    let mut wrong_size_origins = vec![
        aarch64_movz_x0_42(0x401000),
        aarch64_add_x0_x1_x2(0x401004),
        aarch64_sub_x0_x1_x2(0x401008),
    ];
    wrong_size_origins[1].instruction_size = Some(8);
    let wrong_size_witness = straight_line_witness(wrong_size_origins);

    let size_mismatch_report = replay_machine_witness(
        &wrong_size_witness,
        &BinaryMachineReplayConfig::default(),
        &exact_backend,
    );

    assert_eq!(size_mismatch_report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(size_mismatch_report.trust_types_status, ReplayStatus::Spurious);
    assert_ne!(size_mismatch_report.trust_types_status, ReplayStatus::Replayed);
    assert!(!size_mismatch_report.matched_instruction_trace);
    assert!(size_mismatch_report.reason.contains("instruction size"));
}

#[test]
fn bounded_machine_mapped_x86_64_straight_line_replay_reports_replayed() {
    let witness = straight_line_witness(vec![x86_64_nop(0x401000), x86_64_nop(0x401001)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::X86_64,
        [(0x401000, X86_64_NOP_BYTES.to_vec()), (0x401001, X86_64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(
        report.observed_instruction_trace[1].origin.instruction_bytes,
        X86_64_NOP_BYTES.to_vec()
    );
}

#[test]
fn bounded_machine_mapped_x86_64_movabs_replay_advances_by_exact_size() {
    let witness =
        straight_line_witness(vec![x86_64_movabs_rax_imm64(0x401000), x86_64_nop(0x40100a)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::X86_64,
        [(0x401000, X86_64_MOVABS_RAX_IMM64_BYTES.to_vec()), (0x40100a, X86_64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_size, Some(10));
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_MOVABS_RAX_IMM64_BYTES.to_vec()
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x40100a);
}

#[test]
fn bounded_machine_mapped_x86_64_store_then_load_replay_reports_replayed() {
    let witness = straight_line_witness(vec![
        x86_64_mov_ptr_rax_rax(0x401000),
        x86_64_mov_rcx_ptr_rax(0x401003),
    ]);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_MOV_PTR_RAX_RAX_BYTES.to_vec()),
            (0x401003, X86_64_MOV_RCX_PTR_RAX_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x6, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x0, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_size, Some(3));
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401003);
}

#[test]
fn checked_in_x86_64_load_model_witness_replays_against_original_bytes_golden() {
    let selected_image = checked_in_x86_64_load_selected_image();
    let origin = checked_in_x86_64_load_instruction_origin(
        X86_64_LOAD_ENTRY,
        X86_64_LOAD_TEXT_FILE_OFFSET,
        X86_64_LOAD_INSTRUCTION_BYTES,
    );
    let input = checked_in_x86_64_load_replay_input(vec![origin.clone()], selected_image.clone());
    let backend = checked_in_x86_64_load_backend(selected_image.clone());

    let report = replay_binary_counterexample_with_machine_replay(
        BinaryReplayTarget::binary_origin(BinaryOrigin {
            image: Some(X86_64_LOAD_FIXTURE_PATH.to_owned()),
            architecture: Some("x86_64".to_owned()),
            function: Some("trust_fixture_x86_load".to_owned()),
            entry: Some(X86_64_LOAD_ENTRY),
        }),
        &input,
        &BinaryReplayConfig::default(),
        &BinaryMachineReplayConfig::default(),
        &backend,
    );
    let machine = &report.machine_replay;

    assert_eq!(machine.status, BinaryMachineReplayStatus::Replayed, "{}", machine.reason);
    assert_eq!(machine.trust_types_status, ReplayStatus::Replayed);
    assert!(machine.matched_instruction_trace);
    assert!(machine.matched_artifact_digest);
    assert!(machine.matched_selected_image);
    assert!(machine.matched_effect_evidence, "{:?}", machine.effect_diagnostics);
    assert!(machine.source_backprop_replay_ready(), "{machine:?}");
    assert_eq!(machine.expected_selected_image, Some(selected_image.clone()));
    assert_eq!(machine.observed_selected_image, Some(selected_image.clone()));
    assert_eq!(machine.expected_instruction_trace, vec![origin.clone()]);
    assert_eq!(machine.observed_instruction_trace.len(), 1);
    assert_eq!(machine.observed_instruction_trace[0].step, Some(0));
    assert_eq!(
        machine.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_LOAD_INSTRUCTION_BYTES.to_vec()
    );
    assert_eq!(machine.byte_range_evidence.len(), 1);
    assert_eq!(machine.byte_range_evidence[0].instruction_address, X86_64_LOAD_ENTRY);
    assert_eq!(machine.byte_range_evidence[0].step, Some(0));
    assert_eq!(machine.byte_range_evidence[0].file_offset, X86_64_LOAD_TEXT_FILE_OFFSET);
    assert_eq!(
        machine.byte_range_evidence[0].instruction_bytes.as_slice(),
        X86_64_LOAD_INSTRUCTION_BYTES
    );
    assert_eq!(machine.attestation_slices.len(), 1);
    assert_eq!(
        machine.attestation_slices[0].status,
        BinaryMachineReplayAttestationStatus::Accepted
    );
    assert_eq!(machine.attestation_slices[0].selected_image, Some(selected_image.clone()));

    let replay_transcript_digest = machine
        .replay_transcript_digest
        .as_deref()
        .expect("replayed machine witness should bind a transcript digest");
    assert_canonical_sha256_digest(replay_transcript_digest);
    let mut stale_transcript = machine.clone();
    stale_transcript.replay_transcript_digest =
        Some("0000000000000000000000000000000000000000000000000000000000000000".to_owned());
    let stale_transcript_blocker = stale_transcript
        .source_backprop_replay_blocker_reason()
        .expect("stale transcript digest should block source backprop");
    assert!(stale_transcript_blocker.contains("replay transcript digest"));
    let vc_context = report
        .normalized_witness
        .provenance
        .verification_context
        .as_ref()
        .expect("model witness should retain VC context");
    assert_canonical_sha256_digest(&vc_context.vc_digest);

    let memory_read = machine
        .effect_evidence
        .iter()
        .find(|evidence| evidence.kind == BinaryMachineReplayEffectKind::MemoryRead)
        .expect("x86_64 load should consume a memory-read effect");
    assert_eq!(memory_read.step, Some(0));
    assert_eq!(
        memory_read.memory_access.expect("memory-read effect should bind concrete address").address,
        X86_64_LOAD_MEMORY_ADDRESS
    );
    assert_eq!(
        memory_read.memory_access.expect("memory-read effect should bind width").width_bytes,
        8
    );
    assert!(
        machine
            .effect_evidence
            .iter()
            .any(|evidence| evidence.kind == BinaryMachineReplayEffectKind::RegisterWrite
                && evidence.subject.as_deref() == Some("GPR0:64"))
    );
    assert!(
        machine.attestation_slices[0]
            .effect_identities
            .iter()
            .any(|effect| effect.kind == BinaryMachineReplayEffectKind::MemoryRead)
    );
    assert!(
        machine.attestation_slices[0]
            .effect_identities
            .iter()
            .any(|effect| effect.kind == BinaryMachineReplayEffectKind::RegisterWrite)
    );

    let mut effect_kinds = machine
        .effect_evidence
        .iter()
        .map(|evidence| evidence.kind.to_string())
        .collect::<Vec<_>>();
    effect_kinds.sort();
    let golden = serde_json::json!({
        "fixture": X86_64_LOAD_FIXTURE_PATH,
        "root_artifact_sha256": X86_64_LOAD_FIXTURE_SHA256,
        "selected_image": {
            "file_offset": 0,
            "file_size": checked_in_x86_64_load_fixture_bytes().len(),
            "sha256": X86_64_LOAD_FIXTURE_SHA256,
        },
        "path": {
            "trace_program_points": report.normalized_witness.provenance.trace_program_points.clone(),
            "machine_step": machine.observed_instruction_trace[0].step,
            "instruction_address": X86_64_LOAD_ENTRY,
        },
        "instruction": {
            "file_offset": machine.byte_range_evidence[0].file_offset,
            "size": machine.byte_range_evidence[0].size,
            "bytes": machine.byte_range_evidence[0].instruction_bytes.clone(),
        },
        "model_assignments": report.normalized_witness.provenance.model_assignment_names.clone(),
        "effect_kinds": effect_kinds,
        "memory_read": {
            "address": memory_read.memory_access.unwrap().address,
            "width_bytes": memory_read.memory_access.unwrap().width_bytes,
        },
        "vc": {
            "function": vc_context.function.clone(),
            "kind": vc_context.kind.clone(),
            "location": vc_context.location.file.clone(),
            "digest": vc_context.vc_digest.clone(),
        },
        "replay_transcript_digest": replay_transcript_digest,
    });
    assert_eq!(
        golden,
        serde_json::json!({
            "fixture": "tests/fixtures/binary_decomp/x86_64-load-elf.hex",
            "root_artifact_sha256": "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000",
            "selected_image": {
                "file_offset": 0,
                "file_size": 576,
                "sha256": "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000",
            },
            "path": {
                "trace_program_points": ["bb0@0x400000"],
                "machine_step": 0,
                "instruction_address": 0x400000,
            },
            "instruction": {
                "file_offset": 0x78,
                "size": 3,
                "bytes": [0x48, 0x8b, 0x07],
            },
            "model_assignments": ["RDI", "mem[0x2000:8]"],
            "effect_kinds": ["memory_read", "program_counter_update", "register_write"],
            "memory_read": {
                "address": 0x2000,
                "width_bytes": 8,
            },
            "vc": {
                "function": "trust_fixture_x86_load",
                "kind": "{\"Assertion\":{\"message\":\"checked-in x86_64 load replay witness\"}}",
                "location": "binary:0x400000",
                "digest": "7c0c0f8922dfcab54b767468c0f05a667c62103b54893920105ec3fa9c650ded",
            },
            "replay_transcript_digest": "14ec54fa0d854d0be174ad7522bf9cd0a4cdb5ede072d03a13b88afbac3e9dbf",
        })
    );
}

#[test]
fn checked_in_x86_64_load_replay_rejects_stale_selected_image_digest() {
    let mut stale_selected_image = checked_in_x86_64_load_selected_image();
    stale_selected_image.sha256 =
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_owned();
    let origin = checked_in_x86_64_load_instruction_origin(
        X86_64_LOAD_ENTRY,
        X86_64_LOAD_TEXT_FILE_OFFSET,
        X86_64_LOAD_INSTRUCTION_BYTES,
    );
    let input = checked_in_x86_64_load_replay_input(vec![origin], stale_selected_image.clone());
    let backend = checked_in_x86_64_load_backend(stale_selected_image);

    let report = replay_binary_counterexample_with_machine_replay(
        BinaryReplayTarget::binary_origin(BinaryOrigin {
            image: Some(X86_64_LOAD_FIXTURE_PATH.to_owned()),
            architecture: Some("x86_64".to_owned()),
            function: Some("trust_fixture_x86_load".to_owned()),
            entry: Some(X86_64_LOAD_ENTRY),
        }),
        &input,
        &BinaryReplayConfig::default(),
        &BinaryMachineReplayConfig::default(),
        &backend,
    );
    let machine = &report.machine_replay;

    assert_eq!(machine.status, BinaryMachineReplayStatus::Spurious);
    assert!(!machine.source_backprop_replay_ready());
    assert!(machine.reason.contains("selected-image digest is stale"), "{}", machine.reason);
    assert!(machine.observed_instruction_trace.is_empty());
    assert_eq!(machine.byte_range_diagnostics.len(), 1);
    assert_eq!(
        machine.byte_range_diagnostics[0].kind,
        BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageDigestMismatch
    );
    assert!(machine.replay_transcript_digest.is_some());
}

#[test]
fn checked_in_x86_64_load_replay_rejects_path_mismatch_against_original_bytes() {
    let selected_image = checked_in_x86_64_load_selected_image();
    let load_origin = checked_in_x86_64_load_instruction_origin(
        X86_64_LOAD_ENTRY,
        X86_64_LOAD_TEXT_FILE_OFFSET,
        X86_64_LOAD_INSTRUCTION_BYTES,
    );
    let skipped_ret_origin = checked_in_x86_64_load_instruction_origin(
        X86_64_LOAD_ENTRY + 4,
        X86_64_LOAD_TEXT_FILE_OFFSET + 4,
        X86_64_LOAD_NOP_BYTES,
    );
    let mut input = checked_in_x86_64_load_replay_input(
        vec![load_origin, skipped_ret_origin],
        selected_image.clone(),
    );
    input
        .counterexample
        .trace
        .as_mut()
        .expect("fixture counterexample should carry trace")
        .steps
        .push(TraceStep {
            step: 1,
            assignments: BTreeMap::new(),
            program_point: Some(format!("bb1@0x{:x}", X86_64_LOAD_ENTRY + 4)),
        });
    let mut image = checked_in_x86_64_load_backend(selected_image).image;
    image.insert_instruction_at_file_offset(
        X86_64_LOAD_ENTRY + 4,
        X86_64_LOAD_TEXT_FILE_OFFSET + 4,
        X86_64_LOAD_NOP_BYTES,
    );
    let backend = BoundedMachineCodeReplayBackend::new(image);

    let report = replay_binary_counterexample_with_machine_replay(
        BinaryReplayTarget::binary_origin(BinaryOrigin {
            image: Some(X86_64_LOAD_FIXTURE_PATH.to_owned()),
            architecture: Some("x86_64".to_owned()),
            function: Some("trust_fixture_x86_load".to_owned()),
            entry: Some(X86_64_LOAD_ENTRY),
        }),
        &input,
        &BinaryReplayConfig::default(),
        &BinaryMachineReplayConfig::default(),
        &backend,
    );
    let machine = &report.machine_replay;

    assert_eq!(machine.status, BinaryMachineReplayStatus::Spurious);
    assert!(!machine.source_backprop_replay_ready());
    assert!(machine.reason.contains("left straight-line trace"), "{}", machine.reason);
    assert!(machine.reason.contains("expected 0x400004"), "{}", machine.reason);
    assert_eq!(machine.observed_instruction_trace.len(), 1);
    assert_eq!(
        machine.observed_instruction_trace[0].origin.instruction_bytes.as_slice(),
        X86_64_LOAD_INSTRUCTION_BYTES
    );
    assert!(machine.replay_transcript_digest.is_some());
}

#[test]
fn bounded_machine_mapped_x86_64_stack_push_pop_trace_replay_reports_replayed() {
    let witness = x86_push_pop_stack_witness(0x1ff8, 0x1122_3344_5566_7788);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_PUSH_RAX_BYTES.to_vec()),
            (0x401001, X86_64_POP_RCX_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x3, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 3);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_PUSH_RAX_BYTES
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, X86_64_POP_RCX_BYTES);
    assert_eq!(report.observed_instruction_trace[2].origin.instruction_address, 0x401002);
}

#[test]
fn bounded_machine_mapped_x86_64_direct_call_ret_trace_replay_reports_replayed() {
    let witness = x86_call_ret_stack_witness(true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_0X401010_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401005, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_capability_evidence);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 3);
    assert_eq!(report.capability_evidence.len(), 2);
    assert_eq!(report.capability_evidence[0].capability, BinaryMachineReplayCapability::DirectCall);
    assert_eq!(report.capability_evidence[0].instruction_address, 0x401000);
    assert_eq!(report.capability_evidence[0].step, Some(0));
    assert!(
        report.capability_evidence[0].validation.contains("direct call target"),
        "{:?}",
        report.capability_evidence[0]
    );
    assert_eq!(report.capability_evidence[1].capability, BinaryMachineReplayCapability::Return);
    assert_eq!(report.capability_evidence[1].instruction_address, 0x401010);
    assert_eq!(report.capability_evidence[1].step, Some(1));
    assert!(
        report.capability_evidence[1].validation.contains("return target"),
        "{:?}",
        report.capability_evidence[1]
    );
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_CALL_0X401010_BYTES
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, X86_64_RET_BYTES);
    assert_eq!(report.observed_instruction_trace[2].origin.instruction_address, 0x401005);
}

#[test]
fn bounded_machine_mapped_x86_64_indirect_call_ret_trace_replay_reports_replayed() {
    let witness = x86_indirect_call_ret_stack_witness(true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_RAX_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 3);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_CALL_RAX_BYTES
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, X86_64_RET_BYTES);
    assert_eq!(report.observed_instruction_trace[2].origin.instruction_address, 0x401002);
}

#[test]
fn bounded_machine_mapped_x86_64_memory_indirect_call_ret_trace_replay_reports_replayed() {
    let witness = x86_memory_indirect_call_ret_stack_witness(true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_PTR_RAX_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    loaded_image.insert_segment(0x3000, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 3);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_CALL_PTR_RAX_BYTES
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, X86_64_RET_BYTES);
    assert_eq!(report.observed_instruction_trace[2].origin.instruction_address, 0x401002);
}

#[test]
fn bounded_machine_mapped_aarch64_direct_call_ret_stack_witness_replay_reports_replayed() {
    let witness = aarch64_call_ret_stack_witness(true);
    let stack_witness = witness.trace[2]
        .assignments
        .iter()
        .find(|record| {
            matches!(
                record.storage,
                BinaryStorageLocation::Stack {
                    base: BinaryStackBase::StackPointer,
                    offset: 8,
                    size_bytes: Some(8),
                }
            )
        })
        .expect("return-address stack witness");
    assert_eq!(stack_witness.raw_name, "stack:sp+8");
    assert_eq!(stack_witness.value.raw, "0x401004");

    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_BL_PLUS_8_BYTES.to_vec()),
            (0x401004, AARCH64_NOP_BYTES.to_vec()),
            (0x401008, AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES.to_vec()),
            (0x40100c, AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES.to_vec()),
            (0x401010, AARCH64_RET_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x14, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff0, 0x10, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_BL_PLUS_8_BYTES
    );
    assert_eq!(
        report.observed_instruction_trace[1].origin.instruction_bytes,
        AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES
    );
    assert_eq!(
        report.observed_instruction_trace[2].origin.instruction_bytes,
        AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES
    );
    assert_eq!(report.observed_instruction_trace[3].origin.instruction_address, 0x401010);
    assert_eq!(report.observed_instruction_trace[3].origin.instruction_bytes, AARCH64_RET_BYTES);
    assert_eq!(report.observed_instruction_trace[4].origin.instruction_address, 0x401004);
    assert_eq!(report.observed_instruction_trace[4].origin.instruction_bytes, AARCH64_NOP_BYTES);
}

#[test]
fn bounded_machine_mapped_aarch64_indirect_call_ret_stack_witness_replay_reports_replayed() {
    let witness = aarch64_indirect_call_ret_stack_witness(true, true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_BLR_X8_BYTES.to_vec()),
            (0x401004, AARCH64_NOP_BYTES.to_vec()),
            (0x401008, AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES.to_vec()),
            (0x40100c, AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES.to_vec()),
            (0x401010, AARCH64_RET_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x14, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff0, 0x10, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_bytes, AARCH64_BLR_X8_BYTES);
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401008);
    assert_eq!(
        report.observed_instruction_trace[1].origin.instruction_bytes,
        AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES
    );
    assert_eq!(report.observed_instruction_trace[3].origin.instruction_bytes, AARCH64_RET_BYTES);
    assert_eq!(report.observed_instruction_trace[4].origin.instruction_address, 0x401004);
    assert_eq!(report.observed_instruction_trace[4].origin.instruction_bytes, AARCH64_NOP_BYTES);
}

#[test]
fn bounded_machine_aarch64_direct_call_ret_requires_return_address_stack_witness() {
    let witness = aarch64_call_ret_stack_witness(false);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_BL_PLUS_8_BYTES.to_vec()),
            (0x401004, AARCH64_NOP_BYTES.to_vec()),
            (0x401008, AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES.to_vec()),
            (0x40100c, AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES.to_vec()),
            (0x401010, AARCH64_RET_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x14, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff0, 0x10, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace.len(), 4);
    assert_eq!(report.observed_instruction_trace[3].origin.instruction_address, 0x401010);
    assert_eq!(report.observed_instruction_trace[3].origin.instruction_bytes, AARCH64_RET_BYTES);
    assert!(report.reason.contains("AArch64 return replay"), "{}", report.reason);
    assert!(report.reason.contains("saved return-address stack witness"), "{}", report.reason);
    assert!(report.reason.contains("0x401010"), "{}", report.reason);
    assert!(report.reason.contains("expected trace length 5"), "{}", report.reason);
}

#[test]
fn bounded_machine_aarch64_indirect_call_requires_target_register_witness() {
    let witness = aarch64_indirect_call_ret_stack_witness(false, true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [
            (0x401000, AARCH64_BLR_X8_BYTES.to_vec()),
            (0x401004, AARCH64_NOP_BYTES.to_vec()),
            (0x401008, AARCH64_STP_X29_X30_SP_PRE_DEC16_BYTES.to_vec()),
            (0x40100c, AARCH64_LDP_X29_X30_SP_POST_INC16_BYTES.to_vec()),
            (0x401010, AARCH64_RET_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x14, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff0, 0x10, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 5);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_bytes, AARCH64_BLR_X8_BYTES);
    assert!(report.reason.contains("unsupported control flow: indirect call"), "{}", report.reason);
    assert!(report.reason.contains("AArch64 register-indirect call replay"), "{}", report.reason);
    assert!(report.reason.contains("exact 64-bit X8 witness"), "{}", report.reason);
    assert!(report.reason.contains("trace step 0"), "{}", report.reason);
}

#[test]
fn bounded_machine_x86_64_direct_call_ret_requires_return_address_stack_witness() {
    let witness = x86_call_ret_stack_witness(false);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_0X401010_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401005, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert!(report.reason.contains("unsupported control flow: direct call"), "{}", report.reason);
    assert!(report.reason.contains("return-address stack witness"), "{}", report.reason);
    assert!(report.reason.contains("trace step 1"), "{}", report.reason);
}

#[test]
fn bounded_machine_x86_64_indirect_call_requires_target_register_witness() {
    let witness = x86_indirect_call_ret_stack_witness(false);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_RAX_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert!(report.reason.contains("unsupported control flow: indirect call"), "{}", report.reason);
    assert!(report.reason.contains("exact 64-bit RAX witness"), "{}", report.reason);
    assert!(report.reason.contains("trace step 0"), "{}", report.reason);
}

#[test]
fn bounded_machine_x86_64_memory_indirect_call_requires_target_memory_load_witness() {
    let witness = x86_memory_indirect_call_ret_stack_witness(false);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_CALL_PTR_RAX_BYTES.to_vec()),
            (0x401010, X86_64_RET_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x11, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    loaded_image.insert_segment(0x3000, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 3);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        X86_64_CALL_PTR_RAX_BYTES
    );
    assert!(report.reason.contains("unsupported control flow: indirect call"), "{}", report.reason);
    assert!(report.reason.contains("memory-indirect call replay"), "{}", report.reason);
    assert!(report.reason.contains("target-memory operand [RAX]"), "{}", report.reason);
    assert!(report.reason.contains("0x3000"), "{}", report.reason);
    assert!(report.reason.contains("8-byte target-memory load witness"), "{}", report.reason);
    assert!(report.reason.contains("trace step 0"), "{}", report.reason);
}

#[test]
fn bounded_machine_stack_trace_sp_mismatch_fails_closed_with_diagnostic() {
    let witness = x86_push_pop_stack_witness(0x2000, 0x1122_3344_5566_7788);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_PUSH_RAX_BYTES.to_vec()),
            (0x401001, X86_64_POP_RCX_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x3, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert!(report.reason.contains("register RSP mismatch"), "{}", report.reason);
    assert!(report.reason.contains("trace step 1"), "{}", report.reason);
    assert!(report.reason.contains("expected 0x2000"), "{}", report.reason);
    assert!(report.reason.contains("observed 0x1ff8"), "{}", report.reason);
}

#[test]
fn bounded_machine_stack_trace_memory_mismatch_fails_closed_with_diagnostic() {
    let witness = x86_push_pop_stack_witness(0x1ff8, 0x1122_3344_5566_7789);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::X86_64,
        [
            (0x401000, X86_64_PUSH_RAX_BYTES.to_vec()),
            (0x401001, X86_64_POP_RCX_BYTES.to_vec()),
            (0x401002, X86_64_NOP_BYTES.to_vec()),
        ],
    );
    loaded_image.insert_segment(0x401000, 0x3, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x1ff8, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert!(report.reason.contains("memory witness mismatch"), "{}", report.reason);
    assert!(report.reason.contains("trace step 1"), "{}", report.reason);
    assert!(report.reason.contains("address 0x1ff8"), "{}", report.reason);
    assert!(report.reason.contains("expected 0x1122334455667789"), "{}", report.reason);
    assert!(report.reason.contains("observed 0x1122334455667788"), "{}", report.reason);
}

#[test]
fn bounded_machine_trace_length_limit_fails_closed_with_diagnostic() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000), aarch64_nop(0x401004)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec()), (0x401004, AARCH64_NOP_BYTES.to_vec())],
    ))
    .with_max_instructions(1);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("trace length 2 exceeds configured limit 1"));
}

#[test]
fn bounded_machine_unmapped_instruction_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(BoundedMachineCodeImage::new(
        BoundedMachineCodeArchitecture::Aarch64,
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("no original instruction bytes mapped"));
}

#[test]
fn bounded_machine_instruction_byte_mismatch_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_YIELD_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("instruction bytes"));
}

#[test]
fn bounded_machine_non_executable_segment_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let mut loaded_image =
        image(BoundedMachineCodeArchitecture::Aarch64, [(0x401000, AARCH64_NOP_BYTES.to_vec())]);
    loaded_image.insert_segment(0x401000, 0x1000, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("non-executable"));
    assert!(report.reason.contains("0x401000"));
}

#[test]
fn bounded_machine_memory_access_without_loaded_segment_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_str_x0_x1(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_STR_X0_X1_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 1);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("loaded memory segment"));
    assert!(report.reason.contains("write"));
    assert!(report.reason.contains("0x0"));
}

#[test]
fn bounded_machine_memory_trace_evidence_without_loaded_segment_fails_closed() {
    let mut witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let program_point = witness.trace[0].program_point.clone();
    witness.trace[0].assignments.push(BinaryWitnessRecord {
        source: BinaryWitnessRecordSource::TraceAssignment,
        raw_name: "memory:0x2000".to_owned(),
        value: BinaryWitnessValue {
            typed: Some(CounterexampleValue::Int(42)),
            raw: "0x2a".to_owned(),
        },
        subject: BinaryFactSubject::Memory { name: None, address: Some(0x2000) },
        storage: BinaryStorageLocation::Memory {
            address: Formula::UInt(0x2000),
            size_bytes: Some(8),
        },
        function: None,
        local_index: None,
        program_point,
    });
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 1);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("memory witness"), "{}", report.reason);
    assert!(report.reason.contains("loaded memory segment"), "{}", report.reason);
}

#[test]
fn bounded_machine_mapped_aarch64_direct_branch_replay_reports_replayed() {
    let witness = straight_line_witness(vec![aarch64_b_plus_8(0x401000), aarch64_nop(0x401008)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_B_PLUS_8_BYTES.to_vec()), (0x401008, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_capability_evidence);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(report.capability_evidence.len(), 1);
    assert_eq!(
        report.capability_evidence[0].capability,
        BinaryMachineReplayCapability::DirectBranch
    );
    assert_eq!(report.capability_evidence[0].architecture, "AArch64");
    assert_eq!(report.capability_evidence[0].instruction_address, 0x401000);
    assert_eq!(report.capability_evidence[0].step, Some(0));
    assert_eq!(report.capability_evidence[0].instruction_bytes, AARCH64_B_PLUS_8_BYTES);
    assert!(
        report.capability_evidence[0].validation.contains("direct branch target"),
        "{:?}",
        report.capability_evidence[0]
    );
    assert_eq!(
        report.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_B_PLUS_8_BYTES.to_vec()
    );
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401008);
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, AARCH64_NOP_BYTES);
}

#[test]
fn machine_replay_requires_explicit_capability_evidence_for_validated_call_flow() {
    let origin = x86_64_call_0x401010(0x401000);
    let witness = straight_line_witness(vec![origin.clone()]);
    let backend = AddressOnlyReplayBackend { origin };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(report.matched_instruction_trace);
    assert!(!report.matched_capability_evidence);
    assert!(report.capability_evidence.is_empty());
    assert!(report.reason.contains("capability evidence"), "{}", report.reason);
    assert!(report.reason.contains("direct_call"), "{}", report.reason);
    assert!(report.reason.contains("branch/call/return"), "{}", report.reason);
}

#[test]
fn machine_replay_requires_explicit_capability_evidence_for_validated_direct_branch() {
    let origin = aarch64_b_plus_8(0x401000);
    let witness = straight_line_witness(vec![origin.clone()]);
    let backend = AddressOnlyReplayBackend { origin };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(report.matched_instruction_trace);
    assert!(!report.matched_capability_evidence);
    assert!(report.capability_evidence.is_empty());
    assert!(report.reason.contains("capability evidence"), "{}", report.reason);
    assert!(report.reason.contains("direct_branch"), "{}", report.reason);
    assert!(report.reason.contains("branch/call/return"), "{}", report.reason);
}

#[test]
fn machine_replay_rejects_mismatched_direct_branch_capability_evidence() {
    let origin = aarch64_b_plus_8(0x401000);
    let witness = straight_line_witness(vec![origin.clone()]);
    let capability_evidence = BinaryMachineReplayCapabilityEvidence::new(
        BinaryMachineReplayCapability::DirectBranch,
        "AArch64",
        0x401000,
        "decoded direct branch target validated against following trace step",
    )
    .with_step(Some(1))
    .with_instruction_bytes(AARCH64_B_PLUS_8_BYTES);
    let backend = CapabilityReplayBackend { origin, capability_evidence };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(report.matched_instruction_trace);
    assert!(!report.matched_capability_evidence);
    assert_eq!(report.capability_evidence.len(), 1);
    assert_eq!(
        report.capability_evidence[0].capability,
        BinaryMachineReplayCapability::DirectBranch
    );
    assert_eq!(report.capability_evidence[0].step, Some(1));
    assert!(report.reason.contains("capability evidence"), "{}", report.reason);
    assert!(report.reason.contains("direct_branch"), "{}", report.reason);
}

#[test]
fn source_backprop_replay_ready_requires_consumed_machine_effect_witnesses() {
    let origin = aarch64_nop(0x401000);
    let mut proof_witness = straight_line_witness(vec![origin.clone()]);
    proof_witness.provenance.requires_selected_image_identity = true;
    bind_dummy_model_assignment(&mut proof_witness);
    let backend = EffectlessReplayBackend { origin: origin.clone() };

    let report =
        replay_machine_witness(&proof_witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_artifact_digest);
    assert!(report.matched_selected_image);
    assert!(!report.matched_effect_evidence);
    assert_eq!(report.effect_diagnostics.len(), 1);
    assert_eq!(
        report.effect_diagnostics[0].kind,
        BinaryMachineReplayEffectDiagnosticKind::MissingMachineEffectWitness
    );
    assert_eq!(
        report.effect_diagnostics[0].effect_kind,
        Some(BinaryMachineReplayEffectKind::NoStateChange)
    );
    assert!(report.reason.contains("effect witness"), "{}", report.reason);
    assert!(!report.source_backprop_replay_ready());

    let exploratory_witness = straight_line_witness(vec![origin.clone()]);
    let exploratory = replay_machine_witness(
        &exploratory_witness,
        &BinaryMachineReplayConfig::default(),
        &backend,
    );

    assert_eq!(exploratory.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(exploratory.trust_types_status, ReplayStatus::Replayed);
    assert!(!exploratory.matched_effect_evidence);
    assert!(exploratory.effect_diagnostics.is_empty());
    assert!(!exploratory.source_backprop_replay_ready());
    let blocker = exploratory
        .source_backprop_replay_blocker_reason()
        .expect("effectless exploratory replay must not be source-backprop ready");
    assert!(blocker.contains("machine-effect witnesses"), "{blocker}");
}

#[test]
fn source_backprop_replay_ready_requires_concrete_scalar_memory_effect_witness() {
    let origin = aarch64_str_x0_x1(0x401000);
    let mut proof_witness = straight_line_witness(vec![origin.clone()]);
    proof_witness.provenance.requires_selected_image_identity = true;
    bind_dummy_model_assignment(&mut proof_witness);
    let backend = GenericMemoryEffectReplayBackend {
        origin: origin.clone(),
        kind: BinaryMachineReplayEffectKind::MemoryWrite,
    };

    let report =
        replay_machine_witness(&proof_witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert_eq!(report.trust_types_status, ReplayStatus::NotAttempted);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_artifact_digest);
    assert!(report.matched_selected_image);
    assert!(!report.matched_effect_evidence);
    assert_eq!(report.effect_evidence.len(), 1);
    assert_eq!(report.effect_evidence[0].kind, BinaryMachineReplayEffectKind::MemoryWrite);
    assert_eq!(report.effect_evidence[0].subject.as_deref(), Some("memory_access#0:8B"));
    assert_eq!(report.effect_evidence[0].memory_access, None);
    assert_eq!(report.effect_diagnostics.len(), 1);
    assert_eq!(
        report.effect_diagnostics[0].kind,
        BinaryMachineReplayEffectDiagnosticKind::MissingMachineEffectWitness
    );
    assert_eq!(
        report.effect_diagnostics[0].effect_kind,
        Some(BinaryMachineReplayEffectKind::MemoryWrite)
    );
    assert!(report.reason.contains("concrete scalar memory address"), "{}", report.reason);
    assert!(!report.source_backprop_replay_ready());

    let exploratory_witness = straight_line_witness(vec![origin]);
    let exploratory = replay_machine_witness(
        &exploratory_witness,
        &BinaryMachineReplayConfig::default(),
        &backend,
    );
    let blocker = exploratory
        .source_backprop_replay_blocker_reason()
        .expect("generic memory effect replay must not be source-backprop ready");

    assert_eq!(exploratory.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(exploratory.trust_types_status, ReplayStatus::Replayed);
    assert!(!exploratory.matched_effect_evidence);
    assert!(exploratory.effect_diagnostics.is_empty());
    assert!(blocker.contains("concrete scalar memory address"), "{blocker}");
    assert!(!exploratory.source_backprop_replay_ready());
}

#[test]
fn source_backprop_attestation_slice_accepts_scalar_store_effect() {
    let witness = straight_line_witness(vec![aarch64_str_x0_x1(0x401000)]);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_STR_X0_X1_BYTES.to_vec())],
    );
    loaded_image.insert_segment(0x401000, 0x4, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x0, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert!(report.source_backprop_replay_ready(), "{report:?}");
    assert_eq!(report.attestation_slices.len(), 1);
    let slice = &report.attestation_slices[0];
    assert_eq!(slice.status, BinaryMachineReplayAttestationStatus::Accepted);
    assert_eq!(slice.instruction_address, 0x401000);
    assert_eq!(slice.step, Some(0));
    assert_eq!(slice.selected_image, Some(test_selected_image()));
    assert_eq!(slice.instruction_bytes, AARCH64_STR_X0_X1_BYTES.to_vec());
    let range = slice.byte_range.as_ref().expect("accepted slice carries byte range");
    assert_eq!(range.file_offset, 0);
    assert_eq!(range.size, AARCH64_STR_X0_X1_BYTES.len() as u64);

    let memory_write = slice
        .effect_identities
        .iter()
        .find(|identity| identity.kind == BinaryMachineReplayEffectKind::MemoryWrite)
        .expect("accepted scalar slice carries consumed memory-write identity");
    assert_eq!(memory_write.subject.as_deref(), Some("memory_access#0:8B"));
    let memory_access = memory_write.memory_access.expect("memory write carries concrete access");
    assert_eq!(memory_access.address, 0);
    assert_eq!(memory_access.width_bytes, 8);
}

#[test]
fn source_backprop_readiness_rejects_minimized_attestation_without_range_or_memory_binding() {
    let witness = straight_line_witness(vec![aarch64_str_x0_x1(0x401000)]);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_STR_X0_X1_BYTES.to_vec())],
    );
    loaded_image.insert_segment(0x401000, 0x4, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x0, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
    assert!(report.source_backprop_replay_ready(), "{report:?}");
    assert_eq!(report.attestation_slices.len(), 1);
    assert_eq!(report.attestation_slices[0].status, BinaryMachineReplayAttestationStatus::Accepted);

    let mut missing_range = report.clone();
    missing_range.attestation_slices[0].byte_range = None;
    let range_blocker = missing_range
        .source_backprop_replay_blocker_reason()
        .expect("minimized attestation without byte range must block source backprop");

    assert!(!missing_range.source_backprop_replay_ready());
    assert!(range_blocker.contains("byte/range binding"), "{range_blocker}");
    assert!(range_blocker.contains("minimized replay witnesses"), "{range_blocker}");

    let mut missing_memory_binding = report.clone();
    let memory_write = missing_memory_binding.attestation_slices[0]
        .effect_identities
        .iter_mut()
        .find(|identity| identity.kind == BinaryMachineReplayEffectKind::MemoryWrite)
        .expect("accepted scalar store slice carries memory-write identity");
    memory_write.memory_access = None;
    let effect_blocker = missing_memory_binding
        .source_backprop_replay_blocker_reason()
        .expect("minimized attestation without memory-effect range must block source backprop");

    assert!(!missing_memory_binding.source_backprop_replay_ready());
    assert!(effect_blocker.contains("memory_write effect identity"), "{effect_blocker}");
    assert!(effect_blocker.contains("concrete scalar memory address"), "{effect_blocker}");
    assert!(effect_blocker.contains("minimized replay witnesses"), "{effect_blocker}");
}

#[test]
fn source_backprop_attestation_slice_rejects_instruction_byte_mismatch() {
    let expected = aarch64_str_x0_x1(0x401000);
    let observed = aarch64_ldr_x2_x1(0x401000);
    let witness = straight_line_witness(vec![expected]);
    let backend = GenericMemoryEffectReplayBackend {
        origin: observed,
        kind: BinaryMachineReplayEffectKind::MemoryRead,
    };

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert!(!report.source_backprop_replay_ready());
    assert_eq!(report.attestation_slices.len(), 1);
    let slice = &report.attestation_slices[0];
    assert_eq!(slice.status, BinaryMachineReplayAttestationStatus::Rejected);
    let diagnostic = slice.diagnostic.as_deref().expect("rejected slice diagnostic");
    assert!(diagnostic.contains("instruction bytes"), "{diagnostic}");
}

#[test]
fn source_backprop_attestation_slice_rejects_selected_image_range_mismatch() {
    let witness = straight_line_witness(vec![aarch64_str_x0_x1(0x401000)]);
    let mut loaded_image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
        .with_artifact_digest(test_artifact_digest())
        .with_selected_image(test_selected_image());
    loaded_image.insert_instruction_at_file_offset(
        0x401000,
        test_selected_image().file_size + 4,
        AARCH64_STR_X0_X1_BYTES,
    );
    loaded_image.insert_segment(0x401000, 0x4, BoundedMachineCodeSegmentPermissions::rx());
    loaded_image.insert_segment(0x0, 0x8, BoundedMachineCodeSegmentPermissions::rw());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(
        report.byte_range_diagnostics[0].kind,
        BinaryMachineReplayByteRangeDiagnosticKind::OriginalByteRangeOutsideSelectedImage
    );
    assert!(!report.source_backprop_replay_ready());
    assert_eq!(report.attestation_slices.len(), 1);
    let slice = &report.attestation_slices[0];
    assert_eq!(slice.status, BinaryMachineReplayAttestationStatus::Rejected);
    let diagnostic = slice.diagnostic.as_deref().expect("rejected slice diagnostic");
    assert!(diagnostic.contains("outside selected-image byte range"), "{diagnostic}");
}

#[test]
fn source_backprop_attestation_slice_rejects_missing_machine_effect_identity() {
    let origin = aarch64_str_x0_x1(0x401000);
    let mut proof_witness = straight_line_witness(vec![origin.clone()]);
    proof_witness.provenance.requires_selected_image_identity = true;
    bind_dummy_model_assignment(&mut proof_witness);
    let backend = EffectlessReplayBackend { origin };

    let report =
        replay_machine_witness(&proof_witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert!(!report.source_backprop_replay_ready());
    assert_eq!(report.attestation_slices.len(), 1);
    let slice = &report.attestation_slices[0];
    assert_eq!(slice.status, BinaryMachineReplayAttestationStatus::Rejected);
    let diagnostic = slice.diagnostic.as_deref().expect("rejected slice diagnostic");
    assert!(diagnostic.contains("effect witness"), "{diagnostic}");
    assert!(diagnostic.contains("memory_write"), "{diagnostic}");
}

#[test]
fn source_backprop_attestation_slice_rejects_unsupported_boundary() {
    let witness = straight_line_witness(vec![aarch64_svc0(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_SVC0_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert!(!report.source_backprop_replay_ready());
    assert_eq!(report.boundary_evidence.len(), 1);
    assert_eq!(report.attestation_slices.len(), 1);
    let slice = &report.attestation_slices[0];
    assert_eq!(slice.status, BinaryMachineReplayAttestationStatus::Rejected);
    let diagnostic = slice.diagnostic.as_deref().expect("rejected slice diagnostic");
    assert!(diagnostic.contains("unchecked AArch64 syscall boundary"), "{diagnostic}");
    assert!(
        diagnostic.contains("exact boundary witness semantics are not represented"),
        "{diagnostic}"
    );
}

#[test]
fn bounded_machine_replay_reports_typed_unsupported_effect_witness_class() {
    let origin = aarch64_dmb_ish(0x401000);
    let mut proof_witness = straight_line_witness(vec![origin.clone()]);
    proof_witness.provenance.requires_selected_image_identity = true;
    bind_dummy_model_assignment(&mut proof_witness);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_DMB_ISH_BYTES.to_vec())],
    ));

    let report =
        replay_machine_witness(&proof_witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert!(report.matched_instruction_trace);
    assert!(!report.matched_effect_evidence);
    assert_eq!(report.effect_diagnostics.len(), 1);
    assert_eq!(
        report.effect_diagnostics[0].kind,
        BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass
    );
    assert_eq!(
        report.effect_diagnostics[0].effect_kind,
        Some(BinaryMachineReplayEffectKind::Aarch64SyncBoundary)
    );
    assert!(report.reason.contains("unsupported machine-effect witness class"));
    assert!(report.reason.contains("aarch64_sync_boundary"));
    assert!(!report.source_backprop_replay_ready());

    let exploratory_witness = straight_line_witness(vec![origin]);
    let exploratory = replay_machine_witness(
        &exploratory_witness,
        &BinaryMachineReplayConfig::default(),
        &backend,
    );

    assert_eq!(exploratory.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(exploratory.trust_types_status, ReplayStatus::Replayed);
    assert!(!exploratory.matched_effect_evidence);
    assert_eq!(exploratory.effect_diagnostics.len(), 1);
    assert_eq!(
        exploratory.effect_diagnostics[0].kind,
        BinaryMachineReplayEffectDiagnosticKind::UnsupportedMachineEffectWitnessClass
    );
    assert!(!exploratory.source_backprop_replay_ready());
}

#[test]
fn bounded_machine_direct_call_control_flow_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_bl_plus_8(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_BL_PLUS_8_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_unsupported_control_flow_report(
        &report,
        0x401000,
        &AARCH64_BL_PLUS_8_BYTES,
        "Call",
        "unsupported control flow: direct call",
    );
}

#[test]
fn bounded_machine_indirect_call_control_flow_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_blr_x8(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_BLR_X8_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_unsupported_control_flow_report(
        &report,
        0x401000,
        &AARCH64_BLR_X8_BYTES,
        "Call",
        "unsupported control flow: indirect call",
    );
}

#[test]
fn bounded_machine_return_control_flow_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_ret(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_RET_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_unsupported_control_flow_report(
        &report,
        0x401000,
        &AARCH64_RET_BYTES,
        "Return",
        "unsupported control flow: return",
    );
}

#[test]
fn bounded_machine_indirect_branch_control_flow_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_br_x16(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_BR_X16_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_unsupported_control_flow_report(
        &report,
        0x401000,
        &AARCH64_BR_X16_BYTES,
        "Branch",
        "unsupported control flow: indirect branch",
    );
}

#[test]
fn bounded_machine_mapped_aarch64_indirect_branch_register_witness_replay_reports_replayed() {
    let witness = aarch64_indirect_branch_witness(true);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_BR_X16_BYTES.to_vec()), (0x401020, AARCH64_NOP_BYTES.to_vec())],
    );
    loaded_image.insert_segment(0x401000, 0x24, BoundedMachineCodeSegmentPermissions::rx());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert_eq!(report.trust_types_status, ReplayStatus::Replayed);
    assert!(report.matched_instruction_trace);
    assert!(report.matched_capability_evidence);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 2);
    assert_eq!(report.capability_evidence.len(), 1);
    assert_eq!(
        report.capability_evidence[0].capability,
        BinaryMachineReplayCapability::IndirectBranch
    );
    assert_eq!(report.capability_evidence[0].instruction_address, 0x401000);
    assert_eq!(report.capability_evidence[0].step, Some(0));
    assert!(
        report.capability_evidence[0].validation.contains("register-indirect branch"),
        "{:?}",
        report.capability_evidence[0]
    );
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_bytes, AARCH64_BR_X16_BYTES);
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_address, 0x401020);
    assert_eq!(report.observed_instruction_trace[1].origin.instruction_bytes, AARCH64_NOP_BYTES);
}

#[test]
fn bounded_machine_aarch64_indirect_branch_requires_target_register_witness() {
    let witness = aarch64_indirect_branch_witness(false);
    let mut loaded_image = image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_BR_X16_BYTES.to_vec()), (0x401020, AARCH64_NOP_BYTES.to_vec())],
    );
    loaded_image.insert_segment(0x401000, 0x24, BoundedMachineCodeSegmentPermissions::rx());
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert_ne!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(!report.matched_instruction_trace);
    assert_eq!(report.expected_instruction_trace.len(), 2);
    assert_eq!(report.observed_instruction_trace.len(), 1);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_address, 0x401000);
    assert_eq!(report.observed_instruction_trace[0].origin.instruction_bytes, AARCH64_BR_X16_BYTES);
    assert!(
        report.reason.contains("unsupported control flow: indirect branch"),
        "{}",
        report.reason
    );
    assert!(report.reason.contains("AArch64 register-indirect branch replay"), "{}", report.reason);
    assert!(report.reason.contains("exact 64-bit X16 witness"), "{}", report.reason);
    assert!(report.reason.contains("trace step 0"), "{}", report.reason);
}

#[test]
fn bounded_machine_x86_64_instruction_byte_mismatch_fails_closed() {
    let witness = straight_line_witness(vec![x86_64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::X86_64,
        [(0x401000, X86_64_INT3_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("instruction bytes"));
    assert!(report.reason.contains("normalized witness provenance"));
}

#[test]
fn bounded_machine_instruction_size_mismatch_fails_closed() {
    let mut origin = aarch64_nop(0x401000);
    origin.instruction_bytes.clear();
    let witness = straight_line_witness(vec![origin]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, vec![0x1f, 0x20, 0x03, 0xd5, 0x00])],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("instruction size"));
}

#[test]
fn bounded_machine_unsupported_architecture_fails_closed() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Unsupported,
        [(0x401000, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert!(!report.matched_instruction_trace);
    assert!(report.observed_instruction_trace.is_empty());
    assert!(report.reason.contains("selected architecture"));
}

#[test]
fn source_backprop_replay_ready_blocks_unchecked_boundary_evidence() {
    let cases = [
        (
            "syscall",
            aarch64_svc0(0x401000),
            AARCH64_SVC0_BYTES.to_vec(),
            BinaryMachineReplayBoundaryKind::Syscall,
            "SVC",
            "unchecked AArch64 syscall boundary",
        ),
        (
            "exception",
            aarch64_hvc0(0x401000),
            AARCH64_HVC0_BYTES.to_vec(),
            BinaryMachineReplayBoundaryKind::Exception,
            "HVC",
            "unchecked AArch64 exception boundary",
        ),
        (
            "trap",
            aarch64_brk1(0x401000),
            AARCH64_BRK1_BYTES.to_vec(),
            BinaryMachineReplayBoundaryKind::Trap,
            "BRK",
            "unchecked AArch64 trap boundary",
        ),
    ];

    for (name, origin, bytes, expected_kind, opcode, needle) in cases {
        let witness = straight_line_witness(vec![origin.clone()]);
        let backend = BoundedMachineCodeReplayBackend::new(image(
            BoundedMachineCodeArchitecture::Aarch64,
            [(origin.instruction_address, bytes.clone())],
        ));

        let report =
            replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
        let blocker = report
            .source_backprop_replay_blocker_reason()
            .unwrap_or_else(|| panic!("{name} boundary unexpectedly source-backprop ready"));

        assert_eq!(report.status, BinaryMachineReplayStatus::Unsupported, "{name}");
        assert_eq!(report.trust_types_status, ReplayStatus::Failed, "{name}");
        assert!(!report.source_backprop_replay_ready(), "{name}: {report:?}");
        assert_eq!(report.expected_artifact_digest, Some(test_artifact_digest()), "{name}");
        assert_eq!(report.observed_artifact_digest, Some(test_artifact_digest()), "{name}");
        assert_eq!(report.expected_selected_image, Some(test_selected_image()), "{name}");
        assert_eq!(report.observed_selected_image, Some(test_selected_image()), "{name}");
        assert_eq!(report.boundary_evidence.len(), 1, "{name}: {report:?}");

        let boundary = &report.boundary_evidence[0];
        assert_eq!(boundary.kind, expected_kind, "{name}");
        assert_eq!(boundary.architecture, "AArch64", "{name}");
        assert_eq!(boundary.instruction_address, origin.instruction_address, "{name}");
        assert_eq!(boundary.step, Some(0), "{name}");
        assert_eq!(boundary.instruction_bytes, bytes, "{name}");
        assert_eq!(boundary.opcode.to_ascii_uppercase(), opcode, "{name}");
        assert_eq!(
            boundary.semantics,
            BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness,
            "{name}"
        );
        assert!(boundary.diagnostic.contains(needle), "{name}: {}", boundary.diagnostic);
        assert!(blocker.contains(needle), "{name}: {blocker}");
        assert!(
            blocker.contains("exact boundary witness semantics are not represented"),
            "{name}: {blocker}"
        );
    }
}

#[test]
fn sat_dispatch_exception_boundary_cannot_satisfy_exact_replay_requirement() {
    let mut dispatch = sat_dispatch_with_witness();
    dispatch.origin = Some(aarch64_hvc0(0x401000));
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_HVC0_BYTES.to_vec())],
    ));

    let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
        &dispatch,
        None,
        &BinaryReplayConfig::default(),
        &BinaryMachineReplayConfig::default(),
        &backend,
    );

    assert!(evidence.produced_witness());
    assert_eq!(evidence.replay_requirement, BinaryReplayRequirement::ExactMachineWitnessReplay);
    assert!(!evidence.requirement_satisfied);
    assert!(evidence.needs_machine_witness_replay());
    assert_ne!(evidence.replay, ReplayStatus::Replayed);

    let report = evidence.replay_report.as_ref().expect("SAT dispatch should produce a report");
    assert_eq!(report.trust_types_status, ReplayStatus::Failed);
    assert!(!report.needs_machine_replay);

    let machine = &report.machine_replay;
    let blocker = machine
        .source_backprop_replay_blocker_reason()
        .expect("unchecked exception boundary must remain an explicit replay blocker");

    assert_eq!(machine.status, BinaryMachineReplayStatus::Unsupported);
    assert_eq!(machine.trust_types_status, ReplayStatus::Failed);
    assert!(!machine.source_backprop_replay_ready());
    assert_eq!(machine.boundary_evidence.len(), 1);
    assert_eq!(machine.boundary_evidence[0].kind, BinaryMachineReplayBoundaryKind::Exception);
    assert_eq!(
        machine.boundary_evidence[0].semantics,
        BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness
    );
    assert!(blocker.contains("unchecked AArch64 exception boundary"), "{blocker}");
    assert!(blocker.contains("exact boundary witness semantics are not represented"), "{blocker}");
    assert!(evidence.reason.contains("unchecked AArch64 exception boundary"));
}

#[test]
fn source_backprop_blocker_prioritizes_typed_boundary_evidence() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec())],
    ));

    let mut report =
        replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);
    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed, "{}", report.reason);
    assert!(report.source_backprop_replay_ready(), "{report:?}");

    report.status = BinaryMachineReplayStatus::Unsupported;
    report.trust_types_status = ReplayStatus::Failed;
    report.reason = "backend stopped before producing source-backprop evidence".to_owned();
    report.boundary_evidence.push(BinaryMachineReplayBoundaryEvidence {
        kind: BinaryMachineReplayBoundaryKind::Exception,
        architecture: "AArch64".to_owned(),
        instruction_address: 0x401004,
        step: Some(1),
        instruction_bytes: AARCH64_HVC0_BYTES.to_vec(),
        opcode: "HVC".to_owned(),
        encoding: AARCH64_HVC0_ENCODING,
        immediate: Some(0),
        semantics: BinaryMachineReplayBoundarySemantics::UnsupportedNoExactWitness,
        diagnostic: "unchecked AArch64 exception boundary".to_owned(),
    });

    let blocker = report
        .source_backprop_replay_blocker_reason()
        .expect("unchecked boundary evidence should block source backprop");

    assert!(!report.source_backprop_replay_ready());
    assert!(blocker.contains("unchecked AArch64 exception boundary"), "{blocker}");
    assert!(!blocker.contains("backend stopped"), "{blocker}");
}

#[test]
fn bounded_machine_replay_producer_file_offsets_gate_source_backprop_readiness() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401004)]);
    let mut missing_offset_image =
        BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
            .with_artifact_digest(test_artifact_digest())
            .with_selected_image(test_selected_image());
    missing_offset_image.insert_instruction(0x401004, AARCH64_NOP_BYTES);

    let missing_offset_report = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(missing_offset_image),
    );

    assert_eq!(missing_offset_report.status, BinaryMachineReplayStatus::Replayed);
    assert!(missing_offset_report.matched_instruction_trace);
    assert!(missing_offset_report.matched_artifact_digest);
    assert!(missing_offset_report.matched_selected_image);
    assert!(missing_offset_report.byte_range_evidence.is_empty());
    assert!(!missing_offset_report.source_backprop_replay_ready());
    let blocker = missing_offset_report
        .source_backprop_replay_blocker_reason()
        .expect("missing producer file offsets must block source backprop");
    assert!(blocker.contains("original byte/range attestation"), "{blocker}");

    let explicit_file_offset = 0x128;
    let mut offset_image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
        .with_artifact_digest(test_artifact_digest())
        .with_selected_image(test_selected_image());
    offset_image.insert_instruction_at_file_offset(
        0x401004,
        explicit_file_offset,
        AARCH64_NOP_BYTES,
    );

    let offset_report = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(offset_image),
    );

    assert_eq!(offset_report.status, BinaryMachineReplayStatus::Replayed);
    assert!(offset_report.source_backprop_replay_ready(), "{offset_report:?}");
    assert_eq!(offset_report.byte_range_evidence.len(), 1);
    let range = &offset_report.byte_range_evidence[0];
    assert_eq!(range.instruction_address, 0x401004);
    assert_eq!(range.step, Some(0));
    assert_eq!(range.file_offset, explicit_file_offset);
    assert_eq!(range.size, AARCH64_NOP_BYTES.len() as u64);
    assert_eq!(range.instruction_bytes, AARCH64_NOP_BYTES.to_vec());
    assert!(offset_report.byte_range_diagnostics.is_empty());
}

#[test]
fn source_backprop_replay_ready_requires_selected_image_original_byte_ranges() {
    let witness = straight_line_witness(vec![aarch64_nop(0x401000)]);
    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec())],
    ));

    let report = replay_machine_witness(&witness, &BinaryMachineReplayConfig::default(), &backend);

    assert_eq!(report.status, BinaryMachineReplayStatus::Replayed);
    assert!(report.source_backprop_replay_ready(), "{report:?}");
    assert_eq!(report.byte_range_evidence.len(), 1);
    assert!(report.byte_range_diagnostics.is_empty());

    let mut missing_attestation = report.clone();
    missing_attestation.byte_range_evidence.clear();
    let blocker = missing_attestation
        .source_backprop_replay_blocker_reason()
        .expect("missing byte/range attestation should block source backprop");
    assert!(!missing_attestation.source_backprop_replay_ready());
    assert!(blocker.contains("original byte/range attestation"), "{blocker}");

    let mut stale_image = BoundedMachineCodeImage::new(BoundedMachineCodeArchitecture::Aarch64)
        .with_artifact_digest(test_artifact_digest())
        .with_selected_image(test_selected_image());
    stale_image.insert_instruction_at_file_offset(
        0x401000,
        test_selected_image().file_size + 4,
        AARCH64_NOP_BYTES,
    );
    let stale_report = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(stale_image),
    );
    let stale_blocker = stale_report
        .source_backprop_replay_blocker_reason()
        .expect("stale byte range should block source backprop");
    assert_eq!(stale_report.status, BinaryMachineReplayStatus::Spurious);
    assert!(!stale_report.source_backprop_replay_ready());
    assert_eq!(
        stale_report.byte_range_diagnostics[0].kind,
        BinaryMachineReplayByteRangeDiagnosticKind::OriginalByteRangeOutsideSelectedImage
    );
    assert!(stale_report.reason.contains("outside selected-image byte range"));
    assert!(stale_blocker.contains("outside selected-image byte range"));

    let mismatched_range = replay_machine_witness(
        &witness,
        &BinaryMachineReplayConfig::default(),
        &BoundedMachineCodeReplayBackend::new(image_with_identity(
            Some(test_artifact_digest()),
            Some(offset_test_selected_image()),
        )),
    );
    let range_blocker = mismatched_range
        .source_backprop_replay_blocker_reason()
        .expect("mismatched selected-image range should block source backprop");
    assert_eq!(mismatched_range.status, BinaryMachineReplayStatus::Spurious);
    assert!(!mismatched_range.source_backprop_replay_ready());
    assert_eq!(
        mismatched_range.byte_range_diagnostics[0].kind,
        BinaryMachineReplayByteRangeDiagnosticKind::SelectedImageByteRangeMismatch
    );
    assert!(mismatched_range.reason.contains("selected-image byte range"));
    assert!(range_blocker.contains("selected-image byte range"));
}

#[test]
fn sat_counterexample_dispatch_requires_exact_machine_witness_replay() {
    let dispatch = sat_dispatch_with_witness();

    let evidence =
        replay_solver_dispatch_counterexample(&dispatch, None, &BinaryReplayConfig::default());

    assert!(evidence.produced_witness());
    assert_eq!(evidence.replay_requirement, BinaryReplayRequirement::ExactMachineWitnessReplay);
    assert!(!evidence.requirement_satisfied);
    assert!(evidence.needs_machine_witness_replay());
    assert!(!evidence.needs_checked_certificate());
    assert_eq!(evidence.replay, ReplayStatus::NotAttempted);

    let report = evidence.replay_report.as_ref().expect("SAT witness should produce report");
    assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::NeedsMachineReplay);
    assert!(report.needs_machine_replay);
}

#[test]
fn sat_counterexample_dispatch_distinguishes_witness_only_from_exact_machine_replay() {
    let dispatch = sat_dispatch_with_witness();

    let witness_only =
        replay_solver_dispatch_counterexample(&dispatch, None, &BinaryReplayConfig::default());

    assert!(witness_only.produced_witness());
    assert_eq!(witness_only.replay_requirement, BinaryReplayRequirement::ExactMachineWitnessReplay);
    assert!(!witness_only.requirement_satisfied);
    assert!(witness_only.needs_machine_witness_replay());
    assert_eq!(witness_only.replay, ReplayStatus::NotAttempted);
    let witness_only_report =
        witness_only.replay_report.as_ref().expect("SAT witness should produce report");
    assert_eq!(
        witness_only_report.machine_replay.status,
        BinaryMachineReplayStatus::NeedsMachineReplay
    );

    let backend = BoundedMachineCodeReplayBackend::new(image(
        BoundedMachineCodeArchitecture::Aarch64,
        [(0x401000, AARCH64_NOP_BYTES.to_vec())],
    ));

    let exact_machine = replay_machine_witness(
        &witness_only_report.normalized_witness,
        &BinaryMachineReplayConfig::default(),
        &backend,
    );

    assert_eq!(exact_machine.status, BinaryMachineReplayStatus::Replayed);
    assert_eq!(exact_machine.trust_types_status, ReplayStatus::Replayed);
    assert!(exact_machine.matched_instruction_trace);
    assert_eq!(exact_machine.expected_instruction_trace.len(), 1);
    assert_eq!(exact_machine.observed_instruction_trace.len(), 1);
    assert_eq!(
        exact_machine.observed_instruction_trace[0].origin.instruction_bytes,
        AARCH64_NOP_BYTES.to_vec()
    );
}

#[test]
fn sat_exact_replay_rejects_selected_image_segment_without_execute_permission() {
    let dispatch = sat_dispatch_with_witness();
    let mut loaded_image =
        image(BoundedMachineCodeArchitecture::Aarch64, [(0x401000, AARCH64_NOP_BYTES.to_vec())]);
    loaded_image.insert_segment(
        0x401000,
        AARCH64_NOP_BYTES.len() as u64,
        BoundedMachineCodeSegmentPermissions::rw(),
    );
    let backend = BoundedMachineCodeReplayBackend::new(loaded_image);

    let evidence = replay_solver_dispatch_counterexample_with_machine_replay(
        &dispatch,
        None,
        &BinaryReplayConfig::default(),
        &BinaryMachineReplayConfig::default(),
        &backend,
    );

    assert!(evidence.produced_witness());
    assert_eq!(evidence.replay_requirement, BinaryReplayRequirement::ExactMachineWitnessReplay);
    assert!(!evidence.requirement_satisfied);
    assert_eq!(evidence.replay, ReplayStatus::Spurious);
    assert!(evidence.reason.contains("SAT counterexample requires exact machine witness replay"));
    assert!(evidence.reason.contains("source-backprop blocked"), "{}", evidence.reason);
    assert!(evidence.reason.contains("non-executable loaded image segments"));

    let report = evidence.replay_report.as_ref().expect("SAT witness should produce report");
    assert_eq!(report.trust_types_status, ReplayStatus::Spurious);
    assert_eq!(report.machine_replay.status, BinaryMachineReplayStatus::Spurious);
    assert_eq!(report.normalized_witness.provenance.selected_image, Some(test_selected_image()));
    assert!(report.normalized_witness.provenance.requires_selected_image_identity);
    assert_eq!(report.machine_replay.expected_selected_image, Some(test_selected_image()));
    assert_eq!(report.machine_replay.observed_selected_image, Some(test_selected_image()));
    assert_eq!(report.machine_replay.expected_artifact_digest, Some(test_artifact_digest()));
    assert_eq!(report.machine_replay.observed_artifact_digest, Some(test_artifact_digest()));
    assert!(!report.machine_replay.matched_instruction_trace);
    assert!(report.machine_replay.observed_instruction_trace.is_empty());
    assert_eq!(report.machine_replay.expected_instruction_trace.len(), 1);
    assert!(report.machine_replay.reason.contains("0x401000"));
    assert!(report.machine_replay.reason.contains("non-executable"));

    let blocker = report
        .machine_replay
        .source_backprop_replay_blocker_reason()
        .expect("non-executable segment must remain an explicit blocker");
    assert!(blocker.contains("source-backprop blocked"), "{blocker}");
    assert!(blocker.contains("non-executable loaded image segments"), "{blocker}");
}

#[test]
fn unsat_dispatch_with_checked_certificate_is_certificate_only_not_machine_replay() {
    let dispatch = unsat_dispatch_with_certificate(ProofCertificateStatus::Checked {
        checker: "ay-cert-check".to_string(),
        format: "lfsc".to_string(),
        sha256: Some("checked-unsat-vc0".to_string()),
    });

    let evidence =
        replay_solver_dispatch_counterexample(&dispatch, None, &BinaryReplayConfig::default());

    assert!(!evidence.produced_witness());
    assert_eq!(evidence.replay_requirement, BinaryReplayRequirement::CheckedUnsatCertificate);
    assert!(evidence.requirement_satisfied);
    assert!(!evidence.needs_machine_witness_replay());
    assert!(!evidence.needs_checked_certificate());
    assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
    assert!(evidence.replay_report.is_none());
    assert!(evidence.reason.contains("checked proof certificate satisfies"));
}

#[test]
fn unknown_unsupported_dispatch_state_has_unsatisfied_requirement() {
    let dispatch = unknown_dispatch();

    let evidence =
        replay_solver_dispatch_counterexample(&dispatch, None, &BinaryReplayConfig::default());

    assert!(!evidence.produced_witness());
    assert_eq!(evidence.replay_requirement, BinaryReplayRequirement::UnknownUnsupportedState);
    assert!(!evidence.requirement_satisfied);
    assert!(!evidence.needs_machine_witness_replay());
    assert!(!evidence.needs_checked_certificate());
    assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
    assert!(evidence.replay_report.is_none());
    assert!(evidence.reason.contains("unsupported"));
}

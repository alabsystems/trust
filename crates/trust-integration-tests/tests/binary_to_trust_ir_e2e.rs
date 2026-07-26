// trust-integration-tests/tests/binary_to_trust_ir_e2e.rs
//
// End-to-end scaffold for binary -> parse -> lift -> TrustIr -> VC generation.

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_binary_parse::Elf64;
use trust_lift::{BinaryLiftOptions, Lifter, LocalLayout};
use trust_proof_cert::{
    BinaryCertificateCheckRequest, CheckedBinaryCertificateAuditExport,
    CheckedBinaryCertificateExternalCheckerRunner, CheckedBinaryCertificateManifest,
    CheckedBinaryCertificateManifestAcceptanceRequest, CheckedBinaryCertificateManifestEntry,
    CheckedBinaryCertificateSourceBackpropagationGate, SolverProofExport,
    StructuralBinaryCertificateChecker, check_binary_certificate,
    import_checked_certificate_manifest_entry_for_dispatch, persist_checked_certificate_artifact,
    persist_checked_certificate_audit_export_bundle,
};
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    Endianness, Formula, MemoryAccessFact, MemoryAccessKind, MemoryRegionKind,
    ProofCertificateStatus, ReplayStatus, SerializableVc, SolverDispatchRecord,
    SolverDispatchStatus, SolverQuerySemantics, Sort, SourceSpan, Terminator, VcKind,
    VerificationCondition,
};

const FIXTURE_SYMBOL: &str = "trust_fixture_return";
const X86_64_LOAD_FIXTURE_SYMBOL: &str = "trust_fixture_x86_load";
const X86_64_LOAD_FIXTURE_ENTRY: u64 = 0x400000;
const X86_64_LOAD_FIXTURE_SHA256: &str =
    "251757e36749c41d81a42feb4764e9ed80c354990f9de66858a498e549524000";
const X86_64_LOAD_FIXTURE_HEX: &str =
    include_str!("../../../tests/fixtures/binary_decomp/x86_64-load-elf.hex");
const PRODUCTION_POSITIVE_X86_64_LOAD_TRUST_CG_GOLDEN: &str =
    include_str!("binary_decompile_convert_trust_cg_production_positive_golden.json");
const UNDECODABLE_FIXTURE_SYMBOL: &str = "trust_fixture_undecodable";
const UNSUPPORTED_FIXTURE_SYMBOL: &str = "trust_fixture_unsupported";
const UNRESOLVED_FIXTURE_SYMBOL: &str = "trust_fixture_unresolved";
const UNRESOLVED_INDIRECT_BRANCH_GOLDEN: &str =
    include_str!("binary_unresolved_indirect_branch_golden.json");

const X86_64_RET_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_return
    .type trust_fixture_return,@function
trust_fixture_return:
    retq
    .size trust_fixture_return, .-trust_fixture_return
    .section .note.GNU-stack,"",@progbits
"#;

const X86_64_UNDECODABLE_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_undecodable
    .type trust_fixture_undecodable,@function
trust_fixture_undecodable:
    retq
    .byte 0xff
    .size trust_fixture_undecodable, .-trust_fixture_undecodable
    .section .note.GNU-stack,"",@progbits
"#;

const X86_64_UNSUPPORTED_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_unsupported
    .type trust_fixture_unsupported,@function
trust_fixture_unsupported:
    .byte 0xcc
    .size trust_fixture_unsupported, .-trust_fixture_unsupported
    .section .note.GNU-stack,"",@progbits
"#;

const X86_64_UNRESOLVED_ASM: &str = r#"
    .text
    .byte 0x90
    .globl trust_fixture_unresolved
    .type trust_fixture_unresolved,@function
trust_fixture_unresolved:
    .byte 0xff, 0xe0
    .size trust_fixture_unresolved, .-trust_fixture_unresolved
    .section .note.GNU-stack,"",@progbits
"#;

const AARCH64_EXCLUSIVE_ASM: &str = r#"
    .arch armv8-a
    .text
    .globl trust_fixture_aarch64_exclusive
    .type trust_fixture_aarch64_exclusive,%function
trust_fixture_aarch64_exclusive:
    ldaxr x0, [x0]
    ret
    .size trust_fixture_aarch64_exclusive, .-trust_fixture_aarch64_exclusive
    .section .note.GNU-stack,"",@progbits
"#;

#[derive(Clone, Copy)]
struct FailClosedFixtureCase {
    label: &'static str,
    symbol: &'static str,
    expected_fragments: &'static [&'static str],
    build: fn(&Path) -> Result<PathBuf, String>,
}

#[derive(Default)]
struct BinaryVcFamilyCounts {
    memory_access: usize,
    stack_discipline: usize,
    saved_return_address: usize,
    format_string: usize,
    tainted_indirect_branch: usize,
}

impl BinaryVcFamilyCounts {
    fn from_vcs(vcs: &[trust_types::VerificationCondition]) -> Self {
        let mut counts = Self::default();
        for vc in vcs {
            match &vc.kind {
                VcKind::Assertion { message }
                    if message.contains("binary memory read")
                        || message.contains("binary memory write")
                        || message.contains("missing access fact") =>
                {
                    counts.memory_access += 1;
                }
                VcKind::Assertion { message } if message.contains("stack pointer not restored") => {
                    counts.stack_discipline += 1;
                }
                VcKind::SavedReturnAddressOverwrite { .. } => {
                    counts.saved_return_address += 1;
                }
                VcKind::FormatStringViolation { .. } => {
                    counts.format_string += 1;
                }
                VcKind::TaintedIndirectBranch { .. } => {
                    counts.tainted_indirect_branch += 1;
                }
                _ => {}
            }
        }
        counts
    }
}

const X86_64_EXEC_ENTRY_ASM: &str = r#"
    .text
    .globl _start
    .type _start,@function
_start:
    retq
    .size _start, .-_start
    .section .note.GNU-stack,"",@progbits
"#;

const AARCH64_EXEC_ENTRY_ASM: &str = r#"
    .text
    .globl _start
    .type _start,%function
_start:
    ret
    .size _start, .-_start
    .section .note.GNU-stack,"",@progbits
"#;

#[test]
fn test_generated_elf_parse_lift_trust_ir_and_binary_vcs() {
    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = fs::read(&elf_path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", elf_path.display()));
    let elf = Elf64::parse(&bytes)
        .unwrap_or_else(|e| panic!("failed to parse generated ELF {}: {e}", elf_path.display()));
    assert_eq!(elf.header.e_machine, 0x3e, "fixture must be x86_64 ELF");

    let lifted_binary = trust_lift::lift_binary_to_trust_ir(
        &bytes,
        BinaryLiftOptions::functions_by_name([FIXTURE_SYMBOL]),
    )
    .expect("public binary-to-TrustIr API should lift fixture symbol");
    assert_eq!(lifted_binary.format, "ELF");
    assert_eq!(lifted_binary.architecture, "x86-64");
    assert_eq!(lifted_binary.functions.len(), 1);
    assert!(lifted_binary.failures.is_empty());

    let lifter = Lifter::from_elf(&elf).expect("x86_64 ELF should create a lifter");
    let boundary =
        lifter.functions().iter().find(|boundary| boundary.name == FIXTURE_SYMBOL).unwrap_or_else(
            || {
                panic!(
                    "expected {FIXTURE_SYMBOL} in detected ELF function symbols; got {:?}",
                    lifter.functions()
                )
            },
        );

    let lifted = lifter
        .lift_function(&bytes, boundary.start)
        .expect("generated ELF function should lift to TrustIr");
    let api_lifted = &lifted_binary.functions[0];
    assert_eq!(api_lifted.name, lifted.name);
    assert_eq!(api_lifted.entry_point, lifted.entry_point);

    assert_eq!(lifted.name, FIXTURE_SYMBOL);
    assert_eq!(lifted.entry_point, boundary.start);
    assert_eq!(lifted.cfg.block_count(), 1, "ret-only fixture should recover one CFG block");
    assert_eq!(lifted.cfg.blocks[0].instructions.len(), 1, "ret should decode as one instruction");
    assert_eq!(lifted.trust_ir_body.locals.len(), LocalLayout::x86_64().total);
    assert!(
        lifted.trust_ir_body.blocks.iter().any(|block| matches!(block.terminator, Terminator::Return)),
        "lifted TrustIr should contain a return terminator"
    );
    assert!(lifted.ssa.is_some(), "lift_function should attach SSA metadata");
    assert!(!lifted.annotations.is_empty(), "lift_function should annotate decoded instructions");

    let verifiable = trust_vcgen::lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, FIXTURE_SYMBOL);
    assert_eq!(verifiable.def_path, format!("binary::{FIXTURE_SYMBOL}"));
    assert_eq!(verifiable.body.blocks.len(), lifted.trust_ir_body.blocks.len());

    let vcs = trust_vcgen::lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "binary VC generation should produce at least stack discipline VCs");
    assert!(vcs.iter().all(|vc| vc.function == FIXTURE_SYMBOL));
    let family_counts = BinaryVcFamilyCounts::from_vcs(&vcs);
    assert_eq!(
        family_counts.stack_discipline, 1,
        "ret-only fixture should emit exactly one stack-discipline VC"
    );
    assert_eq!(
        family_counts.tainted_indirect_branch, 0,
        "direct ret-only fixture should not emit an indirect-branch VC"
    );
    assert!(
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("stack pointer not restored")
            )
        }),
        "ret-only binary fixture should exercise the binary stack-discipline VC path"
    );
}

#[test]
fn test_binary_lift_fails_closed_on_undecodable_function_bytes() {
    let tmp = tempfile::tempdir().expect("create temp undecodable fixture dir");
    let elf_path = match build_x86_64_undecodable_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    assert_strict_and_best_effort_lift_failure(
        &bytes,
        UNDECODABLE_FIXTURE_SYMBOL,
        &["disassembly error"],
    );
}

#[test]
fn test_binary_lift_fails_closed_on_unsupported_instruction_semantics() {
    let tmp = tempfile::tempdir().expect("create temp unsupported fixture dir");
    let elf_path = match build_x86_64_unsupported_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    // Trust: lifter no longer phrases failures as "unsupported opcode"; the
    // current strict failure surface is "unsupported instruction semantics"
    // followed by the concrete opcode (e.g. `opcode Int3:` and
    // `opcode Some("Int3")`). Match both pieces of evidence instead of the
    // historical "unsupported opcode" phrasing.
    assert_strict_and_best_effort_lift_failure(
        &bytes,
        UNSUPPORTED_FIXTURE_SYMBOL,
        &["unsupported instruction semantics", "opcode Int3"],
    );
}

#[test]
fn test_binary_lift_fails_closed_on_unresolved_indirect_control_flow() {
    let tmp = tempfile::tempdir().expect("create temp unresolved fixture dir");
    let elf_path = match build_x86_64_unresolved_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    assert_strict_and_best_effort_lift_failure(
        &bytes,
        UNRESOLVED_FIXTURE_SYMBOL,
        &["CFG proof mode", "has no direct CFG target"],
    );
}

#[test]
fn test_aarch64_exclusive_lift_blocker_names_atomic_exclusive_evidence() {
    let tmp = tempfile::tempdir().expect("create temp AArch64 exclusive fixture dir");
    let elf_path = match build_aarch64_exclusive_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = read_checked_elf_fixture(&elf_path, 0xb7, "AArch64 exclusive fixture");
    let elf = Elf64::parse(&bytes).expect("AArch64 fixture should parse");
    let lifter = Lifter::from_elf(&elf).expect("AArch64 ELF should create a lifter");
    let err = lifter.lift_function(&bytes, 0).expect_err("exclusive load must fail closed");
    assert_contains_all(
        &err.to_string(),
        &[
            "AArch64 atomic/exclusive memory-order semantics",
            "exclusive monitor semantics",
            "proof-consumed witnesses",
        ],
        "AArch64 exclusive lift failure",
    );
}

#[test]
fn test_unresolved_indirect_branch_golden_json_stays_rejected_not_proof_grade() {
    let golden: serde_json::Value = serde_json::from_str(UNRESOLVED_INDIRECT_BRANCH_GOLDEN)
        .expect("unresolved indirect branch golden JSON should parse");
    assert_eq!(golden["fixture_family"], "unresolved_indirect_branch");
    assert_eq!(golden["symbol"], UNRESOLVED_FIXTURE_SYMBOL);

    let expected_fragments = golden["expected_unsupported_fragments"]
        .as_array()
        .expect("golden expected_unsupported_fragments should be an array")
        .iter()
        .map(|value| value.as_str().expect("golden fragment should be a string"))
        .collect::<Vec<_>>();

    let tmp = tempfile::tempdir().expect("create temp unresolved golden fixture dir");
    let elf_path = match build_x86_64_unresolved_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    assert_strict_and_best_effort_lift_failure(
        &bytes,
        UNRESOLVED_FIXTURE_SYMBOL,
        &expected_fragments,
    );

    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };
    let entry = function_entry_for_symbol(&bytes, UNRESOLVED_FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");
    let output = Command::new(&targo_trust)
        .arg("verify-binary")
        .arg(&elf_path)
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--solver")
        .arg("ay")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !output.status.success(),
        "golden unresolved indirect branch fixture must fail closed\nstdout:\n{stdout}"
    );
    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}"));
    assert_eq!(json["status"], golden["expected_verify_binary_status"]);
    assert_eq!(json["verification_status"], golden["expected_verification_status"]);
    assert_eq!(json["trust_level"], golden["expected_trust_level"]);
    assert_eq!(json["functions_analyzed"].as_u64(), Some(0));
    assert_eq!(json["vcs"].as_u64(), Some(0), "unliftable indirect branch must not dispatch VCs");
    assert_eq!(json["solver_results"]["status"], "not_run");
    assert_eq!(json["solver_results"]["total"].as_u64(), Some(0));
    assert!(json["solver_result_items"].as_array().is_some_and(Vec::is_empty));
    assert_no_proof_grade_release_claim(&json, "unresolved indirect branch golden");
    assert_optional_proof_gate_rejected(&json);
}

#[test]
fn test_binary_vcs_fail_closed_on_unknown_memory_read_fact() {
    let tmp = tempfile::tempdir().expect("create temp unknown-memory fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let elf = Elf64::parse(&bytes).expect("generated fixture should parse as ELF");
    let lifter = Lifter::from_elf(&elf).expect("x86_64 ELF should create a lifter");
    let mut lifted = lifter
        .lift_function(&bytes, entry)
        .expect("generated ELF function should lift before injecting memory uncertainty");

    lifted.memory_accesses = vec![MemoryAccessFact {
        origin: BinaryOrigin {
            binary_path: Some(elf_path.display().to_string()),
            function_entry: Some(entry),
            instruction_address: entry,
            instruction_size: Some(1),
            encoding: None,
            instruction_bytes: vec![0xc3],
            source: None,
        },
        kind: MemoryAccessKind::Read,
        address: Formula::Var("unknown_binary_read_addr".into(), Sort::BitVec(64)),
        width_bytes: 8,
        endianness: Endianness::Little,
        region: MemoryRegionKind::Unknown,
        base_object: None,
        offset: None,
        extent: None,
        provenance: None,
        taint: vec!["unknown-region".into()],
    }];

    let vcs = trust_vcgen::lift_adapter::generate_binary_vcs(&lifted);
    let memory_vc = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message }
                    if message.contains("binary memory read invalid")
            )
        })
        .unwrap_or_else(|| panic!("unknown memory read should emit a fail-closed VC: {vcs:?}"));

    assert_eq!(
        memory_vc.formula,
        Formula::Bool(true),
        "unknown-region memory reads must become unconditional bad-state VCs"
    );
    assert_eq!(memory_vc.function, FIXTURE_SYMBOL);
    assert_eq!(memory_vc.location.file, format!("binary:0x{entry:x}"));
}

#[test]
fn test_macho_aarch64_fixture_gate_is_explicit_in_elf_only_integration_tests() {
    let skip_reason = macho_aarch64_skip_reason();
    assert!(skip_reason.contains("Mach-O/AArch64"), "skip reason: {skip_reason}");
    assert!(skip_reason.contains("trust-lift"), "skip reason: {skip_reason}");
    eprintln!("SKIP: {skip_reason}");
}

fn assert_strict_and_best_effort_lift_failure(
    bytes: &[u8],
    symbol: &str,
    expected_fragments: &[&str],
) {
    let strict_error =
        trust_lift::lift_binary_to_trust_ir(bytes, BinaryLiftOptions::functions_by_name([symbol]))
            .expect_err("strict binary lift must fail closed");
    let strict_error = strict_error.to_string();
    assert_contains_all(&strict_error, expected_fragments, "strict failure");

    let best_effort = trust_lift::lift_binary_to_trust_ir(
        bytes,
        BinaryLiftOptions::functions_by_name([symbol]).best_effort(),
    )
    .unwrap_or_else(|e| panic!("best-effort binary lift should collect {symbol} failure: {e}"));
    assert!(best_effort.functions.is_empty(), "{symbol} must not produce TrustIr");
    assert_eq!(best_effort.failures.len(), 1);
    let failure = &best_effort.failures[0];
    assert_eq!(failure.name.as_deref(), Some(symbol));
    assert_contains_all(&failure.error, expected_fragments, "best-effort failure");
}

fn assert_contains_all(haystack: &str, expected_fragments: &[&str], context: &str) {
    for fragment in expected_fragments {
        assert!(
            haystack.contains(fragment),
            "{context} should contain `{fragment}`, got: {haystack}"
        );
    }
}

fn assert_json_canonical_digest_uri(value: &serde_json::Value, context: &str) {
    let digest =
        value.as_str().unwrap_or_else(|| panic!("{context}: expected digest string, got {value}"));
    let hex = digest
        .strip_prefix("sha256:")
        .unwrap_or_else(|| panic!("{context}: expected sha256:<hex> digest, got {digest}"));
    assert_eq!(hex.len(), 64, "{context}: digest is not 64 hex chars: {digest}");
    assert!(
        hex.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{context}: digest is not lowercase canonical hex: {digest}"
    );
}

fn assert_json_blocker_codes_include(
    blockers: &[serde_json::Value],
    expected_codes: &[&str],
    context: &str,
) {
    assert!(!blockers.is_empty(), "{context} should include blockers");
    for expected_code in expected_codes {
        assert!(
            blockers.iter().any(|blocker| blocker["code"].as_str() == Some(expected_code)),
            "{context} should include blocker code `{expected_code}`: {blockers:?}"
        );
    }
}

fn assert_json_value_contains_all(
    value: &serde_json::Value,
    expected_fragments: &[&str],
    context: &str,
) {
    let rendered =
        serde_json::to_string(value).unwrap_or_else(|e| panic!("{context} should serialize: {e}"));
    assert_contains_all(&rendered, expected_fragments, context);
}

fn assert_json_record_kinds_rejected(
    records: &[serde_json::Value],
    expected_kinds: &[&str],
    context: &str,
) {
    assert!(!records.is_empty(), "{context} should include evidence records");
    for expected_kind in expected_kinds {
        assert!(
            records.iter().any(|record| {
                record["kind"].as_str() == Some(expected_kind)
                    && record["accepted"].as_bool() == Some(false)
            }),
            "{context} should include rejected `{expected_kind}` evidence: {records:?}"
        );
    }
}

fn blocker_identity_projection(blockers: &[serde_json::Value]) -> Vec<serde_json::Value> {
    blockers
        .iter()
        .map(|blocker| {
            serde_json::json!({
                "code": blocker["code"].clone(),
                "stage": blocker.get("stage").cloned().unwrap_or(serde_json::Value::Null),
                "feature": blocker.get("feature").cloned().unwrap_or(serde_json::Value::Null),
                "evidence_required": blocker
                    .get("evidence_required")
                    .cloned()
                    .unwrap_or(serde_json::Value::Null),
            })
        })
        .collect()
}

fn blocker_codes_projection(blockers: &[serde_json::Value]) -> Vec<serde_json::Value> {
    blockers.iter().map(|blocker| blocker["code"].clone()).collect()
}

fn target_record_kinds_projection(records: &[serde_json::Value]) -> Vec<serde_json::Value> {
    records.iter().map(|record| record["kind"].clone()).collect()
}

fn source_backpropagation_gate_projection(gate: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "accepted": gate["accepted"].clone(),
        "status": gate["status"].clone(),
        "source_provenance": gate["source_provenance"].clone(),
        "binary_verification_evidence": gate["binary_verification_evidence"].clone(),
        "reconstruction_evidence": gate["reconstruction_evidence"].clone(),
        "checked_certificate_source_backpropagation_gate": gate
            .get("checked_certificate_source_backpropagation_gate")
            .cloned()
            .unwrap_or(serde_json::Value::Null),
        "blocker_identities": blocker_identity_projection(
            gate["blockers"]
                .as_array()
                .expect("source backpropagation blockers"),
        ),
    })
}

fn assert_source_backpropagation_gate_rejected(
    gate: &serde_json::Value,
    source_provenance: &str,
    binary_verification_evidence: &str,
    reconstruction_evidence: &str,
    expected_blocker_codes: &[&str],
    context: &str,
) {
    assert_eq!(gate["accepted"], false, "{context}");
    assert_eq!(gate["status"], "rejected", "{context}");
    assert_eq!(gate["source_provenance"], source_provenance, "{context}");
    assert_eq!(gate["binary_verification_evidence"], binary_verification_evidence, "{context}");
    assert_eq!(gate["reconstruction_evidence"], reconstruction_evidence, "{context}");
    let blockers =
        gate["blockers"].as_array().expect("source_backpropagation_gate blockers should be array");
    assert_json_blocker_codes_include(blockers, expected_blocker_codes, context);
}

fn assert_checked_certificate_evidence_blocks_release(evidence: &serde_json::Value, context: &str) {
    assert_eq!(evidence["status"], "blocked", "{context}");
    assert_eq!(evidence["raw_solver_proof_bytes_sufficient"], false, "{context}");
    if let Some(accepted) = evidence.get("proof_grade_release_accepted") {
        assert_eq!(accepted, false, "{context}");
    }
    assert!(
        evidence["blockers"].as_array().is_some_and(|blockers| !blockers.is_empty())
            || evidence["proof_grade_release_blockers"]
                .as_array()
                .is_some_and(|blockers| !blockers.is_empty()),
        "{context} should name checked-certificate blockers: {evidence}"
    );
}

fn assert_convert_checked_certificate_preconditions_rejected(
    evidence: &serde_json::Value,
    context: &str,
) {
    assert_eq!(evidence["required"], true, "{context}");
    assert_eq!(evidence["status"], "blocked", "{context}");
    assert_eq!(evidence["proof_grade_release_accepted"], false, "{context}");
    assert_eq!(evidence["raw_solver_proof_bytes_sufficient"], false, "{context}");
    assert_eq!(evidence["normalized_solver_proof_exports"].as_u64(), Some(0), "{context}");
    assert_eq!(evidence["checked_certificates"].as_u64(), Some(0), "{context}");
    assert_eq!(evidence["loader"]["status"], "not_requested", "{context}");
    assert_production_positive_golden_inventory_fail_closed(evidence, "trust-cg", context);

    let release_blockers = evidence["proof_grade_release_blockers"]
        .as_array()
        .expect("proof_grade_release_blockers should be an array");
    assert_json_blocker_codes_include(
        release_blockers,
        &[
            "proof-grade-artifact-missing",
            "translation-validation-missing",
            "target-semantic-validation-missing",
            "checked-certificate-missing",
            "exact-machine-replay-missing",
            "symbolic-formula-preservation-not-consumed",
            "unsupported-ledger-nonempty",
        ],
        context,
    );

    let blockers = evidence["blockers"].as_array().expect("checked-certificate blockers array");
    assert_json_blocker_codes_include(
        blockers,
        &[
            "proof-grade-artifact-missing",
            "convert-checked-certificate-loader-missing",
            "proof-evidence-missing",
            "exact-machine-replay-missing",
            "symbolic-formula-preservation-not-consumed",
            "unsupported-ledger-nonempty",
        ],
        context,
    );
}

fn assert_target_proof_consumer_evidence_rejected(
    evidence: &serde_json::Value,
    target: &str,
    context: &str,
) {
    assert_eq!(evidence["target"], target, "{context}");
    assert_eq!(evidence["status"], "rejected", "{context}");
    assert_eq!(evidence["target_semantics_consumed"], false, "{context}");
    let blockers =
        evidence["blockers"].as_array().expect("target proof-consumer blockers should be array");
    assert_json_blocker_codes_include(
        blockers,
        &[
            "target-semantics-not-consumed",
            "symbolic-formula-not-consumed-by-target-semantics",
            "missing-checked-proof-certificate",
            "missing-proof-replay-metadata",
        ],
        context,
    );
    let records =
        evidence["records"].as_array().expect("target proof-consumer records should be array");
    assert_json_record_kinds_rejected(
        records,
        &["target_semantics", "symbolic_formula", "checked_certificate", "proof_replay"],
        context,
    );
}

fn assert_trust_ir_target_proof_consumer_identity_accepted(
    json: &serde_json::Value,
    output_content: &str,
    context: &str,
) {
    let expected_output = format!("trust_ir-json:sha256:{}", trust_types::digest::stable_sha256_hex(output_content.as_bytes()));
    let evidence = &json["target_proof_consumer_evidence"];
    let records =
        evidence["records"].as_array().expect("target proof-consumer records should be array");
    let binding = &evidence["binding"];
    let target_validation_blockers = json["target_validation_blockers"]
        .as_array()
        .expect("target_validation_blockers should be an array");

    assert_eq!(evidence["target"], "trust_ir", "{context}");
    assert_eq!(binding["target"], "trust_ir", "{context}");
    assert_eq!(binding["target_output"].as_str(), Some(expected_output.as_str()), "{context}");
    if target_validation_blockers.is_empty() {
        assert_eq!(evidence["status"], "accepted", "{context}");
        assert_eq!(evidence["target_semantics_consumed"], true, "{context}");
        assert_eq!(binding["status"], "accepted", "{context}");
        assert_eq!(binding["target_semantics_consumed"], true, "{context}");
        assert!(
            evidence["blockers"].as_array().is_some_and(Vec::is_empty),
            "{context}: TrustIr identity target consumer should not carry blockers: {evidence}"
        );
    } else {
        assert_eq!(evidence["status"], "rejected", "{context}");
        assert_eq!(evidence["target_semantics_consumed"], false, "{context}");
        assert_eq!(binding["status"], "rejected", "{context}");
        assert_eq!(binding["target_semantics_consumed"], false, "{context}");
        assert!(
            evidence["blockers"]
                .as_array()
                .expect("target consumer blockers")
                .iter()
                .any(|blocker| blocker["code"] == "trust_ir-target-validation-blockers-present"),
            "{context}: target validation blockers must keep TrustIr target consumer rejected: {evidence}"
        );
    }
    assert!(
        binding["inputs"]
            .as_array()
            .expect("binding inputs")
            .iter()
            .all(|input| { input["target_output"].as_str() == Some(expected_output.as_str()) }),
        "{context}: binding inputs must name the current TrustIr output digest: {binding}"
    );
    for kind in ["target_artifact", "lifted_binary_trust_ir", "reconstruction_refinement"] {
        assert!(
            records.iter().any(|record| {
                record["kind"].as_str() == Some(kind) && record["accepted"].as_bool() == Some(true)
            }),
            "{context}: missing accepted `{kind}` target proof-consumer record: {evidence}"
        );
    }
    assert!(
        records.iter().any(|record| record["kind"].as_str() == Some("target_semantics")),
        "{context}: missing target_semantics target proof-consumer record: {evidence}"
    );
    assert!(
        records.iter().any(|record| {
            record["kind"].as_str() == Some("target_artifact")
                && record["identifier"].as_str() == Some(expected_output.as_str())
                && record["accepted"].as_bool() == Some(true)
        }),
        "{context}: missing content-addressed target artifact record: {evidence}"
    );
    assert_eq!(
        json["artifact_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"],
        "{context}"
    );
    assert_eq!(
        json["target_evidence"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"],
        "{context}"
    );
}

fn assert_checked_certificate_readback_keeps_source_backprop_closed(
    evidence: &serde_json::Value,
    dispatch_id: &str,
    context: &str,
) {
    assert_eq!(evidence["required"], true, "{context}");
    assert_eq!(evidence["status"], "blocked", "{context}");
    assert_eq!(evidence["proof_grade_release_accepted"], false, "{context}");
    assert_eq!(evidence["loader"]["status"], "loaded", "{context}");
    assert_eq!(evidence["loader"]["requested_artifacts"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["loader"]["loaded_artifacts"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["checked_artifact_rows"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["accepted_certificate_rows"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["proof_export_readback_rows"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["checked_certificate_readback_rows"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["checker_successes"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["checked_certificates"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["normalized_solver_proof_exports"].as_u64(), Some(1), "{context}");
    assert_eq!(evidence["raw_solver_proof_bytes_sufficient"], false, "{context}");
    assert_production_positive_golden_inventory_fail_closed(evidence, "trust-cg", context);

    let readback_records =
        evidence["readback_records"].as_array().expect("readback records should be array");
    assert_eq!(readback_records.len(), 1, "{context}");
    let readback = &readback_records[0];
    assert_eq!(readback["status"], "readback", "{context}");
    assert_eq!(readback["dispatch_id"].as_str(), Some(dispatch_id), "{context}");
    assert!(
        matches!(readback["replay"].as_str(), Some("NotAttempted" | "not_attempted")),
        "{context}: replay readback must remain not-attempted, got {readback}"
    );
    assert_eq!(
        readback["binary_artifact_digest_identity"]["root_artifact_digest"]["algorithm"], "sha256",
        "{context}"
    );
    assert_eq!(
        readback["binary_artifact_digest_identity"]["selected_image"]["file_offset"].as_u64(),
        Some(0),
        "{context}"
    );
    assert_eq!(
        readback["binary_artifact_digest_identity"]["selected_image"]["file_size"].as_u64(),
        Some(64),
        "{context}"
    );
    assert_eq!(
        readback["binary_artifact_digest_identity"]["selected_image"]["sha256"],
        readback["binary_artifact_digest_identity"]["root_artifact_digest"]["value"],
        "{context}"
    );
    assert_eq!(
        readback["source_backpropagation_gate"]["source_backpropagation_allowed"], false,
        "{context}: checked-certificate readback must not authorize source rewrites"
    );
    assert!(
        readback["source_backpropagation_gate"]["blockers"]
            .as_array()
            .expect("readback source-backprop blockers")
            .iter()
            .any(|blocker| blocker.as_str() == Some("source_backpropagation_gate_not_evaluated")),
        "{context}: readback source-backprop gate should remain closed: {readback}"
    );

    let release_blockers = evidence["proof_grade_release_blockers"]
        .as_array()
        .expect("proof_grade_release_blockers should be an array");
    assert_json_blocker_codes_include(
        release_blockers,
        &[
            "proof-grade-artifact-missing",
            "translation-validation-missing",
            "target-semantic-validation-missing",
            "symbolic-formula-preservation-not-consumed",
            "unsupported-ledger-nonempty",
        ],
        context,
    );
    assert!(
        release_blockers.iter().any(|blocker| {
            matches!(
                blocker["code"].as_str(),
                Some(
                    "exact-machine-replay-missing"
                        | "selected-image-replay-identity-missing"
                        | "replay-artifact-digest-identity-missing"
                )
            )
        }),
        "{context} should preserve a replay-identity release blocker: {release_blockers:?}"
    );

    let blockers = evidence["blockers"].as_array().expect("checked-certificate blockers array");
    assert_json_blocker_codes_include(
        blockers,
        &[
            "proof-grade-artifact-missing",
            "translation-validation-missing",
            "target-semantic-validation-missing",
            "symbolic-formula-preservation-not-consumed",
            "unsupported-ledger-nonempty",
        ],
        context,
    );
}

fn assert_production_positive_golden_inventory_fail_closed(
    evidence: &serde_json::Value,
    target: &str,
    context: &str,
) {
    let inventory = &evidence["production_positive_golden_inventory"];
    assert_eq!(inventory["target"], target, "{context}");
    assert_ne!(inventory["status"], "accepted", "{context}");

    if inventory["required"].as_bool() == Some(true) {
        assert_eq!(inventory["status"], "blocked", "{context}");
        let missing_artifacts = inventory["missing_artifacts"]
            .as_array()
            .expect("production-positive missing artifacts should be array");
        assert!(!missing_artifacts.is_empty(), "{context}");
        let missing_names = missing_artifacts
            .iter()
            .map(|artifact| artifact["artifact"].as_str().expect("artifact name"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_contains_all(
            &missing_names,
            &[
                "decompile --to trust_cg --json",
                "decompile -> convert --to trust_cg --json",
                "checked cert manifest",
                "replay identity",
                "unsupported-ledger elimination",
            ],
            context,
        );
    } else {
        assert_eq!(inventory["required"], false, "{context}");
        assert_eq!(inventory["status"], "not_required", "{context}");
        assert!(
            inventory["missing_artifacts"].as_array().is_some_and(Vec::is_empty),
            "{context}: non-required production-positive inventory should not invent missing rows"
        );
    }
}

fn assert_exact_instruction_provenance(
    function: &serde_json::Value,
    entry_arg: &str,
    context: &str,
) {
    let entry =
        u64::from_str_radix(entry_arg.strip_prefix("0x").expect("entry arg should be hex"), 16)
            .expect("entry arg should parse");
    let provenance = function["instruction_provenance"]
        .as_array()
        .and_then(|items| items.first())
        .unwrap_or_else(|| panic!("{context} should expose per-instruction provenance"));
    assert_eq!(provenance["function_entry"].as_u64(), Some(entry), "{context}");
    assert_eq!(provenance["instruction_address"].as_u64(), Some(entry), "{context}");
    assert_eq!(provenance["instruction_size"].as_u64(), Some(1), "{context}");
    assert_eq!(provenance["encoding"].as_u64(), Some(0xc3), "{context}");
    let bytes =
        provenance["instruction_bytes"].as_array().expect("instruction bytes should be an array");
    assert_eq!(bytes.len(), 1, "{context}");
    assert_eq!(bytes[0].as_u64(), Some(0xc3), "{context}");
    let expected_source_file = format!("binary:{entry_arg}");
    assert_eq!(
        provenance["source"]["file"].as_str(),
        Some(expected_source_file.as_str()),
        "{context}"
    );
}

fn assert_decompile_release_gate_blocker_class_coverage(
    json: &serde_json::Value,
    artifact: &serde_json::Value,
    entry_arg: &str,
) {
    let context = "decompile TrustIr proof-grade blocker class coverage";
    assert_eq!(json["artifact_gate"]["accepted"], false, "{context}");
    assert_eq!(json["artifact_gate"]["status"], "rejected", "{context}");
    assert_eq!(json["artifact_gate"]["proof_grade_artifact"], false, "{context}");

    let functions = json["functions"].as_array().expect("functions should be an array");
    assert_exact_instruction_provenance(&functions[0], entry_arg, context);
    assert_exact_instruction_provenance(&artifact["functions"][0], entry_arg, context);

    let metadata = &artifact["metadata"];
    assert_eq!(metadata["root_artifact_digest"]["algorithm"], "sha256", "{context}");
    let root_sha =
        metadata["root_artifact_digest"]["value"].as_str().expect("root digest should be a string");
    assert_eq!(root_sha.len(), 64, "{context}");
    assert_eq!(metadata["selected_image"]["file_offset"].as_u64(), Some(0), "{context}");
    assert_eq!(
        metadata["selected_image"]["file_size"].as_u64(),
        metadata["byte_len"].as_u64(),
        "{context}"
    );
    assert_eq!(metadata["selected_image"]["sha256"].as_str(), Some(root_sha), "{context}");

    let bridge_gate = &artifact["checked_certificate_bridge"]["release_gate"];
    assert_eq!(bridge_gate["accepted"], false, "{context}");
    assert_eq!(bridge_gate["checked_certificates_accepted"], false, "{context}");
    assert_eq!(bridge_gate["replay_accepted"], false, "{context}");
    assert_eq!(bridge_gate["source_provenance_accepted"], false, "{context}");
    assert_eq!(bridge_gate["binary_artifact_identity_accepted"], false, "{context}");
    assert_eq!(bridge_gate["target_reconstruction_accepted"], false, "{context}");
    assert_json_value_contains_all(
        &bridge_gate["replay_identity_blockers"],
        &[
            "matched instruction trace",
            "matched root artifact digest",
            "matched selected-image digest/range",
            "no unchecked boundary evidence",
        ],
        context,
    );

    assert_source_backpropagation_gate_rejected(
        &json["artifact_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
            "checked-certificate-source-backpropagation-gate-missing",
        ],
        context,
    );
    assert_checked_certificate_evidence_blocks_release(
        &json["checked_certificate_readback"],
        context,
    );
    assert_production_positive_golden_inventory_fail_closed(
        &json["checked_certificate_readback"],
        "trust_ir",
        context,
    );
    assert!(
        artifact["unsupported"]["records"].as_array().is_some_and(|records| !records.is_empty()),
        "{context}: unsupported ledger records must remain visible"
    );
}

fn assert_convert_release_gate_blocker_class_coverage(json: &serde_json::Value, entry_arg: &str) {
    let context = "convert trust_cg proof-grade blocker class coverage";
    assert_eq!(json["conversion_gate"]["accepted"], false, "{context}");
    assert_eq!(json["conversion_gate"]["status"], "rejected", "{context}");
    assert_eq!(json["conversion_gate"]["proof_grade_artifact"], false, "{context}");

    let functions = json["functions"].as_array().expect("functions should be an array");
    assert_exact_instruction_provenance(&functions[0], entry_arg, context);

    let release_blockers = json["checked_certificate_readback"]["proof_grade_release_blockers"]
        .as_array()
        .expect("proof_grade_release_blockers should be an array");
    assert_json_blocker_codes_include(
        release_blockers,
        &[
            "proof-grade-artifact-missing",
            "translation-validation-missing",
            "target-semantic-validation-missing",
            "checked-certificate-missing",
            "exact-machine-replay-missing",
            "symbolic-formula-preservation-not-consumed",
            "unsupported-ledger-nonempty",
        ],
        context,
    );
    assert_json_value_contains_all(
        &serde_json::Value::Array(release_blockers.clone()),
        &[
            "ReplayStatus::Replayed",
            "exact replay checked",
            "artifact SHA-256 identity",
            "formula JSON/SMT-LIB/sort metadata",
        ],
        context,
    );

    let target_features = json["target_validation_blockers"]
        .as_array()
        .expect("target_validation_blockers should be an array")
        .iter()
        .map(|blocker| blocker["feature"].as_str().expect("target blocker feature"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_contains_all(
        &target_features,
        &[
            "binary-provenance-not-consumed-by-target-semantics",
            "target-semantics-not-consumed",
            "bounded-empty-slice-non-noop-provenance",
            "bounded-empty-slice-missing-checked-certificate",
            "bounded-empty-slice-missing-exact-replay",
            "non-empty-scalar-checked-certificate-identity-missing",
            "non-empty-scalar-replay-artifact-identity-missing",
            "symbolic-formula-not-consumed-by-target-semantics",
            "missing-proof-replay-metadata",
        ],
        context,
    );
    assert_json_value_contains_all(
        &json["target_validation_blockers"],
        &[
            "exact bytes",
            "canonical proof replay metadata",
            "ReplayStatus::Replayed",
            "artifact SHA-256 identity",
        ],
        context,
    );

    assert!(
        json["preserved_symbolic_formulas"].as_array().is_some_and(|items| !items.is_empty()),
        "{context}: preserved symbolic formulas must stay visible"
    );
    assert_target_proof_consumer_evidence_rejected(
        &json["target_proof_consumer_evidence"],
        "trust-cg",
        context,
    );
    assert_eq!(
        json["conversion_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"],
        "{context}"
    );
    assert_source_backpropagation_gate_rejected(
        &json["conversion_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
            "checked-certificate-source-backpropagation-gate-missing",
        ],
        context,
    );
    assert!(
        json["unsupported"].as_u64().unwrap_or(0) > 0,
        "{context}: unsupported ledger count should remain nonzero"
    );
    assert_json_string_items_contain_all(
        json["unsupported_items"].as_array().expect("unsupported_items"),
        &[
            "non-exact source provenance",
            "non-recovered debug type provenance",
            "parser artifact identity",
        ],
        context,
    );
    assert_production_positive_golden_inventory_fail_closed(
        &json["checked_certificate_readback"],
        "trust-cg",
        context,
    );
    assert_no_proof_grade_release_claim(json, context);
}

fn assert_optional_proof_gate_rejected(json: &serde_json::Value) {
    for key in ["proof_gate", "binary_proof_gate", "proof_grade_gate"] {
        let Some(gate) = json.get(key) else {
            continue;
        };
        assert!(
            gate.as_str().is_some_and(|status| status == "rejected")
                || gate
                    .get("status")
                    .and_then(serde_json::Value::as_str)
                    .is_some_and(|status| status == "rejected"),
            "optional {key} field must be rejected when exposed: {gate}"
        );
    }
    for key in ["proof_gate_status", "binary_proof_gate_status"] {
        if let Some(status) = json.get(key).and_then(serde_json::Value::as_str) {
            assert_eq!(status, "rejected", "optional {key} field must be rejected when exposed");
        }
    }
}

fn assert_no_proof_grade_release_claim(json: &serde_json::Value, context: &str) {
    assert_no_proof_grade_trust_fields(json, context);

    if let Some(gate) = json.get("proof_grade_gate") {
        assert_eq!(
            gate["accepted"].as_bool(),
            Some(false),
            "{context} proof-grade gate must not accept: {gate}"
        );
        assert_eq!(
            gate["status"].as_str(),
            Some("rejected"),
            "{context} proof-grade gate must be rejected: {gate}"
        );
        assert_ne!(
            gate["final_trust_level"].as_str(),
            Some("proof_grade"),
            "{context} proof-grade gate must not report proof_grade final trust: {gate}"
        );
    }

    if let Some(output_content) = json.get("output_content").and_then(serde_json::Value::as_str) {
        if let Ok(content_json) = serde_json::from_str::<serde_json::Value>(output_content) {
            assert_no_proof_grade_trust_fields(&content_json, context);
        } else {
            assert!(
                !output_content.contains("proof_grade"),
                "{context} text output_content must not claim proof_grade: {output_content}"
            );
        }
    }
}

fn assert_no_proof_grade_trust_fields(value: &serde_json::Value, context: &str) {
    match value {
        serde_json::Value::Object(map) => {
            for (key, child) in map {
                if (matches!(
                    key.as_str(),
                    "trust_level" | "output_trust_level" | "final_trust_level"
                ) || key.ends_with("_trust_level"))
                    && let Some(trust_level) = child.as_str() {
                        assert!(
                            !matches!(trust_level, "proof_grade" | "ProofGrade"),
                            "{context} must not emit proof-grade trust in `{key}`: {value}"
                        );
                    }
                assert_no_proof_grade_trust_fields(child, context);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                assert_no_proof_grade_trust_fields(item, context);
            }
        }
        _ => {}
    }
}

fn assert_decompile_partial_trust_ir_shape(json: &serde_json::Value, entry_arg: &str) {
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["format"], "ELF");
    assert_eq!(json["architecture"], "x86-64");
    assert_eq!(json["selection"], "address");
    assert_eq!(json["entry"].as_str(), Some(entry_arg));
    assert_eq!(json["binary_entry"].as_str(), Some("0x0"));
    assert_eq!(json["strict"], true);
    assert_eq!(json["functions_decompiled"].as_u64(), Some(1));
    assert_eq!(json["blocks"].as_u64(), Some(1));
    assert_eq!(json["instructions"].as_u64(), Some(1));
    assert!(json["statements"].as_u64().unwrap_or(0) >= 1);
    assert!(json["memory_facts"].as_u64().unwrap_or(0) >= 1);
    assert!(json["unsupported"].as_u64().unwrap_or(0) >= 1);
    assert_eq!(json["failures"].as_u64(), Some(0));

    let unsupported_items =
        json["unsupported_items"].as_array().expect("unsupported_items should be an array");
    assert_json_string_items_contain_all(
        unsupported_items,
        &[
            "non-exact source provenance",
            "non-recovered debug type provenance",
            "parser artifact identity",
        ],
        "partial TrustIr proof-grade blockers",
    );
    let failure_items = json["failure_items"].as_array().expect("failure_items should be an array");
    assert!(failure_items.is_empty(), "partial fixture has no failure items");

    let functions = json["functions"].as_array().expect("functions should be an array");
    assert_eq!(functions.len(), 1);
    let function = &functions[0];
    assert_eq!(function["name"], FIXTURE_SYMBOL);
    assert_eq!(function["entry"].as_str(), Some(entry_arg));
    assert_eq!(function["blocks"].as_u64(), Some(1));
    assert_eq!(function["instructions"].as_u64(), Some(1));
}

fn assert_binary_only_source_file_provenance(value: &serde_json::Value, context: &str) {
    match value {
        serde_json::Value::Object(map) => {
            for (key, child) in map {
                match key.as_str() {
                    "source_file" | "source_path" | "debug_file" | "debug_path" => {
                        panic!("{context} must not expose invented source mapping field `{key}`")
                    }
                    "file" => {
                        let file = child.as_str().unwrap_or_else(|| {
                            panic!("{context} source file field must be a string: {child}")
                        });
                        assert!(
                            file.starts_with("binary:"),
                            "{context} source file field must stay binary-address-only, got: {file}"
                        );
                    }
                    _ => {}
                }
                assert_binary_only_source_file_provenance(child, context);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                assert_binary_only_source_file_provenance(item, context);
            }
        }
        _ => {}
    }
}

fn assert_text_has_no_source_file_mapping(text: &str, context: &str) {
    for fragment in ["source_file", "source_path", "debug_file", "src/", ".rs", "\"file\""] {
        assert!(
            !text.contains(fragment),
            "{context} must not invent a source file mapping via `{fragment}`: {text}"
        );
    }
}

fn assert_json_string_items_contain_all(
    items: &[serde_json::Value],
    expected_fragments: &[&str],
    context: &str,
) {
    assert!(!items.is_empty(), "{context} should include at least one item");
    let joined = items
        .iter()
        .map(|item| item.as_str().unwrap_or_else(|| panic!("{context} item should be a string")))
        .collect::<Vec<_>>()
        .join("\n");
    assert_contains_all(&joined, expected_fragments, context);
}

fn production_positive_x86_64_load_trust_cg_golden_projection(
    decompile_json: &serde_json::Value,
    convert_json: &serde_json::Value,
    fixture_sha256: &str,
) -> serde_json::Value {
    let output_content = decompile_json["output_content"]
        .as_str()
        .expect("decompile TrustIr output_content should be JSON text");
    let artifact: serde_json::Value = serde_json::from_str(output_content)
        .unwrap_or_else(|e| panic!("decompile TrustIr output_content was not JSON: {e}"));
    let function = &artifact["functions"][0];
    let lifted = &function["lifted"];
    let lifted_body = &lifted["body"];

    serde_json::json!({
        "fixture_family": "production_positive_x86_64_load_decompile_convert_trust_cg",
        "fixture": {
            "symbol": X86_64_LOAD_FIXTURE_SYMBOL,
            "entry": format!("0x{X86_64_LOAD_FIXTURE_ENTRY:x}"),
            "sha256": fixture_sha256,
            "byte_len": artifact["metadata"]["byte_len"].clone(),
            "format": decompile_json["format"].clone(),
            "architecture": decompile_json["architecture"].clone(),
        },
        "decompile_trust_ir": {
            "status": decompile_json["status"].clone(),
            "strict": decompile_json["strict"].clone(),
            "output_kind": decompile_json["output_kind"].clone(),
            "output_trust_level": decompile_json["output_trust_level"].clone(),
            "output_validation": decompile_json["output_validation"].clone(),
            "functions_decompiled": decompile_json["functions_decompiled"].clone(),
            "blocks": decompile_json["blocks"].clone(),
            "instructions": decompile_json["instructions"].clone(),
            "statements": decompile_json["statements"].clone(),
            "memory_facts": decompile_json["memory_facts"].clone(),
            "unsupported": decompile_json["unsupported"].clone(),
            "failures": decompile_json["failures"].clone(),
            "output_content_sha256": optional_string_sha256(decompile_json.get("output_content")),
            "function": function_report_projection(decompile_json),
            "artifact_gate": {
                "accepted": decompile_json["artifact_gate"]["accepted"].clone(),
                "status": decompile_json["artifact_gate"]["status"].clone(),
                "proof_grade_artifact": decompile_json["artifact_gate"]["proof_grade_artifact"].clone(),
                "source_backpropagation_gate": source_backpropagation_gate_projection(
                    &decompile_json["artifact_gate"]["source_backpropagation_gate"]
                ),
            },
            "artifact": {
                "trust_level": artifact["trust_level"].clone(),
                "metadata": {
                    "format": artifact["metadata"]["format"].clone(),
                    "image_kind": artifact["metadata"]["image_kind"].clone(),
                    "architecture": artifact["metadata"]["architecture"].clone(),
                    "entry_point": artifact["metadata"]["entry_point"].clone(),
                    "byte_len": artifact["metadata"]["byte_len"].clone(),
                    "root_artifact_digest": artifact["metadata"]["root_artifact_digest"].clone(),
                    "selected_image": artifact["metadata"]["selected_image"].clone(),
                    "segments": artifact["metadata"]["segments"].clone(),
                    "symbols": artifact["metadata"]["symbols"].clone(),
                },
                "source_provenance_status": artifact["source_provenance"]["status"].clone(),
                "module_summary": module_summary_projection(&artifact),
                "lifted_body": {
                    "def_path": lifted["def_path"].clone(),
                    "local_count": lifted_body["locals"].as_array().expect("locals array").len(),
                    "local_names": lifted_body["locals"]
                        .as_array()
                        .expect("locals array")
                        .iter()
                        .map(|local| local["name"].clone())
                        .collect::<Vec<_>>(),
                    "block_count": lifted_body["blocks"].as_array().expect("blocks array").len(),
                    "block_stmt_kinds": lifted_block_stmt_kinds(lifted_body),
                    "block_terminators": lifted_body["blocks"]
                        .as_array()
                        .expect("blocks array")
                        .iter()
                        .map(|block| block["terminator"].clone())
                        .collect::<Vec<_>>(),
                },
                "signature": {
                    "calling_convention": function["signature"]["calling_convention"].clone(),
                    "parameters": function["signature"]["parameters"]
                        .as_array()
                        .expect("signature parameters")
                        .iter()
                        .map(|param| param["storage"]["Register"]["name"].clone())
                        .collect::<Vec<_>>(),
                    "returns": function["signature"]["returns"]
                        .as_array()
                        .expect("signature returns")
                        .iter()
                        .map(|ret| ret["storage"]["Register"]["name"].clone())
                        .collect::<Vec<_>>(),
                    "assumptions": function["signature"]["assumptions"]
                        .as_array()
                        .expect("signature assumptions")
                        .iter()
                        .map(|assumption| assumption["description"].clone())
                        .collect::<Vec<_>>(),
                },
                "memory_accesses": function["memory_accesses"]
                    .as_array()
                    .expect("memory accesses")
                    .iter()
                    .map(memory_access_projection)
                    .collect::<Vec<_>>(),
                "unsupported_records": unsupported_record_projection(
                    artifact["unsupported"]["records"]
                        .as_array()
                        .expect("unsupported records")
                ),
                "verification": function["verification"].clone(),
            },
            "preserved_symbolic_formulas": formula_summaries(decompile_json),
        },
        "convert_trust_cg": {
            "status": convert_json["status"].clone(),
            "strict": convert_json["strict"].clone(),
            "output_kind": convert_json["output_kind"].clone(),
            "output_trust_level": convert_json["output_trust_level"].clone(),
            "output_validation": convert_json["output_validation"].clone(),
            "functions_decompiled": convert_json["functions_decompiled"].clone(),
            "blocks": convert_json["blocks"].clone(),
            "instructions": convert_json["instructions"].clone(),
            "statements": convert_json["statements"].clone(),
            "memory_facts": convert_json["memory_facts"].clone(),
            "unsupported": convert_json["unsupported"].clone(),
            "failures": convert_json["failures"].clone(),
            "output_content_sha256": optional_string_sha256(convert_json.get("output_content")),
            "function": function_report_projection(convert_json),
            "conversion_gate": {
                "target": convert_json["conversion_gate"]["target"].clone(),
                "accepted": convert_json["conversion_gate"]["accepted"].clone(),
                "status": convert_json["conversion_gate"]["status"].clone(),
                "validation": convert_json["conversion_gate"]["validation"].clone(),
                "proof_grade_artifact": convert_json["conversion_gate"]["proof_grade_artifact"].clone(),
                "validation_blocker_count": convert_json["conversion_gate"]["validation_blockers"]
                    .as_array()
                    .expect("conversion gate validation blockers")
                    .len(),
                "blocker_count": convert_json["conversion_gate"]["blockers"]
                    .as_array()
                    .expect("conversion gate blockers")
                    .len(),
                "source_backpropagation_gate": source_backpropagation_gate_projection(
                    &convert_json["conversion_gate"]["source_backpropagation_gate"]
                ),
            },
            "target_validation_blocker_features": convert_json["target_validation_blockers"]
                .as_array()
                .expect("target validation blockers")
                .iter()
                .map(|blocker| blocker["feature"].clone())
                .collect::<Vec<_>>(),
            "proof_grade_release_blocker_codes": convert_json["checked_certificate_readback"]
                ["proof_grade_release_blockers"]
                .as_array()
                .expect("proof-grade release blockers")
                .iter()
                .map(|blocker| blocker["code"].clone())
                .collect::<Vec<_>>(),
            "proof_grade_release_blocker_identities": blocker_identity_projection(
                convert_json["checked_certificate_readback"]["proof_grade_release_blockers"]
                    .as_array()
                    .expect("proof-grade release blockers"),
            ),
            "checked_certificate_readback": {
                "status": convert_json["checked_certificate_readback"]["status"].clone(),
                "loader_status": convert_json["checked_certificate_readback"]["loader"]["status"].clone(),
                "normalized_solver_proof_exports": convert_json["checked_certificate_readback"]
                    ["normalized_solver_proof_exports"]
                    .clone(),
                "checked_certificates": convert_json["checked_certificate_readback"]
                    ["checked_certificates"]
                    .clone(),
                "raw_solver_proof_bytes_sufficient": convert_json["checked_certificate_readback"]
                    ["raw_solver_proof_bytes_sufficient"]
                    .clone(),
                "proof_grade_release_accepted": convert_json["checked_certificate_readback"]
                    ["proof_grade_release_accepted"]
                    .clone(),
                "production_positive_golden_inventory": convert_json["checked_certificate_readback"]
                    ["production_positive_golden_inventory"]
                    .clone(),
            },
            "target_proof_consumer_evidence": {
                "target": convert_json["target_proof_consumer_evidence"]["target"].clone(),
                "status": convert_json["target_proof_consumer_evidence"]["status"].clone(),
                "target_semantics_consumed": convert_json["target_proof_consumer_evidence"]
                    ["target_semantics_consumed"]
                    .clone(),
                "binding": target_proof_consumer_binding_projection(
                    &convert_json["target_proof_consumer_evidence"]
                ),
                "record_kinds": convert_json["target_proof_consumer_evidence"]["records"]
                    .as_array()
                    .expect("target proof-consumer records")
                    .iter()
                    .map(|record| record["kind"].clone())
                    .collect::<Vec<_>>(),
                "record_identities": convert_json["target_proof_consumer_evidence"]["records"]
                    .as_array()
                    .expect("target proof-consumer records")
                    .iter()
                    .map(|record| {
                        serde_json::json!({
                            "kind": record["kind"].clone(),
                            "identifier": record["identifier"].clone(),
                            "accepted": record["accepted"].clone(),
                        })
                    })
                    .collect::<Vec<_>>(),
                "blocker_codes": convert_json["target_proof_consumer_evidence"]["blockers"]
                    .as_array()
                    .expect("target proof-consumer blockers")
                    .iter()
                    .map(|blocker| blocker["code"].clone())
                    .collect::<Vec<_>>(),
            },
            "positive_release_gate_scaffold": production_positive_release_gate_scaffold(
                decompile_json,
                &artifact,
                convert_json,
            ),
            "preserved_symbolic_formulas": formula_summaries(convert_json),
        },
    })
}

fn count_accepted_target_records(records: &[serde_json::Value], kind: &str) -> usize {
    records
        .iter()
        .filter(|record| {
            record["kind"].as_str() == Some(kind) && record["accepted"].as_bool() == Some(true)
        })
        .count()
}

fn readback_has_binary_artifact_digest_identity(record: &serde_json::Value) -> bool {
    let identity = &record["binary_artifact_digest_identity"];
    let root = &identity["root_artifact_digest"];
    let selected = &identity["selected_image"];
    root["algorithm"].as_str() == Some("sha256")
        && root["value"].as_str().is_some_and(|value| !value.is_empty())
        && selected["file_size"].as_u64().unwrap_or(0) > 0
        && selected["sha256"] == root["value"]
}

fn release_blocker_present(blockers: &[serde_json::Value], code: &str) -> bool {
    blockers.iter().any(|blocker| blocker["code"].as_str() == Some(code))
}

fn target_blocker_present(blockers: &[serde_json::Value], code: &str) -> bool {
    blockers.iter().any(|blocker| blocker["code"].as_str() == Some(code))
}

fn target_validation_feature_present(blockers: &[serde_json::Value], feature: &str) -> bool {
    blockers.iter().any(|blocker| blocker["feature"].as_str() == Some(feature))
}

fn production_positive_release_gate_scaffold(
    decompile_json: &serde_json::Value,
    artifact: &serde_json::Value,
    convert_json: &serde_json::Value,
) -> serde_json::Value {
    let checked_certificate = &convert_json["checked_certificate_readback"];
    let release_blockers = checked_certificate["proof_grade_release_blockers"]
        .as_array()
        .expect("proof-grade release blockers");
    let readback_records = checked_certificate["readback_records"]
        .as_array()
        .expect("checked-certificate readback records");
    let source_gate = &convert_json["conversion_gate"]["source_backpropagation_gate"];
    let source_blockers = source_gate["blockers"].as_array().expect("source-backprop blockers");
    let target_consumer = &convert_json["target_proof_consumer_evidence"];
    let target_records = target_consumer["records"].as_array().expect("target consumer records");
    let target_blockers = target_consumer["blockers"].as_array().expect("target consumer blockers");
    let target_validation_blockers =
        convert_json["target_validation_blockers"].as_array().expect("target validation blockers");
    let unsupported_records =
        artifact["unsupported"]["records"].as_array().expect("artifact unsupported records");

    let unsupported_ledger_empty = decompile_json["unsupported"].as_u64() == Some(0)
        && convert_json["unsupported"].as_u64() == Some(0)
        && unsupported_records.is_empty();
    let manifest_identity_rows = readback_records
        .iter()
        .filter(|record| {
            record.get("manifest_identity_sha256").and_then(|value| value.as_str()).is_some()
        })
        .count();
    let source_gate_identity_rows = readback_records
        .iter()
        .filter(|record| {
            record
                .get("source_backpropagation_gate_sha256")
                .and_then(|value| value.as_str())
                .is_some()
        })
        .count();
    let binary_digest_identity_rows = readback_records
        .iter()
        .filter(|record| readback_has_binary_artifact_digest_identity(record))
        .count();
    let checked_cert_readback_identity = !readback_records.is_empty()
        && checked_certificate["normalized_solver_proof_exports"].as_u64().unwrap_or(0) > 0
        && checked_certificate["checked_certificates"].as_u64().unwrap_or(0) > 0
        && checked_certificate["accepted_certificate_rows"].as_u64().unwrap_or(0)
            == checked_certificate["checked_certificates"].as_u64().unwrap_or(0)
        && manifest_identity_rows == readback_records.len()
        && source_gate_identity_rows == readback_records.len()
        && binary_digest_identity_rows == readback_records.len();

    let replayed_readback_records = readback_records
        .iter()
        .filter(|record| matches!(record["replay"].as_str(), Some("replayed" | "Replayed")))
        .count();
    let accepted_replay_digest_identity_rows = readback_records
        .iter()
        .filter(|record| record["replay_digest_identity"]["status"].as_str() == Some("accepted"))
        .count();
    let accepted_proof_replay_records =
        count_accepted_target_records(target_records, "proof_replay");
    let replay_attested = !readback_records.is_empty()
        && replayed_readback_records == readback_records.len()
        && accepted_replay_digest_identity_rows == readback_records.len()
        && accepted_proof_replay_records > 0;

    let missing_refinement_metadata = target_validation_feature_present(
        target_validation_blockers,
        "missing-refinement-metadata",
    );
    let target_binding = target_proof_consumer_binding_projection(target_consumer);
    let target_binding_digest_present = target_binding["available"].as_bool() == Some(true)
        && target_binding["digest_matches_binding"].as_bool() == Some(true)
        && json_string_is_canonical_sha256(&target_binding["binding_sha256"]);
    let target_refinement_consumer = target_consumer["status"].as_str() == Some("accepted")
        && target_consumer["target_semantics_consumed"].as_bool() == Some(true)
        && target_binding_digest_present
        && !missing_refinement_metadata
        && target_blockers.is_empty()
        && target_records.iter().all(|record| record["accepted"].as_bool() == Some(true));

    let source_backprop_handoff = source_gate["accepted"].as_bool() == Some(true)
        && source_gate["status"].as_str() == Some("accepted")
        && source_gate["checked_certificate_source_backpropagation_gate"].as_str()
            == Some("accepted")
        && source_blockers.is_empty();

    let accepted = unsupported_ledger_empty
        && checked_cert_readback_identity
        && replay_attested
        && target_refinement_consumer
        && source_backprop_handoff
        && checked_certificate["proof_grade_release_accepted"].as_bool() == Some(true)
        && convert_json["conversion_gate"]["accepted"].as_bool() == Some(true);

    serde_json::json!({
        "target": convert_json["target"].clone(),
        "status": if accepted { "accepted" } else { "rejected" },
        "accepted": accepted,
        "requires_all_real_evidence": true,
        "prerequisites": {
            "empty_unsupported_ledger": {
                "accepted": unsupported_ledger_empty,
                "decompile_unsupported": decompile_json["unsupported"].clone(),
                "artifact_unsupported_records": unsupported_records.len(),
                "convert_unsupported": convert_json["unsupported"].clone(),
                "release_blocker_present": release_blocker_present(
                    release_blockers,
                    "unsupported-ledger-nonempty",
                ),
            },
            "checked_cert_readback_identity": {
                "accepted": checked_cert_readback_identity,
                "loader_status": checked_certificate["loader"]["status"].clone(),
                "normalized_solver_proof_exports": checked_certificate
                    ["normalized_solver_proof_exports"]
                    .clone(),
                "checked_certificates": checked_certificate["checked_certificates"].clone(),
                "accepted_certificate_rows": checked_certificate
                    ["accepted_certificate_rows"]
                    .clone(),
                "readback_record_count": readback_records.len(),
                "manifest_identity_rows": manifest_identity_rows,
                "source_backpropagation_gate_identity_rows": source_gate_identity_rows,
                "binary_artifact_digest_identity_rows": binary_digest_identity_rows,
                "release_blocker_present": release_blocker_present(
                    release_blockers,
                    "checked-certificate-missing",
                ),
            },
            "replay_attestation": {
                "accepted": replay_attested,
                "raw_solver_proof_bytes_sufficient": checked_certificate
                    ["raw_solver_proof_bytes_sufficient"]
                    .clone(),
                "replayed_readback_records": replayed_readback_records,
                "accepted_replay_digest_identity_rows": accepted_replay_digest_identity_rows,
                "accepted_target_proof_replay_records": accepted_proof_replay_records,
                "target_consumer_blocker_present": target_blocker_present(
                    target_blockers,
                    "missing-proof-replay-metadata",
                ),
            },
            "target_refinement_consumer": {
                "accepted": target_refinement_consumer,
                "target_consumer_status": target_consumer["status"].clone(),
                "target_semantics_consumed": target_consumer
                    ["target_semantics_consumed"]
                    .clone(),
                "missing_refinement_metadata": missing_refinement_metadata,
                "record_kinds": target_record_kinds_projection(target_records),
                "blocker_codes": blocker_codes_projection(target_blockers),
            },
            "target_proof_consumer_binding": {
                "accepted": target_binding_digest_present,
                "available": target_binding["available"].clone(),
                "binding_sha256": target_binding["binding_sha256"].clone(),
                "digest_source": target_binding["digest_source"].clone(),
                "digest_matches_binding": target_binding["digest_matches_binding"].clone(),
                "input_count": target_binding["input_count"].clone(),
                "all_inputs_consumed": target_binding["all_inputs_consumed"].clone(),
                "target_output_sha256": target_binding["target_output_sha256"].clone(),
                "blocker_count": target_binding["blocker_count"].clone(),
            },
            "source_backprop_handoff": {
                "accepted": source_backprop_handoff,
                "gate_status": source_gate["status"].clone(),
                "source_provenance": source_gate["source_provenance"].clone(),
                "binary_verification_evidence": source_gate
                    ["binary_verification_evidence"]
                    .clone(),
                "reconstruction_evidence": source_gate["reconstruction_evidence"].clone(),
                "checked_certificate_source_backpropagation_gate": source_gate
                    ["checked_certificate_source_backpropagation_gate"]
                    .clone(),
                "blocker_codes": blocker_codes_projection(source_blockers),
            },
        },
        "release_blocker_codes": blocker_codes_projection(release_blockers),
    })
}

fn assert_production_positive_release_gate_scaffold_rejected(
    scaffold: &serde_json::Value,
    context: &str,
) {
    assert_eq!(scaffold["target"], "trust-cg", "{context}");
    assert_eq!(scaffold["status"], "rejected", "{context}");
    assert_eq!(scaffold["accepted"], false, "{context}");
    assert_eq!(scaffold["requires_all_real_evidence"], true, "{context}");

    let prerequisites = &scaffold["prerequisites"];
    for key in [
        "empty_unsupported_ledger",
        "checked_cert_readback_identity",
        "replay_attestation",
        "target_refinement_consumer",
        "target_proof_consumer_binding",
        "source_backprop_handoff",
    ] {
        assert_eq!(
            prerequisites[key]["accepted"], false,
            "{context}: `{key}` must remain rejected until backed by real evidence"
        );
    }
    assert_eq!(
        prerequisites["empty_unsupported_ledger"]["release_blocker_present"], true,
        "{context}"
    );
    assert_eq!(
        prerequisites["checked_cert_readback_identity"]["release_blocker_present"], true,
        "{context}"
    );
    assert_eq!(
        prerequisites["replay_attestation"]["target_consumer_blocker_present"], true,
        "{context}"
    );
    assert_eq!(
        prerequisites["target_refinement_consumer"]["missing_refinement_metadata"], true,
        "{context}"
    );
    assert_json_value_contains_all(
        &prerequisites["source_backprop_handoff"]["blocker_codes"],
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
            "checked-certificate-source-backpropagation-gate-missing",
        ],
        context,
    );
}

#[test]
fn test_release_gate_scaffold_records_target_consumer_binding_digest_when_blocked() {
    let binding = serde_json::json!({
        "target": "trust-cg",
        "target_output": "trust_cg-lir:blocked-scalar",
        "status": "rejected",
        "target_semantics_consumed": false,
        "inputs": [
            {
                "kind": "checked_certificate",
                "identifier": "dispatch:vc0",
                "canonical_source": "trust_proof.checked_certificate",
                "target_output": "trust_cg-lir:blocked-scalar",
                "consumed_by_target_semantics": false,
                "detail": "checked certificate is bound but target semantics have not consumed it"
            }
        ],
        "blockers": [
            {
                "code": "target-semantics-not-consumed",
                "detail": "target semantics still reject this binding"
            }
        ]
    });
    let binding_sha256 = json_value_sha256(&binding);
    let decompile_json = serde_json::json!({ "unsupported": 0 });
    let artifact = serde_json::json!({ "unsupported": { "records": [] } });
    let convert_json = serde_json::json!({
        "target": "trust-cg",
        "unsupported": 0,
        "conversion_gate": {
            "accepted": false,
            "source_backpropagation_gate": {
                "accepted": false,
                "status": "rejected",
                "source_provenance": "accepted",
                "binary_verification_evidence": "missing",
                "reconstruction_evidence": "accepted",
                "checked_certificate_source_backpropagation_gate": "missing",
                "blockers": [
                    {
                        "code": "proof-grade-binary-verification-missing"
                    }
                ]
            }
        },
        "checked_certificate_readback": {
            "normalized_solver_proof_exports": 0,
            "checked_certificates": 0,
            "accepted_certificate_rows": 0,
            "raw_solver_proof_bytes_sufficient": false,
            "proof_grade_release_accepted": false,
            "readback_records": [],
            "proof_grade_release_blockers": [
                {
                    "code": "checked-certificate-missing"
                }
            ]
        },
        "target_validation_blockers": [
            {
                "feature": "missing-refinement-metadata"
            }
        ],
        "target_proof_consumer_evidence": {
            "target": "trust-cg",
            "status": "rejected",
            "target_semantics_consumed": false,
            "records": [
                {
                    "kind": "target_semantics",
                    "identifier": "trust_cg-lir",
                    "accepted": false
                }
            ],
            "binding": binding,
            "binding_sha256": binding_sha256,
            "blockers": [
                {
                    "code": "target-semantics-not-consumed"
                }
            ]
        }
    });

    let scaffold =
        production_positive_release_gate_scaffold(&decompile_json, &artifact, &convert_json);
    assert_eq!(scaffold["accepted"], false);
    assert_eq!(scaffold["status"], "rejected");
    assert_eq!(scaffold["prerequisites"]["target_refinement_consumer"]["accepted"], false);

    let target_binding = &scaffold["prerequisites"]["target_proof_consumer_binding"];
    assert_eq!(target_binding["accepted"], true);
    assert_eq!(target_binding["available"], true);
    assert_eq!(target_binding["binding_sha256"], binding_sha256);
    assert_eq!(target_binding["digest_source"], "target_proof_consumer_evidence");
    assert_eq!(target_binding["digest_matches_binding"], true);
    assert_eq!(target_binding["input_count"], 1);
    assert_eq!(target_binding["all_inputs_consumed"], false);
    assert_eq!(target_binding["blocker_count"], 1);
    assert!(json_string_is_canonical_sha256(&target_binding["target_output_sha256"]));
}

fn optional_string_sha256(value: Option<&serde_json::Value>) -> serde_json::Value {
    value
        .and_then(serde_json::Value::as_str)
        .map(|text| serde_json::Value::String(trust_types::digest::stable_sha256_hex(text.as_bytes())))
        .unwrap_or(serde_json::Value::Null)
}

fn json_value_sha256(value: &serde_json::Value) -> String {
    let bytes =
        serde_json::to_vec(value).unwrap_or_else(|e| panic!("JSON value should serialize: {e}"));
    trust_types::digest::stable_sha256_hex(&bytes)
}

fn json_string_is_canonical_sha256(value: &serde_json::Value) -> bool {
    value.as_str().is_some_and(|digest| {
        digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    })
}

fn target_proof_consumer_binding_projection(evidence: &serde_json::Value) -> serde_json::Value {
    let Some(binding) = evidence.get("binding") else {
        return serde_json::json!({
            "available": false,
            "binding_sha256": serde_json::Value::Null,
            "digest_source": "missing",
            "digest_matches_binding": false,
            "status": "missing",
            "target_output_sha256": serde_json::Value::Null,
            "input_count": 0,
            "all_inputs_consumed": false,
            "blocker_count": 0,
        });
    };

    let computed = json_value_sha256(binding);
    let supplied = evidence.get("binding_sha256").and_then(serde_json::Value::as_str);
    let digest = supplied.unwrap_or(&computed);
    let inputs = binding["inputs"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    let blockers = binding["blockers"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    let all_inputs_consumed = !inputs.is_empty()
        && inputs.iter().all(|input| {
            input["consumed_by_target_semantics"].as_bool() == Some(true)
                && input["target_output"] == binding["target_output"]
        });
    let target_output_sha256 = binding["target_output"]
        .as_str()
        .map(|target_output| serde_json::Value::String(trust_types::digest::stable_sha256_hex(target_output.as_bytes())))
        .unwrap_or(serde_json::Value::Null);

    serde_json::json!({
        "available": true,
        "binding_sha256": digest,
        "digest_source": if supplied.is_some() {
            "target_proof_consumer_evidence"
        } else {
            "computed_from_binding"
        },
        "digest_matches_binding": supplied.map(|value| value == computed).unwrap_or(true),
        "status": binding["status"].clone(),
        "target_output_sha256": target_output_sha256,
        "input_count": inputs.len(),
        "all_inputs_consumed": all_inputs_consumed,
        "blocker_count": blockers.len(),
    })
}

fn hex_value(value: &serde_json::Value) -> serde_json::Value {
    value
        .as_u64()
        .map(|number| serde_json::Value::String(format!("0x{number:x}")))
        .unwrap_or(serde_json::Value::Null)
}

fn top_json_kind(value: &serde_json::Value) -> String {
    value.as_object().and_then(|object| object.keys().next()).cloned().unwrap_or_else(|| {
        match value {
            serde_json::Value::Null => "Null",
            serde_json::Value::Bool(_) => "Bool",
            serde_json::Value::Number(_) => "Number",
            serde_json::Value::String(_) => "String",
            serde_json::Value::Array(_) => "Array",
            serde_json::Value::Object(_) => "Object",
        }
        .to_string()
    })
}

fn function_report_projection(report: &serde_json::Value) -> serde_json::Value {
    let function = &report["functions"][0];
    serde_json::json!({
        "name": function["name"].clone(),
        "entry": function["entry"].clone(),
        "blocks": function["blocks"].clone(),
        "instructions": function["instructions"].clone(),
        "statements": function["statements"].clone(),
        "memory_facts": function["memory_facts"].clone(),
        "unsupported": function["unsupported"].clone(),
        "instruction_provenance": function["instruction_provenance"]
            .as_array()
            .expect("instruction provenance")
            .iter()
            .map(instruction_provenance_projection)
            .collect::<Vec<_>>(),
    })
}

fn instruction_provenance_projection(item: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "address": hex_value(&item["instruction_address"]),
        "size": item["instruction_size"].clone(),
        "encoding": item["encoding"].clone(),
        "bytes": item["instruction_bytes"].clone(),
        "source_file": item
            .get("source")
            .and_then(|source| source.get("file"))
            .cloned()
            .unwrap_or(serde_json::Value::Null),
    })
}

fn module_summary_projection(artifact: &serde_json::Value) -> serde_json::Value {
    let functions = artifact["module"]["functions"].as_array().expect("module functions");
    serde_json::json!({
        "function_count": functions.len(),
        "func_type_count": artifact["module"]["func_types"]
            .as_array()
            .expect("module func types")
            .len(),
        "block_counts": functions
            .iter()
            .map(|function| {
                function["blocks"].as_array().expect("module blocks").len()
            })
            .collect::<Vec<_>>(),
        "block_body_lengths": functions
            .iter()
            .map(|function| {
                function["blocks"]
                    .as_array()
                    .expect("module blocks")
                    .iter()
                    .map(|block| block["body"].as_array().expect("module block body").len())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
    })
}

fn lifted_block_stmt_kinds(lifted_body: &serde_json::Value) -> Vec<Vec<String>> {
    lifted_body["blocks"]
        .as_array()
        .expect("lifted blocks")
        .iter()
        .map(|block| {
            block["stmts"]
                .as_array()
                .expect("lifted block statements")
                .iter()
                .map(|stmt| {
                    stmt.as_object()
                        .and_then(|object| object.keys().next())
                        .cloned()
                        .expect("lifted statement should have a kind")
                })
                .collect()
        })
        .collect()
}

fn memory_access_projection(access: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "instruction_address": hex_value(&access["origin"]["instruction_address"]),
        "kind": access["kind"].clone(),
        "width_bytes": access["width_bytes"].clone(),
        "endianness": access["endianness"].clone(),
        "region": access["region"].clone(),
        "base_object": access["base_object"].clone(),
        "provenance": access["provenance"].clone(),
        "address_formula_kind": top_json_kind(&access["address"]),
        "address_formula_sha256": json_value_sha256(&access["address"]),
    })
}

fn unsupported_record_projection(records: &[serde_json::Value]) -> Vec<serde_json::Value> {
    records
        .iter()
        .map(|record| {
            let instruction_address = record
                .get("origin")
                .and_then(|origin| origin.get("instruction_address"))
                .map(hex_value)
                .unwrap_or(serde_json::Value::Null);
            serde_json::json!({
                "stage": record["stage"].clone(),
                "architecture": record["architecture"].clone(),
                "instruction_address": instruction_address,
                "feature": record["feature"].clone(),
            })
        })
        .collect()
}

fn formula_summaries(report: &serde_json::Value) -> Vec<serde_json::Value> {
    report["preserved_symbolic_formulas"]
        .as_array()
        .expect("preserved symbolic formulas")
        .iter()
        .map(|formula| {
            serde_json::json!({
                "target": formula["target"].clone(),
                "function": formula["function"].clone(),
                "block": formula["block"].clone(),
                "statement_index": formula["statement_index"].clone(),
                "location": formula["location"].clone(),
                "formula_kind": top_json_kind(&formula["formula"]),
                "formula_sha256": json_value_sha256(&formula["formula"]),
            })
        })
        .collect()
}

fn macho_aarch64_skip_reason() -> String {
    format!(
        "Mach-O/AArch64 lift fixture skipped in this integration target because trust-lift is \
         enabled with ELF support only; host is {}-{}",
        std::env::consts::ARCH,
        std::env::consts::OS
    )
}

fn fail_closed_fixture_cases() -> [FailClosedFixtureCase; 3] {
    [
        FailClosedFixtureCase {
            label: "undecodable",
            symbol: UNDECODABLE_FIXTURE_SYMBOL,
            expected_fragments: &["disassembly error"],
            build: build_x86_64_undecodable_elf_fixture,
        },
        FailClosedFixtureCase {
            label: "unsupported",
            symbol: UNSUPPORTED_FIXTURE_SYMBOL,
            // Trust: lifter strict failure no longer says "unsupported opcode"
            // — emits "unsupported instruction semantics" plus the concrete
            // opcode (`opcode Int3`).
            expected_fragments: &["unsupported instruction semantics", "opcode Int3"],
            build: build_x86_64_unsupported_elf_fixture,
        },
        FailClosedFixtureCase {
            label: "unresolved",
            symbol: UNRESOLVED_FIXTURE_SYMBOL,
            expected_fragments: &["CFG proof mode", "has no direct CFG target"],
            build: build_x86_64_unresolved_elf_fixture,
        },
    ]
}

#[test]
fn test_host_executable_default_entry_lifts_to_trust_ir_and_vcs() {
    let tmp = tempfile::tempdir().expect("create temp executable fixture dir");
    let fixture = match build_host_executable_fixture(tmp.path()) {
        Ok(fixture) => fixture,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let bytes = fs::read(&fixture.path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", fixture.path.display()));
    let elf = Elf64::parse(&bytes).unwrap_or_else(|e| {
        panic!("failed to parse generated ELF {}: {e}", fixture.path.display())
    });
    assert_ne!(elf.header.e_type, 1, "fixture must be linked, not relocatable");
    assert_eq!(elf.header.e_machine, fixture.elf_machine);
    assert_ne!(elf.entry_point(), 0, "linked executable should have a default entry point");

    let lifted_binary = trust_lift::lift_binary_to_trust_ir(&bytes, BinaryLiftOptions::default())
        .expect("default-entry public binary-to-TrustIr API should lift executable");
    assert_eq!(lifted_binary.format, "ELF");
    assert_eq!(lifted_binary.architecture, fixture.architecture);
    assert_eq!(lifted_binary.entry_point, Some(elf.entry_point()));
    assert!(lifted_binary.failures.is_empty(), "strict default lift should not collect failures");
    assert!(
        !lifted_binary.functions.is_empty(),
        "default-entry executable lift should produce at least one function"
    );

    let lifted = &lifted_binary.functions[0];
    assert_eq!(lifted.entry_point, elf.entry_point());
    assert_eq!(lifted.name, "_start");
    assert!(!lifted.trust_ir_body.blocks.is_empty(), "lifted entry should contain TrustIr blocks");
    assert!(
        lifted.trust_ir_body.blocks.iter().any(|block| matches!(block.terminator, Terminator::Return)),
        "lifted executable entry should contain a return terminator"
    );

    let vcs = trust_vcgen::lift_adapter::generate_binary_vcs(lifted);
    assert!(!vcs.is_empty(), "strict default-entry executable lift should produce binary VCs");
    assert!(vcs.iter().all(|vc| vc.function == lifted.name));
}

#[test]
fn test_targo_trust_lift_json_smoke_for_default_entry_executable() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp executable fixture dir");
    let fixture = match build_host_executable_fixture(tmp.path()) {
        Ok(fixture) => fixture,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };

    let output = Command::new(&targo_trust)
        .arg("lift")
        .arg(&fixture.path)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "targo trust lift should succeed for default-entry fixture\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}"));
    assert_eq!(json["status"], "ok");
    assert_eq!(json["format"], "ELF");
    assert_eq!(json["architecture"], fixture.architecture);
    assert_eq!(json["entry"], serde_json::Value::Null, "smoke test should exercise default entry");
    assert!(json["binary_entry"].as_str().is_some(), "report should expose parsed binary entry");
    assert_eq!(json["strict"], true);
    assert!(json["functions_lifted"].as_u64().unwrap_or(0) >= 1);
    assert!(json["vcs"].as_u64().unwrap_or(0) >= 1);
}

#[test]
fn test_targo_trust_verify_binary_json_accepts_ay_solver_route_without_proof_grade_claim() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("verify-binary")
        .arg(&elf_path)
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--solver")
        .arg("ay")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}"));

    assert_eq!(json["status"], "ok");
    assert_eq!(json["verification_status"], json["solver_results"]["status"]);
    assert_eq!(json["trust_level"], "partial");
    assert_ne!(json["trust_level"], "proof_grade");
    assert_eq!(json["selection"], "address");
    assert_eq!(json["entry"].as_str(), Some(entry_arg.as_str()));
    assert_eq!(json["strict"], true);
    assert_eq!(json["functions_analyzed"].as_u64(), Some(1));
    assert_eq!(json["unsupported"].as_u64(), Some(0));
    assert_eq!(json["failures"].as_u64(), Some(0));

    let vcs = json["vcs"].as_u64().expect("verify-binary JSON should include VC count");
    assert!(vcs >= 1, "verify-binary fixture should emit binary VCs: {json}");
    let solver_results = &json["solver_results"];
    let solver_status =
        solver_results["status"].as_str().expect("solver status should be a string");
    assert!(matches!(solver_status, "proved" | "failed" | "unknown" | "timeout" | "mixed"));
    let total = solver_results["total"].as_u64().expect("solver total should be numeric");
    let proved = solver_results["proved"].as_u64().expect("solver proved count should be numeric");
    let failed = solver_results["failed"].as_u64().expect("solver failed count should be numeric");
    let unknown =
        solver_results["unknown"].as_u64().expect("solver unknown count should be numeric");
    let timeout =
        solver_results["timeout"].as_u64().expect("solver timeout count should be numeric");
    assert_eq!(total, vcs, "every generated VC should have a ay-routed solver result");
    assert_eq!(total, proved + failed + unknown + timeout);

    let solver_items =
        json["solver_result_items"].as_array().expect("solver_result_items should be an array");
    assert_eq!(solver_items.len() as u64, total);
    assert!(
        solver_items.iter().all(|item| {
            let solver = item["solver"].as_str().unwrap_or_default();
            let vc_kind = item["vc_kind"].as_str().unwrap_or_default();
            solver.starts_with("ay-")
                || solver == "ay"
                || (solver == "router" && vc_kind.starts_with("unsupported_mir_"))
        }),
        "binary solver items should use the accepted ay route; unsupported MIR evidence may remain router-classified: {solver_items:?}"
    );
    assert!(
        solver_items.iter().all(|item| item["replay_status"].as_str() != Some("confirmed")),
        "verify-binary must not report confirmed replay without machine-code replay: {solver_items:?}"
    );
    assert!(
        solver_items.iter().all(|item| item["replay_detail"]
            .as_str()
            .is_none_or(|detail| !detail.contains("confirmed"))),
        "verify-binary replay detail must not claim confirmation: {solver_items:?}"
    );
    assert_source_backpropagation_gate_rejected(
        &json["source_backpropagation_gate"],
        "missing",
        "partial",
        "missing",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "verify-binary source backpropagation gate",
    );
    assert_checked_certificate_evidence_blocks_release(
        &json["checked_certificate_evidence"],
        "verify-binary checked-certificate evidence",
    );
    assert_eq!(json["proof_evidence"]["total_vcs"].as_u64(), Some(vcs));
    assert_eq!(
        json["proof_evidence"]["checked_certificate_coverage"]["missing_checked_certificates"]
            .as_u64(),
        Some(vcs)
    );
    assert_eq!(json["proof_grade_gate"]["replay_semantics_satisfied"], false);
    assert_optional_proof_gate_rejected(&json);

    let all_vcs_proved = solver_status == "proved" && total == vcs && proved == total;
    assert_eq!(
        output.status.success(),
        all_vcs_proved,
        "verify-binary should exit successfully only when every generated VC is proved\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn test_targo_trust_decompile_trust_ir_json_reports_partial_binary_only_shape() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("decompile")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust_ir")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "targo trust decompile --to trust_ir must fail closed while provenance/artifact-identity blockers remain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}"));
    assert_decompile_partial_trust_ir_shape(&json, &entry_arg);
    assert_eq!(json["target"], "trust_ir");
    assert_eq!(json["output_kind"], "trust_ir_json");
    assert_eq!(json["output_trust_level"], "partial");
    assert_ne!(json["output_trust_level"], "proof_grade");
    assert_eq!(json["output_validation"], "lifted_trust_ir_partial");
    assert_contains_all(
        json["validation_note"].as_str().expect("validation_note should be a string"),
        &["partial", "no verification summary"],
        "TrustIr validation note",
    );
    assert_source_backpropagation_gate_rejected(
        &json["artifact_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "decompile TrustIr source backpropagation gate",
    );
    assert_checked_certificate_evidence_blocks_release(
        &json["checked_certificate_readback"],
        "decompile TrustIr checked-certificate readback",
    );
    assert_optional_proof_gate_rejected(&json);

    let output_content =
        json["output_content"].as_str().expect("TrustIr JSON output_content should be a string");
    assert_trust_ir_target_proof_consumer_identity_accepted(
        &json,
        output_content,
        "decompile TrustIr target proof-consumer identity evidence",
    );
    let artifact: serde_json::Value = serde_json::from_str(output_content)
        .unwrap_or_else(|e| panic!("TrustIr output_content was not JSON: {e}\n{output_content}"));
    assert_decompile_release_gate_blocker_class_coverage(&json, &artifact, &entry_arg);
    assert_no_proof_grade_trust_fields(&artifact, "partial TrustIr output_content");
    assert_eq!(artifact["trust_level"], "Partial");
    assert_ne!(artifact["trust_level"], "ProofGrade");
    let expected_def_path = format!("binary::{FIXTURE_SYMBOL}");
    assert_eq!(
        artifact["functions"][0]["lifted"]["def_path"].as_str(),
        Some(expected_def_path.as_str())
    );
    assert_eq!(
        artifact["functions"][0]["verification"]["status"], "NotRun",
        "decompile TrustIr JSON must not imply proof validation"
    );
    assert_eq!(artifact["functions"][0]["verification"]["replay"], "NotAttempted");
    assert_eq!(artifact["functions"][0]["verification"]["proof_certificate"], "NotRequested");
    assert!(
        artifact["unsupported"]["records"].as_array().is_some_and(|records| !records.is_empty()),
        "partial TrustIr fixture should carry unsupported proof-grade blockers separately: {artifact}"
    );
    assert_binary_only_source_file_provenance(&artifact, "TrustIr output_content");
}

#[cfg(unix)]
#[test]
fn test_targo_trust_decompile_trust_ir_release_transcript_out_real_selected_slice_fails_closed() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create selected-slice release transcript fixture dir");
    let elf_path = materialize_hex_fixture(
        tmp.path(),
        "x86_64-load.elf",
        X86_64_LOAD_FIXTURE_HEX,
        X86_64_LOAD_FIXTURE_SHA256,
    )
    .unwrap_or_else(|reason| panic!("checked-in x86_64 load fixture should materialize: {reason}"));
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, X86_64_LOAD_FIXTURE_SYMBOL);
    assert_eq!(entry, X86_64_LOAD_FIXTURE_ENTRY);
    let entry_arg = format!("0x{entry:x}");
    let (manifest_path, replay_transcript_digest) =
        build_selected_slice_checked_certificate_manifest(
            tmp.path(),
            &elf_path,
            &bytes,
            entry,
            "selected-slice-release-transcript:vc0",
        )
        .unwrap_or_else(|reason| {
            panic!("selected-slice checked-certificate manifest should build: {reason}")
        });
    let transcript_path = tmp.path().join("proof-grade-release-transcript.json");

    let output = Command::new(&targo_trust)
        .arg("decompile")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust_ir")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--checked-cert-manifest")
        .arg(&manifest_path)
        .arg("--proof-grade-release-transcript-out")
        .arg(&transcript_path)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "release transcript artifact writer must fail closed until every selected-slice proof-grade prerequisite is real and accepted\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !transcript_path.exists(),
        "blocked proof-grade release transcript must not be materialized at {}",
        transcript_path.display()
    );
    assert_contains_all(
        &stderr,
        &[
            "proof_grade_release_transcript_rejected",
            "proof-grade release transcript artifact rejected",
        ],
        "release transcript stderr diagnostic",
    );

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!("decompile stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}")
    });
    assert_eq!(json["target"], "trust_ir");
    assert_eq!(json["functions_decompiled"].as_u64(), Some(1));
    assert_eq!(json["output_trust_level"], "partial");
    assert_ne!(json["output_trust_level"], "proof_grade");
    assert_eq!(json["checked_certificate_readback"]["loader"]["status"], "loaded");
    assert_eq!(
        json["checked_certificate_readback"]["loader"]["requested_manifests"].as_u64(),
        Some(1)
    );
    assert_eq!(
        json["checked_certificate_readback"]["checked_certificate_readback_rows"].as_u64(),
        Some(1)
    );
    assert_eq!(
        json["checked_certificate_readback"]["production_checker_evidence_rows"].as_u64(),
        Some(1)
    );

    let record = &json["checked_certificate_readback"]["readback_records"][0];
    assert_eq!(record["status"], "readback");
    assert_eq!(record["production_checked"], true);
    assert_eq!(record["replay"], "replayed");
    assert_eq!(
        record["replay_transcript_digest"].as_str(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(record["release_transcript_binding"]["status"], "accepted");
    assert_eq!(
        record["release_transcript_binding"]["binary_sha256"].as_str(),
        Some(X86_64_LOAD_FIXTURE_SHA256)
    );
    assert_eq!(
        record["release_transcript_binding"]["selected_image_sha256"].as_str(),
        Some(X86_64_LOAD_FIXTURE_SHA256)
    );
    assert_eq!(record["release_transcript_binding"]["selected_image_file_offset"], 0);
    assert_eq!(
        record["release_transcript_binding"]["selected_image_file_size"].as_u64(),
        Some(bytes.len() as u64)
    );
    assert_eq!(
        record["release_transcript_binding"]["replay_transcript_sha256"].as_str(),
        Some(replay_transcript_digest.as_str())
    );

    let transcript = &json["proof_grade_release_transcript"];
    assert_eq!(
        transcript["accepted_proof_grade_rows"]
            .as_array()
            .expect("accepted transcript rows should be an array")
            .len(),
        0
    );
    let blocked_rows = transcript["blocked_proof_grade_rows"]
        .as_array()
        .expect("blocked transcript rows should be an array");
    assert_eq!(blocked_rows.len(), 1);
    let row = &blocked_rows[0];
    assert_eq!(row["accepted"], false);
    assert_eq!(row["status"], "blocked");
    assert_eq!(row["evidence_origin"], "targo_trust_checked_certificate_readback");
    let expected_binary_digest = format!("sha256:{X86_64_LOAD_FIXTURE_SHA256}");
    let expected_selected_image_identity = format!("file_offset=0:file_size={}", bytes.len());
    let expected_replay_transcript_digest = format!("sha256:{replay_transcript_digest}");
    assert_eq!(row["binary_digest"].as_str(), Some(expected_binary_digest.as_str()));
    assert_eq!(
        row["selected_image"]["identity"].as_str(),
        Some(expected_selected_image_identity.as_str())
    );
    assert_eq!(row["selected_image"]["digest"].as_str(), Some(expected_binary_digest.as_str()));
    assert_eq!(
        row["replay_transcript_digests"][0].as_str(),
        Some(expected_replay_transcript_digest.as_str())
    );
    let row_blockers = row["blockers"]
        .as_array()
        .expect("blocked transcript row should include blockers")
        .iter()
        .map(|blocker| blocker.as_str().expect("row blocker should be a string"))
        .collect::<Vec<_>>()
        .join("\n");
    assert_contains_all(
        &row_blockers,
        &[
            "evidence_origin must be `targo_trust_release_export`",
            "unsupported_ledgers_empty must be true",
            "exact_source_ownership_evidence.digest is missing",
            "type_ownership_evidence.digest is missing",
            "release_transcript_binding_digest cannot be computed",
        ],
        "blocked selected-slice transcript row",
    );
}

#[cfg(unix)]
#[test]
fn test_targo_trust_convert_trust_cg_release_transcript_attempt_assembles_selected_slice_bundle() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create selected-slice release transcript fixture dir");
    let elf_path = materialize_hex_fixture(
        tmp.path(),
        "x86_64-load.elf",
        X86_64_LOAD_FIXTURE_HEX,
        X86_64_LOAD_FIXTURE_SHA256,
    )
    .unwrap_or_else(|reason| panic!("checked-in x86_64 load fixture should materialize: {reason}"));
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, X86_64_LOAD_FIXTURE_SYMBOL);
    assert_eq!(entry, X86_64_LOAD_FIXTURE_ENTRY);
    let entry_arg = format!("0x{entry:x}");
    let (manifest_path, replay_transcript_digest) =
        build_selected_slice_checked_certificate_manifest(
            tmp.path(),
            &elf_path,
            &bytes,
            entry,
            "selected-slice-trust_cg-release-transcript:vc0",
        )
        .unwrap_or_else(|reason| {
            panic!("selected-slice checked-certificate manifest should build: {reason}")
        });
    let transcript_path = tmp.path().join("proof-grade-release-transcript.json");

    let output = Command::new(&targo_trust)
        .arg("convert")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--checked-cert-manifest")
        .arg(&manifest_path)
        .arg("--proof-grade-release-transcript-out")
        .arg(&transcript_path)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "trust-cg selected-slice release transcript must fail closed until the full proof-grade bundle is present\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !transcript_path.exists(),
        "blocked proof-grade release transcript must not be materialized at {}",
        transcript_path.display()
    );
    assert_contains_all(
        &stderr,
        &[
            "proof_grade_release_transcript_rejected",
            "proof-grade release transcript artifact rejected",
        ],
        "trust-cg release transcript stderr diagnostic",
    );

    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!("convert stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}")
    });
    assert_eq!(json["target"], "trust-cg");
    assert_eq!(json["checked_certificate_readback"]["loader"]["status"], "loaded");
    assert_eq!(
        json["checked_certificate_readback"]["checked_certificate_readback_rows"].as_u64(),
        Some(1)
    );
    assert_eq!(
        json["checked_certificate_readback"]["production_checker_evidence_rows"].as_u64(),
        Some(1)
    );

    let record = &json["checked_certificate_readback"]["readback_records"][0];
    assert_eq!(record["status"], "readback");
    assert_eq!(record["production_checked"], true);
    assert_eq!(record["replay"], "replayed");
    assert_eq!(
        record["replay_transcript_digest"].as_str(),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(record["release_transcript_binding"]["status"], "rejected");
    assert_json_string_items_contain_all(
        record["release_transcript_binding"]["blockers"]
            .as_array()
            .expect("release transcript binding blockers should be an array"),
        &["target-consumer binding digest is missing"],
        "selected-slice trust_cg release transcript binding blockers",
    );
    assert_eq!(
        record["release_transcript_binding"]["binary_sha256"].as_str(),
        Some(X86_64_LOAD_FIXTURE_SHA256)
    );
    assert_eq!(
        record["release_transcript_binding"]["selected_image_sha256"].as_str(),
        Some(X86_64_LOAD_FIXTURE_SHA256)
    );
    assert_eq!(record["release_transcript_binding"]["selected_image_file_offset"], 0);
    assert_eq!(
        record["release_transcript_binding"]["selected_image_file_size"].as_u64(),
        Some(bytes.len() as u64)
    );
    assert_eq!(
        record["release_transcript_binding"]["replay_transcript_sha256"].as_str(),
        Some(replay_transcript_digest.as_str())
    );

    let target_consumer = &json["target_proof_consumer_evidence"];
    assert_eq!(target_consumer["target"], "trust-cg");
    assert_eq!(target_consumer["status"], "rejected");
    assert_eq!(target_consumer["target_semantics_consumed"], false);
    let target_consumer_blocker_codes = target_consumer["blockers"]
        .as_array()
        .expect("target proof-consumer blockers should be an array")
        .iter()
        .map(|blocker| blocker["code"].as_str().expect("blocker code should be a string"))
        .collect::<Vec<_>>();
    let unique_blocker_codes: std::collections::BTreeSet<&str> =
        target_consumer_blocker_codes.iter().copied().collect();
    let expected_codes: std::collections::BTreeSet<&str> = [
        "target-semantics-not-consumed",
        "symbolic-formula-not-consumed-by-target-semantics",
        "checked-certificate-not-consumed-by-target-semantics",
        "proof-replay-not-consumed-by-target-semantics",
    ]
    .into_iter()
    .collect();
    assert_eq!(
        unique_blocker_codes,
        expected_codes,
        "trust-cg selected-slice target proof-consumer evidence should reject only the unconsumed real evidence (one blocker entry per preserved formula is permitted): {target_consumer_blocker_codes:?}"
    );
    let target_consumer_records = target_consumer["records"]
        .as_array()
        .expect("target proof-consumer records should be an array");
    assert_json_record_kinds_rejected(
        target_consumer_records,
        &["target_semantics", "symbolic_formula", "checked_certificate", "proof_replay"],
        "trust-cg selected-slice target proof-consumer evidence",
    );
    assert_eq!(
        json["conversion_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"]
    );

    let transcript = &json["proof_grade_release_transcript"];
    assert_eq!(
        transcript["accepted_proof_grade_rows"]
            .as_array()
            .expect("accepted transcript rows should be an array")
            .len(),
        0
    );
    let blocked_rows = transcript["blocked_proof_grade_rows"]
        .as_array()
        .expect("blocked transcript rows should be an array");
    assert_eq!(blocked_rows.len(), 1);
    let row = &blocked_rows[0];
    assert_eq!(row["accepted"], false);
    assert_eq!(row["status"], "blocked");
    assert_eq!(row["evidence_origin"], "targo_trust_checked_certificate_readback");

    let expected_binary_digest = format!("sha256:{X86_64_LOAD_FIXTURE_SHA256}");
    let expected_selected_image_identity = format!("file_offset=0:file_size={}", bytes.len());
    let expected_replay_transcript_digest = format!("sha256:{replay_transcript_digest}");
    assert_eq!(row["binary_digest"].as_str(), Some(expected_binary_digest.as_str()));
    assert_eq!(
        row["selected_image"]["identity"].as_str(),
        Some(expected_selected_image_identity.as_str())
    );
    assert_eq!(row["selected_image"]["digest"].as_str(), Some(expected_binary_digest.as_str()));
    assert_eq!(
        row["replay_transcript_digests"][0].as_str(),
        Some(expected_replay_transcript_digest.as_str())
    );
    assert_eq!(row["unsupported_ledgers_empty"], false);
    assert_eq!(row["exact_source_ownership_evidence"]["status"], "missing");
    assert_eq!(row["type_ownership_evidence"]["status"], "missing");
    let target_digests = row["target_proof_consumer_artifact_digests"]
        .as_array()
        .expect("target proof-consumer digest list should be present");
    assert_eq!(target_digests.len(), 1, "rejected trust_cg target evidence should still be bound");
    assert_json_canonical_digest_uri(
        &target_digests[0],
        "selected-slice target proof-consumer evidence digest",
    );

    let row_blockers = row["blockers"]
        .as_array()
        .expect("blocked transcript row should include blockers")
        .iter()
        .map(|blocker| blocker.as_str().expect("row blocker should be a string").to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        row_blockers,
        vec![
            "evidence_origin must be `targo_trust_release_export` for accepted proof-grade release transcript rows".to_string(),
            "unsupported_ledgers_empty must be true".to_string(),
            "target proof-consumer binding digest is missing".to_string(),
            "exact_source_ownership_evidence.digest is missing".to_string(),
            "type_ownership_evidence.digest is missing".to_string(),
            "release_transcript_binding_digest cannot be computed until all trust.proof-grade-row-binding.v1 inputs are accepted".to_string(),
        ],
        "blocked selected-slice trust_cg transcript row should name exactly the missing real evidence"
    );
}

#[test]
fn test_targo_trust_decompile_rust_json_reports_exploratory_text_only_shape() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("decompile")
        .arg(&elf_path)
        .arg("--to")
        .arg("rust")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "targo trust decompile --to rust must fail closed while provenance/artifact-identity blockers remain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}"));
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["format"], "ELF");
    assert_eq!(json["architecture"], "x86-64");
    assert_eq!(json["selection"], "address");
    assert_eq!(json["entry"].as_str(), Some(entry_arg.as_str()));
    assert_eq!(json["binary_entry"].as_str(), Some("0x0"));
    assert_eq!(json["strict"], true);
    assert_eq!(json["functions_decompiled"].as_u64(), Some(1));
    assert_eq!(json["blocks"].as_u64(), Some(1));
    assert_eq!(json["instructions"].as_u64(), Some(1));
    assert!(json["statements"].as_u64().unwrap_or(0) >= 1);
    assert!(json["memory_facts"].as_u64().unwrap_or(0) >= 1);
    assert!(json["unsupported"].as_u64().unwrap_or(0) > 0);
    assert_eq!(json["failures"].as_u64(), Some(0));
    assert_eq!(json["target"], "rust");
    assert_eq!(json["output_kind"], "rust_skeleton");
    assert_eq!(json["output_trust_level"], "exploratory");
    assert_ne!(json["output_trust_level"], "proof_grade");
    assert_eq!(json["output_validation"], "exploratory_not_validated");
    assert_contains_all(
        json["validation_note"].as_str().expect("validation_note should be a string"),
        &["exploratory/not validated", "no reconstruction validation"],
        "Rust skeleton validation note",
    );
    assert_optional_proof_gate_rejected(&json);

    let output_content =
        json["output_content"].as_str().expect("Rust skeleton output_content should be text");
    assert!(
        serde_json::from_str::<serde_json::Value>(output_content).is_err(),
        "Rust skeleton output_content should be text, not embedded JSON"
    );
    assert!(
        !output_content.contains("proof_grade"),
        "exploratory Rust skeleton must not claim proof_grade: {output_content}"
    );
    assert_contains_all(
        output_content,
        &[
            "Exploratory partial Rust skeleton",
            "not validated Rust reconstruction",
            "Binary: format=ELF arch=x86-64",
            "unsupported_records=",
            FIXTURE_SYMBOL,
            "todo!(\"exploratory decompilation skeleton",
        ],
        "Rust skeleton output_content",
    );
    assert_text_has_no_source_file_mapping(output_content, "Rust skeleton output_content");
}

#[test]
fn test_targo_trust_convert_trust_cg_json_reports_inspectable_rejected_gate() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("convert")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "convert --to trust_cg must reject non-proof-grade output while still emitting JSON\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}"));
    assert_eq!(json["target"], "trust-cg");
    assert_eq!(json["output_kind"], "trust_cg_text");
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["output_validation"], "inspectable_rejected");
    assert_eq!(json["conversion_gate"]["accepted"], false);
    assert_eq!(json["conversion_gate"]["status"], "rejected");
    assert_eq!(json["conversion_gate"]["validation"], "inspectable_rejected");
    assert_eq!(json["conversion_gate"]["proof_grade_artifact"], false);
    assert_source_backpropagation_gate_rejected(
        &json["conversion_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "convert trust_cg source backpropagation gate",
    );
    assert_checked_certificate_evidence_blocks_release(
        &json["checked_certificate_readback"],
        "convert trust_cg checked-certificate readback",
    );
    assert_eq!(
        json["conversion_gate"]["checked_certificate_evidence"],
        json["checked_certificate_readback"]
    );
    assert_target_proof_consumer_evidence_rejected(
        &json["target_proof_consumer_evidence"],
        "trust-cg",
        "convert trust_cg target proof-consumer evidence",
    );
    assert_eq!(
        json["conversion_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"]
    );
    assert!(
        json["output_content"].as_str().is_some_and(|content| {
            content.contains("\"status\": \"inspectable_rejected\"")
                && content.contains("\"trust_level\": \"rejected\"")
        }),
        "inspectable trust_cg output should be present and explicitly rejected: {json}"
    );
    assert!(
        json["target_validation_blockers"].as_array().is_some_and(|items| !items.is_empty()),
        "trust-cg conversion must surface target validation blockers: {json}"
    );
    assert!(
        json["unsupported_items"].as_array().expect("unsupported_items").iter().any(|item| item
            .as_str()
            .is_some_and(|text| text.contains("non-exact source provenance"))),
        "non-exact provenance should remain an explicit proof-grade blocker: {json}"
    );
    assert!(
        json["unsupported_items"]
            .as_array()
            .expect("unsupported_items")
            .iter()
            .all(|item| !item.as_str().unwrap_or_default().contains("trust-cg conversion rejected")),
        "provenance blockers must not be reclassified as trust_cg translation rejection: {json}"
    );
    assert_no_proof_grade_release_claim(&json, "convert trust_cg inspectable rejected");
}

#[test]
fn test_targo_trust_convert_trust_cg_rejects_after_partial_trust_ir_decompile_success() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp fixture dir");
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let decompile_output = Command::new(&targo_trust)
        .arg("decompile")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust_ir")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));
    let decompile_stdout = String::from_utf8_lossy(&decompile_output.stdout);
    let decompile_stderr = String::from_utf8_lossy(&decompile_output.stderr);
    assert!(
        decompile_output.status.success(),
        "partial TrustIr decompile should be inspectable with --allow-unsupported\nstdout:\n{decompile_stdout}\nstderr:\n{decompile_stderr}"
    );
    let decompile_json: serde_json::Value = serde_json::from_str(&decompile_stdout)
        .unwrap_or_else(|e| {
            panic!("decompile stdout was not JSON: {e}\n{decompile_stdout}\nstderr:\n{decompile_stderr}")
        });
    assert_eq!(decompile_json["target"], "trust_ir");
    assert_eq!(decompile_json["strict"], false);
    assert_eq!(decompile_json["status"], "incomplete");
    assert_eq!(decompile_json["output_trust_level"], "partial");
    assert_eq!(decompile_json["functions_decompiled"].as_u64(), Some(1));
    assert_eq!(decompile_json["failures"].as_u64(), Some(0));
    assert!(
        decompile_json["unsupported"].as_u64().unwrap_or(0) > 0,
        "partial TrustIr decompile should expose proof-grade blockers: {decompile_json}"
    );
    assert_source_backpropagation_gate_rejected(
        &decompile_json["artifact_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "pre-convert partial TrustIr source backpropagation gate",
    );
    let decompile_output_content = decompile_json["output_content"]
        .as_str()
        .expect("partial TrustIr output_content should be present");
    let decompile_artifact: serde_json::Value = serde_json::from_str(decompile_output_content)
        .unwrap_or_else(|e| panic!("decompile TrustIr output_content was not JSON: {e}"));
    assert_decompile_release_gate_blocker_class_coverage(
        &decompile_json,
        &decompile_artifact,
        &entry_arg,
    );

    let convert_output = Command::new(&targo_trust)
        .arg("convert")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let convert_stdout = String::from_utf8_lossy(&convert_output.stdout);
    let convert_stderr = String::from_utf8_lossy(&convert_output.stderr);
    assert!(
        !convert_output.status.success(),
        "convert --to trust_cg must still fail closed after partial TrustIr decompile success\nstdout:\n{convert_stdout}\nstderr:\n{convert_stderr}"
    );
    let json: serde_json::Value = serde_json::from_str(&convert_stdout).unwrap_or_else(|e| {
        panic!("convert stdout was not JSON: {e}\n{convert_stdout}\nstderr:\n{convert_stderr}")
    });

    assert_eq!(json["target"], "trust-cg");
    assert_eq!(json["strict"], false);
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["functions_decompiled"].as_u64(), Some(1));
    assert_eq!(json["failures"].as_u64(), Some(0));
    assert_eq!(json["output_kind"], "trust_cg_text");
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["output_validation"], "inspectable_rejected");
    assert_eq!(json["conversion_gate"]["accepted"], false);
    assert_eq!(json["conversion_gate"]["status"], "rejected");
    assert_eq!(json["conversion_gate"]["proof_grade_artifact"], false);
    assert!(
        json["unsupported"].as_u64().unwrap_or(0) > 0,
        "unsupported ledger must remain visible until eliminated: {json}"
    );
    assert!(
        json["target_validation_blockers"].as_array().is_some_and(|items| !items.is_empty()),
        "trust-cg target validation blockers must be visible after successful decompile: {json}"
    );

    assert_source_backpropagation_gate_rejected(
        &json["conversion_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "convert trust_cg post-decompile source backpropagation gate",
    );
    assert_convert_checked_certificate_preconditions_rejected(
        &json["checked_certificate_readback"],
        "convert trust_cg checked-certificate release preconditions",
    );
    assert_eq!(
        json["conversion_gate"]["checked_certificate_evidence"],
        json["checked_certificate_readback"]
    );
    assert_target_proof_consumer_evidence_rejected(
        &json["target_proof_consumer_evidence"],
        "trust-cg",
        "convert trust_cg post-decompile target proof-consumer evidence",
    );
    assert_eq!(
        json["conversion_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"]
    );
    assert_convert_release_gate_blocker_class_coverage(&json, &entry_arg);
    assert_json_string_items_contain_all(
        json["conversion_gate"]["blockers"]
            .as_array()
            .expect("conversion gate blockers should be an array"),
        &[
            "output trust is `rejected`",
            "output validation is `inspectable_rejected`",
            "unsupported conversion/lift coverage remains",
        ],
        "convert trust_cg release gate blockers",
    );
    assert_no_proof_grade_release_claim(&json, "convert trust_cg rejected after partial TrustIr");
}

#[test]
fn test_checked_in_x86_64_load_decompile_canonical_trust_ir_then_convert_trust_cg_golden_blockers() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create checked-in x86_64 load fixture dir");
    let elf_path = materialize_hex_fixture(
        tmp.path(),
        "x86_64-load.elf",
        X86_64_LOAD_FIXTURE_HEX,
        X86_64_LOAD_FIXTURE_SHA256,
    )
    .unwrap_or_else(|reason| panic!("checked-in x86_64 load fixture should materialize: {reason}"));
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, X86_64_LOAD_FIXTURE_SYMBOL);
    assert_eq!(entry, X86_64_LOAD_FIXTURE_ENTRY);
    let entry_arg = format!("0x{entry:x}");

    let decompile_output = Command::new(&targo_trust)
        .arg("decompile")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust_ir")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));
    let decompile_stdout = String::from_utf8_lossy(&decompile_output.stdout);
    let decompile_stderr = String::from_utf8_lossy(&decompile_output.stderr);
    assert!(
        decompile_output.status.success(),
        "checked-in x86_64 load fixture should decompile to canonical partial TrustIr\nstdout:\n{decompile_stdout}\nstderr:\n{decompile_stderr}"
    );
    let decompile_json: serde_json::Value =
        serde_json::from_str(&decompile_stdout).unwrap_or_else(|e| {
            panic!(
                "decompile stdout was not JSON: {e}\n{decompile_stdout}\nstderr:\n{decompile_stderr}"
            )
        });

    let convert_output = Command::new(&targo_trust)
        .arg("convert")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));
    let convert_stdout = String::from_utf8_lossy(&convert_output.stdout);
    let convert_stderr = String::from_utf8_lossy(&convert_output.stderr);
    assert!(
        !convert_output.status.success(),
        "convert --to trust_cg must fail closed after canonical TrustIr decompile while still emitting JSON\nstdout:\n{convert_stdout}\nstderr:\n{convert_stderr}"
    );
    let convert_json: serde_json::Value =
        serde_json::from_str(&convert_stdout).unwrap_or_else(|e| {
            panic!("convert stdout was not JSON: {e}\n{convert_stdout}\nstderr:\n{convert_stderr}")
        });

    let expected: serde_json::Value =
        serde_json::from_str(PRODUCTION_POSITIVE_X86_64_LOAD_TRUST_CG_GOLDEN)
            .expect("production-positive x86_64 load trust_cg golden should parse");
    let observed = production_positive_x86_64_load_trust_cg_golden_projection(
        &decompile_json,
        &convert_json,
        X86_64_LOAD_FIXTURE_SHA256,
    );
    // To regenerate this golden when production output drifts intentionally, set
    // `TRUST_GOLDEN_REGENERATE=<path>` and rerun this test once; it will overwrite the
    // file pointed at by that env var.
    if let Ok(write_to) = std::env::var("TRUST_GOLDEN_REGENERATE") {
        let pretty = serde_json::to_string_pretty(&observed)
            .expect("observed projection should serialize");
        std::fs::write(&write_to, format!("{pretty}\n"))
            .unwrap_or_else(|e| panic!("could not write regenerated golden to {write_to}: {e}"));
        eprintln!("REGENERATED GOLDEN: {write_to}");
    }
    assert_production_positive_release_gate_scaffold_rejected(
        &observed["convert_trust_cg"]["positive_release_gate_scaffold"],
        "checked-in x86_64 load trust_cg positive release-gate scaffold",
    );
    assert_eq!(observed, expected);

    assert_no_proof_grade_release_claim(
        &decompile_json,
        "checked-in x86_64 load canonical TrustIr decompile",
    );
    assert_no_proof_grade_release_claim(
        &convert_json,
        "checked-in x86_64 load trust_cg conversion blockers",
    );
}

#[test]
fn test_targo_trust_convert_trust_cg_keeps_source_backprop_rejected_with_checked_cert_readback() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create checked-certificate readback fixture dir");
    let cert_dispatch_id = "source-backprop-readback:vc0";
    let cert_path = match build_checked_certificate_readback_fixture(tmp.path(), cert_dispatch_id) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let elf_path = match build_x86_64_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("convert")
        .arg(&elf_path)
        .arg("--to")
        .arg("trust-cg")
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--allow-unsupported")
        .arg("--checked-cert-artifact")
        .arg(&cert_path)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "convert --to trust_cg must still reject source-backprop/rewrite authority when checked-certificate readback is present\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!("convert stdout was not JSON: {e}\n{stdout}\nstderr:\n{stderr}")
    });

    assert_eq!(json["target"], "trust-cg");
    assert_eq!(json["strict"], false);
    assert_eq!(json["output_trust_level"], "rejected");
    assert_eq!(json["conversion_gate"]["accepted"], false);
    assert_eq!(json["conversion_gate"]["status"], "rejected");
    assert_source_backpropagation_gate_rejected(
        &json["conversion_gate"]["source_backpropagation_gate"],
        "missing",
        "missing",
        "partial",
        &[
            "exact-source-provenance-missing",
            "proof-grade-binary-verification-missing",
            "accepted-reconstruction-target-validation-missing",
        ],
        "convert trust_cg checked-certificate readback source backpropagation gate",
    );
    assert_checked_certificate_readback_keeps_source_backprop_closed(
        &json["checked_certificate_readback"],
        cert_dispatch_id,
        "convert trust_cg checked-certificate readback source-backprop rejection",
    );
    assert_eq!(
        json["conversion_gate"]["checked_certificate_evidence"],
        json["checked_certificate_readback"]
    );
    assert_eq!(json["target_proof_consumer_evidence"]["target"], "trust-cg");
    assert_eq!(json["target_proof_consumer_evidence"]["status"], "rejected");
    assert_eq!(json["target_proof_consumer_evidence"]["target_semantics_consumed"], false);
    assert_eq!(
        json["conversion_gate"]["target_proof_consumer_evidence"],
        json["target_proof_consumer_evidence"]
    );
    assert_no_proof_grade_release_claim(&json, "convert trust_cg checked-cert readback");
}

#[test]
fn test_targo_trust_verify_binary_json_release_gate_rejects_unliftable_fixtures() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    for case in fail_closed_fixture_cases() {
        for allow_unsupported in [false, true] {
            let tmp = tempfile::tempdir()
                .unwrap_or_else(|e| panic!("create temp {} fixture dir: {e}", case.label));
            let elf_path = match (case.build)(tmp.path()) {
                Ok(path) => path,
                Err(reason) => {
                    eprintln!("SKIP: {reason}");
                    return;
                }
            };
            let bytes = read_checked_x86_64_elf_fixture(&elf_path);
            let entry = function_entry_for_symbol(&bytes, case.symbol);
            let entry_arg = format!("0x{entry:x}");

            let mut command = Command::new(&targo_trust);
            command
                .arg("verify-binary")
                .arg(&elf_path)
                .arg("--entry")
                .arg(&entry_arg)
                .arg("--solver")
                .arg("ay")
                .arg("--json");
            if allow_unsupported {
                command.arg("--allow-unsupported");
            }
            let output = command
                .output()
                .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success(),
                "verify-binary release gate must fail for {} fixture with allow_unsupported={allow_unsupported}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                case.label
            );

            let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
                panic!("stdout was not JSON for {} fixture: {e}\n{stdout}", case.label)
            });
            assert_verify_binary_fail_closed_json(&json, &entry_arg, case, allow_unsupported);
        }
    }
}

#[test]
fn test_targo_trust_decompile_trust_ir_json_release_gate_rejects_unliftable_fixtures() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    for case in fail_closed_fixture_cases() {
        for allow_unsupported in [false, true] {
            let tmp = tempfile::tempdir()
                .unwrap_or_else(|e| panic!("create temp {} fixture dir: {e}", case.label));
            let elf_path = match (case.build)(tmp.path()) {
                Ok(path) => path,
                Err(reason) => {
                    eprintln!("SKIP: {reason}");
                    return;
                }
            };
            let bytes = read_checked_x86_64_elf_fixture(&elf_path);
            let entry = function_entry_for_symbol(&bytes, case.symbol);
            let entry_arg = format!("0x{entry:x}");

            let mut command = Command::new(&targo_trust);
            command
                .arg("decompile")
                .arg(&elf_path)
                .arg("--to")
                .arg("trust_ir")
                .arg("--entry")
                .arg(&entry_arg)
                .arg("--json");
            if allow_unsupported {
                command.arg("--allow-unsupported");
            }
            let output = command
                .output()
                .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success(),
                "decompile release gate must fail for {} fixture with allow_unsupported={allow_unsupported}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                case.label
            );

            let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
                panic!("stdout was not JSON for {} fixture: {e}\n{stdout}", case.label)
            });
            assert_decompile_trust_ir_fail_closed_json(&json, &entry_arg, case, allow_unsupported);
        }
    }
}

#[test]
fn test_targo_trust_decompile_rust_json_rejects_unliftable_strict_fixtures() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    for case in fail_closed_fixture_cases() {
        let tmp = tempfile::tempdir()
            .unwrap_or_else(|e| panic!("create temp {} fixture dir: {e}", case.label));
        let elf_path = match (case.build)(tmp.path()) {
            Ok(path) => path,
            Err(reason) => {
                eprintln!("SKIP: {reason}");
                return;
            }
        };
        let bytes = read_checked_x86_64_elf_fixture(&elf_path);
        let entry = function_entry_for_symbol(&bytes, case.symbol);
        let entry_arg = format!("0x{entry:x}");

        let output = Command::new(&targo_trust)
            .arg("decompile")
            .arg(&elf_path)
            .arg("--to")
            .arg("rust")
            .arg("--entry")
            .arg(&entry_arg)
            .arg("--json")
            .output()
            .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "strict decompile --to rust must reject {} fixture\nstdout:\n{stdout}\nstderr:\n{stderr}",
            case.label
        );

        let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
            panic!("stdout was not JSON for {} fixture: {e}\n{stdout}", case.label)
        });
        assert_decompile_rust_fail_closed_json(&json, &entry_arg, case);
    }
}

fn assert_verify_binary_fail_closed_json(
    json: &serde_json::Value,
    entry_arg: &str,
    case: FailClosedFixtureCase,
    allow_unsupported: bool,
) {
    let context =
        format!("verify-binary {} fixture allow_unsupported={allow_unsupported}", case.label);
    assert_eq!(json["selection"], "address");
    assert_eq!(json["entry"].as_str(), Some(entry_arg));
    assert_eq!(json["strict"].as_bool(), Some(!allow_unsupported));
    assert_eq!(json["status"], "incomplete", "{context}");
    assert_eq!(json["verification_status"], "not_run", "{context}");
    assert_eq!(json["trust_level"], "partial", "{context}");
    assert_eq!(json["functions_analyzed"].as_u64(), Some(0), "{context}");
    assert_eq!(json["blocks"].as_u64(), Some(0), "{context}");
    assert_eq!(json["statements"].as_u64(), Some(0), "{context}");
    assert_eq!(json["vcs"].as_u64(), Some(0), "{context}");
    assert_eq!(json["solver_results"]["status"], "not_run", "{context}");
    assert_eq!(json["solver_results"]["total"].as_u64(), Some(0), "{context}");
    assert_eq!(json["solver_results"]["proved"].as_u64(), Some(0), "{context}");
    assert_eq!(json["solver_results"]["failed"].as_u64(), Some(0), "{context}");
    assert_eq!(json["solver_results"]["unknown"].as_u64(), Some(0), "{context}");
    assert_eq!(json["solver_results"]["timeout"].as_u64(), Some(0), "{context}");
    assert!(
        json["solver_result_items"].as_array().is_some_and(Vec::is_empty),
        "{context} must not dispatch solver work after an unliftable fixture: {json}"
    );
    assert!(json["unsupported"].as_u64().unwrap_or(0) >= 1, "{context}");
    assert_eq!(json["failures"].as_u64(), Some(0), "{context}");
    assert!(
        json["failure_items"].as_array().is_some_and(Vec::is_empty),
        "{context} should classify these as unsupported coverage, not generic failures: {json}"
    );
    let unsupported_items =
        json["unsupported_items"].as_array().expect("unsupported_items should be an array");
    assert_json_string_items_contain_all(
        unsupported_items,
        case.expected_fragments,
        context.as_str(),
    );
    assert_no_proof_grade_release_claim(json, context.as_str());
    assert_optional_proof_gate_rejected(json);
}

fn assert_decompile_trust_ir_fail_closed_json(
    json: &serde_json::Value,
    entry_arg: &str,
    case: FailClosedFixtureCase,
    allow_unsupported: bool,
) {
    let context =
        format!("decompile trust_ir {} fixture allow_unsupported={allow_unsupported}", case.label);
    assert_eq!(json["target"], "trust_ir", "{context}");
    assert_eq!(json["selection"], "address", "{context}");
    assert_eq!(json["entry"].as_str(), Some(entry_arg), "{context}");
    assert_eq!(json["strict"].as_bool(), Some(!allow_unsupported), "{context}");
    assert_eq!(json["status"], "incomplete", "{context}");
    assert_eq!(json["functions_decompiled"].as_u64(), Some(0), "{context}");
    assert_eq!(json["blocks"].as_u64(), Some(0), "{context}");
    assert_eq!(json["instructions"].as_u64(), Some(0), "{context}");
    assert_eq!(json["statements"].as_u64(), Some(0), "{context}");
    assert_eq!(json["memory_facts"].as_u64(), Some(0), "{context}");
    assert!(json["unsupported"].as_u64().unwrap_or(0) >= 1, "{context}");
    assert_eq!(json["failures"].as_u64(), Some(0), "{context}");
    assert!(
        json["failure_items"].as_array().is_some_and(Vec::is_empty),
        "{context} should classify these as unsupported coverage, not generic failures: {json}"
    );
    let unsupported_items =
        json["unsupported_items"].as_array().expect("unsupported_items should be an array");
    assert_json_string_items_contain_all(
        unsupported_items,
        case.expected_fragments,
        context.as_str(),
    );

    if allow_unsupported {
        assert_eq!(json["format"], "ELF", "{context}");
        assert_eq!(json["architecture"], "x86-64", "{context}");
        assert_eq!(json["output_kind"], "trust_ir_json", "{context}");
        assert_eq!(json["output_trust_level"], "partial", "{context}");
        assert_eq!(json["output_validation"], "lifted_trust_ir_partial", "{context}");
        let output_content =
            json["output_content"].as_str().expect("TrustIr output_content should be present");
        let artifact: serde_json::Value = serde_json::from_str(output_content)
            .unwrap_or_else(|e| panic!("{context} output_content was not JSON: {e}"));
        assert_eq!(artifact["functions"].as_array().map(Vec::len), Some(0), "{context}");
        assert_eq!(artifact["trust_level"], "Partial", "{context}");
        assert!(
            artifact["unsupported"]["records"]
                .as_array()
                .is_some_and(|records| !records.is_empty()),
            "{context} must carry unsupported ledger records in the partial artifact: {artifact}"
        );
    } else {
        assert_eq!(json["format"], "ELF", "{context}");
        assert_eq!(json["architecture"], "x86-64", "{context}");
        assert_eq!(json["output_kind"], serde_json::Value::Null, "{context}");
        assert_eq!(json["output_trust_level"], "rejected", "{context}");
        assert_eq!(json["output_validation"], "artifact_not_produced", "{context}");
        assert_eq!(json["output_content"], serde_json::Value::Null, "{context}");
    }

    assert_no_proof_grade_release_claim(json, context.as_str());
    assert_optional_proof_gate_rejected(json);
}

fn assert_decompile_rust_fail_closed_json(
    json: &serde_json::Value,
    entry_arg: &str,
    case: FailClosedFixtureCase,
) {
    let context = format!("decompile rust {} fixture strict", case.label);
    assert_eq!(json["target"], "rust", "{context}");
    assert_eq!(json["selection"], "address", "{context}");
    assert_eq!(json["entry"].as_str(), Some(entry_arg), "{context}");
    assert_eq!(json["strict"].as_bool(), Some(true), "{context}");
    assert_eq!(json["status"], "incomplete", "{context}");
    assert_eq!(json["functions_decompiled"].as_u64(), Some(0), "{context}");
    assert_eq!(json["blocks"].as_u64(), Some(0), "{context}");
    assert_eq!(json["instructions"].as_u64(), Some(0), "{context}");
    assert!(json["unsupported"].as_u64().unwrap_or(0) >= 1, "{context}");
    assert_eq!(json["failures"].as_u64(), Some(0), "{context}");
    assert_eq!(json["output_kind"], serde_json::Value::Null, "{context}");
    assert_eq!(json["output_trust_level"], "rejected", "{context}");
    assert_eq!(json["output_validation"], "artifact_not_produced", "{context}");
    assert_eq!(json["output_content"], serde_json::Value::Null, "{context}");

    let unsupported_items =
        json["unsupported_items"].as_array().expect("unsupported_items should be an array");
    assert_json_string_items_contain_all(
        unsupported_items,
        case.expected_fragments,
        context.as_str(),
    );
    assert_no_proof_grade_release_claim(json, context.as_str());
    assert_optional_proof_gate_rejected(json);
}

#[test]
fn test_targo_trust_lift_json_fails_closed_on_unsupported_instruction_semantics() {
    let targo_trust = match find_targo_trust_binary() {
        Some(path) => path,
        None => {
            eprintln!(
                "SKIP: targo-trust binary not found; build it with `cargo build --manifest-path targo-trust/Cargo.toml`"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().expect("create temp unsupported fixture dir");
    let elf_path = match build_x86_64_unsupported_elf_fixture(tmp.path()) {
        Ok(path) => path,
        Err(reason) => {
            eprintln!("SKIP: {reason}");
            return;
        }
    };
    let bytes = read_checked_x86_64_elf_fixture(&elf_path);
    let entry = function_entry_for_symbol(&bytes, UNSUPPORTED_FIXTURE_SYMBOL);
    let entry_arg = format!("0x{entry:x}");

    let output = Command::new(&targo_trust)
        .arg("lift")
        .arg(&elf_path)
        .arg("--entry")
        .arg(&entry_arg)
        .arg("--json")
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", targo_trust.display()));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "strict targo trust lift should fail closed for unsupported semantics\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout was not JSON: {e}\n{stdout}"));
    assert_eq!(json["status"], "incomplete");
    assert_eq!(json["selection"], "address");
    assert_eq!(json["entry"].as_str(), Some(entry_arg.as_str()));
    assert_eq!(json["strict"], true);
    assert_eq!(json["functions_lifted"].as_u64(), Some(0));
    assert_eq!(json["vcs"].as_u64(), Some(0));
    assert_eq!(json["unsupported"].as_u64(), Some(1));
    assert_eq!(json["failures"].as_u64(), Some(0));
    assert!(
        json["failure_items"].as_array().is_some_and(Vec::is_empty),
        "strict unsupported report should not be classified as a generic failure: {json}"
    );
    let unsupported_items =
        json["unsupported_items"].as_array().expect("unsupported_items should be an array");
    assert_eq!(unsupported_items.len(), 1);
    let item = unsupported_items[0].as_str().expect("unsupported item should be a string");
    // Trust: targo-trust lift JSON no longer phrases the failure as
    // "unsupported opcode"; it surfaces "unsupported instruction semantics"
    // plus the concrete opcode (e.g. `opcode Int3`).
    assert_contains_all(
        item,
        &["unsupported instruction semantics", "opcode Int3"],
        "unsupported JSON item",
    );
}

fn read_checked_x86_64_elf_fixture(path: &Path) -> Vec<u8> {
    read_checked_elf_fixture(path, 0x3e, "x86_64 fixture")
}

fn materialize_hex_fixture(
    dir: &Path,
    fixture_name: &str,
    hex_text: &str,
    expected_sha256: &str,
) -> Result<PathBuf, String> {
    let compact = hex_text.chars().filter(|ch| !ch.is_whitespace()).collect::<String>();
    if compact.is_empty() {
        return Err(format!("{fixture_name} hex fixture is empty"));
    }
    if compact.len() % 2 != 0 {
        return Err(format!("{fixture_name} hex fixture has odd byte length"));
    }

    let mut bytes = Vec::with_capacity(compact.len() / 2);
    for index in (0..compact.len()).step_by(2) {
        let byte = u8::from_str_radix(&compact[index..index + 2], 16).map_err(|e| {
            format!(
                "{fixture_name} hex fixture has invalid byte `{}` at offset {index}: {e}",
                &compact[index..index + 2]
            )
        })?;
        bytes.push(byte);
    }

    let actual_sha256 = trust_types::digest::stable_sha256_hex(&bytes);
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "{fixture_name} SHA-256 mismatch: expected {expected_sha256}, got {actual_sha256}"
        ));
    }

    let path = dir.join(fixture_name);
    fs::write(&path, bytes)
        .map_err(|e| format!("could not write materialized fixture {}: {e}", path.display()))?;
    Ok(path)
}

fn read_checked_elf_fixture(path: &Path, expected_machine: u16, context: &str) -> Vec<u8> {
    let bytes =
        fs::read(path).unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    let elf = Elf64::parse(&bytes)
        .unwrap_or_else(|e| panic!("failed to parse generated ELF {}: {e}", path.display()));
    assert_eq!(elf.header.e_machine, expected_machine, "{context} must have expected ELF machine");
    bytes
}

fn function_entry_for_symbol(bytes: &[u8], symbol: &str) -> u64 {
    let elf = Elf64::parse(bytes).expect("generated fixture should parse as ELF");
    let lifter = Lifter::from_elf(&elf).expect("x86_64 ELF should create a lifter");
    lifter
        .functions()
        .iter()
        .find(|boundary| boundary.name == symbol)
        .unwrap_or_else(|| {
            panic!(
                "expected {symbol} in detected ELF function symbols; got {:?}",
                lifter.functions()
            )
        })
        .start
}

fn build_x86_64_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    build_x86_64_elf_fixture_from_asm(dir, "binary_to_trust_ir_return", X86_64_RET_ASM)
}

fn build_x86_64_undecodable_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    build_x86_64_elf_fixture_from_asm(dir, "binary_to_trust_ir_undecodable", X86_64_UNDECODABLE_ASM)
}

fn build_x86_64_unsupported_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    build_x86_64_elf_fixture_from_asm(dir, "binary_to_trust_ir_unsupported", X86_64_UNSUPPORTED_ASM)
}

fn build_x86_64_unresolved_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    build_x86_64_elf_fixture_from_asm(dir, "binary_to_trust_ir_unresolved", X86_64_UNRESOLVED_ASM)
}

fn build_checked_certificate_readback_fixture(
    dir: &Path,
    dispatch_id: &str,
) -> Result<PathBuf, String> {
    let (dispatch, canonical_vc_bytes) = checked_certificate_readback_dispatch(dispatch_id);
    let export = SolverProofExport::new(
        &dispatch,
        &canonical_vc_bytes,
        "lrat",
        b"normalized checked proof payload".to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_400_000,
    );
    let checker = StructuralBinaryCertificateChecker::new(
        "ay-lrat-binary-check",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_401_000,
    );
    let check = check_binary_certificate(
        &checker,
        BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc_bytes, &export),
    );
    let artifact = check
        .certificate
        .ok_or_else(|| format!("checked-certificate fixture check rejected: {:?}", check.error))?;
    persist_checked_certificate_artifact(dir, &artifact)
        .map_err(|error| format!("failed to persist checked-certificate fixture: {error}"))
}

#[cfg(unix)]
fn build_selected_slice_checked_certificate_manifest(
    dir: &Path,
    binary_path: &Path,
    binary_bytes: &[u8],
    function_entry: u64,
    dispatch_id: &str,
) -> Result<(PathBuf, String), String> {
    let identity = selected_slice_binary_identity(binary_bytes);
    let (mut dispatch, canonical_vc_bytes) = selected_slice_release_transcript_dispatch(
        dispatch_id,
        binary_path,
        binary_bytes,
        function_entry,
        identity,
    );
    let proof_bytes = b"normalized selected-slice proof payload";
    let replay_transcript_digest = trust_types::digest::stable_sha256_hex(
        format!("selected-slice replay transcript:{dispatch_id}:{X86_64_LOAD_FIXTURE_SHA256}")
            .as_bytes(),
    );
    let export = SolverProofExport::new(
        &dispatch,
        &canonical_vc_bytes,
        "lrat",
        proof_bytes.to_vec(),
        Some("4.13.0".to_string()),
        1_777_070_410_000,
    );
    let checker = StructuralBinaryCertificateChecker::new(
        "selected-slice-release-check",
        "0.1.0",
        vec!["lrat".to_string()],
        1_777_070_411_000,
    );
    let mut request =
        BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc_bytes, &export);
    request.replay_transcript_digest = Some(replay_transcript_digest.as_str());
    let check = check_binary_certificate(&checker, request);
    let artifact = check.certificate.ok_or_else(|| {
        format!("selected-slice checked-certificate check rejected: {:?}", check.error)
    })?;

    let export_dir = dir.join("selected-slice-checked-certs");
    let artifact_path =
        persist_checked_certificate_artifact(&export_dir, &artifact).map_err(|error| {
            format!("failed to persist selected-slice checked certificate: {error}")
        })?;
    let relative_path = artifact_path
        .strip_prefix(&export_dir)
        .map_err(|error| format!("selected-slice artifact path was outside export dir: {error}"))?
        .to_path_buf();
    let entry = CheckedBinaryCertificateManifestEntry::from_artifact(&artifact, relative_path);
    let checker_script = write_release_transcript_checker_script(
        dir,
        "selected-slice-release-checker.sh",
        "selected-slice release checker ok",
    )?;
    let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
        checker_script.as_path(),
        std::iter::empty::<String>(),
        1_777_070_412_000,
    )
    .map_err(|error| format!("selected-slice external checker runner failed: {error}"))?;
    let production_evidence = runner
        .run_for_manifest_entry(&entry)
        .map_err(|error| format!("selected-slice external checker failed: {error}"))?;
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            &entry,
            export.normalized_metadata(),
        )
        .and_then(|request| request.with_production_checker_evidence(production_evidence))
        .and_then(|request| {
            request.with_source_backpropagation_gate(
                CheckedBinaryCertificateSourceBackpropagationGate::default(),
            )
        })
        .map_err(|error| format!("selected-slice acceptance request failed: {error}"))?;
    let acceptance_record = import_checked_certificate_manifest_entry_for_dispatch(
        &mut dispatch,
        &canonical_vc_bytes,
        &export_dir,
        &entry,
        &acceptance_request,
    )
    .map_err(|error| format!("selected-slice manifest entry import failed: {error}"))?;
    let audit_export = CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
        entry.clone(),
        acceptance_record,
    )
    .map_err(|error| format!("selected-slice audit export failed: {error}"))?;
    let mut manifest = CheckedBinaryCertificateManifest::new();
    manifest.add_certificate(entry);
    persist_checked_certificate_audit_export_bundle(&export_dir, &manifest, &[audit_export])
        .map_err(|error| format!("selected-slice audit export bundle failed: {error}"))?;

    Ok((trust_proof_cert::checked_certificate_manifest_path(&export_dir), replay_transcript_digest))
}

#[cfg(unix)]
fn selected_slice_binary_identity(binary_bytes: &[u8]) -> BinaryArtifactDigestIdentity {
    let digest = trust_types::digest::stable_sha256_hex(binary_bytes);
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest.clone())),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: binary_bytes.len() as u64,
            sha256: digest,
        }),
    }
}

#[cfg(unix)]
fn selected_slice_release_transcript_dispatch(
    dispatch_id: &str,
    binary_path: &Path,
    binary_bytes: &[u8],
    function_entry: u64,
    identity: BinaryArtifactDigestIdentity,
) -> (SolverDispatchRecord, Vec<u8>) {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: X86_64_LOAD_FIXTURE_SYMBOL.into(),
        location: SourceSpan::binary_address(function_entry),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let serializable_vc = SerializableVc::from_vc(&vc);
    let canonical_vc_bytes =
        serde_json::to_vec(&serializable_vc).expect("selected-slice fixture VC should serialize");
    let first_byte = binary_bytes.first().copied().unwrap_or_default();
    let dispatch = SolverDispatchRecord {
        id: dispatch_id.to_string(),
        function: Some(X86_64_LOAD_FIXTURE_SYMBOL.to_string()),
        origin: Some(BinaryOrigin {
            binary_path: Some(binary_path.display().to_string()),
            function_entry: Some(function_entry),
            instruction_address: function_entry,
            instruction_size: Some(1),
            encoding: Some(u32::from(first_byte)),
            instruction_bytes: vec![first_byte],
            source: Some(SourceSpan::binary_address(function_entry)),
        }),
        vc_kind: Some(vc.kind.clone()),
        vc: Some(serializable_vc),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-lrat".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        binary_artifact_digest_identity: Some(identity),
        replay: ReplayStatus::Replayed,
        certificate: ProofCertificateStatus::Unavailable {
            reason: Some("selected-slice checked artifact not imported yet".to_string()),
        },
        ..Default::default()
    };
    (dispatch, canonical_vc_bytes)
}

#[cfg(unix)]
fn write_release_transcript_checker_script(
    dir: &Path,
    name: &str,
    message: &str,
) -> Result<PathBuf, String> {
    use std::os::unix::fs::PermissionsExt;

    let path = dir.join(name);
    fs::write(&path, format!("#!/bin/sh\nprintf '{}'\n", message.replace('\'', "")))
        .map_err(|error| format!("failed to write checker script {}: {error}", path.display()))?;
    let mut permissions = fs::metadata(&path)
        .map_err(|error| format!("failed to stat checker script {}: {error}", path.display()))?
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions)
        .map_err(|error| format!("failed to chmod checker script {}: {error}", path.display()))?;
    Ok(path)
}

fn checked_certificate_readback_dispatch(dispatch_id: &str) -> (SolverDispatchRecord, Vec<u8>) {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "main".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let serializable_vc = SerializableVc::from_vc(&vc);
    let canonical_vc_bytes =
        serde_json::to_vec(&serializable_vc).expect("fixture VC should serialize");
    let dispatch = SolverDispatchRecord {
        id: dispatch_id.to_string(),
        function: Some("main".to_string()),
        origin: Some(BinaryOrigin {
            binary_path: Some("fixtures/tiny.bin".to_string()),
            function_entry: Some(0x401000),
            instruction_address: 0x401010,
            instruction_size: Some(1),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90],
            source: Some(SourceSpan::binary_address(0x401010)),
        }),
        vc_kind: Some(vc.kind.clone()),
        vc: Some(serializable_vc),
        solver: "ay-incremental".to_string(),
        backend: Some("ay-lrat".to_string()),
        status: SolverDispatchStatus::Unsat,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(trust_types::VerificationResult::Proved {
            solver: "ay-incremental".into(),
            time_ms: 4,
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }),
        binary_artifact_digest_identity: Some(checked_certificate_fixture_binary_identity()),
        replay: ReplayStatus::NotAttempted,
        certificate: ProofCertificateStatus::Unavailable {
            reason: Some("checked artifact not imported yet".to_string()),
        },
        ..Default::default()
    };
    (dispatch, canonical_vc_bytes)
}

fn checked_certificate_fixture_binary_identity() -> BinaryArtifactDigestIdentity {
    let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 64,
            sha256: digest.to_string(),
        }),
    }
}

fn build_aarch64_exclusive_elf_fixture(dir: &Path) -> Result<PathBuf, String> {
    build_aarch64_elf_fixture_from_asm(
        dir,
        "binary_to_trust_ir_aarch64_exclusive",
        AARCH64_EXCLUSIVE_ASM,
    )
}

fn build_x86_64_elf_fixture_from_asm(
    dir: &Path,
    fixture_name: &str,
    asm: &str,
) -> Result<PathBuf, String> {
    let asm_path = dir.join(format!("{fixture_name}.s"));
    let obj_path = dir.join(format!("{fixture_name}.o"));
    fs::write(&asm_path, asm)
        .map_err(|e| format!("could not write fixture assembly {}: {e}", asm_path.display()))?;

    let mut attempts = Vec::new();
    for compiler in candidate_compilers() {
        for args in compiler_arg_sets() {
            let _ = fs::remove_file(&obj_path);
            let mut cmd = Command::new(&compiler);
            cmd.args(&args).arg("-c").arg("-x").arg("assembler").arg(&asm_path);
            cmd.arg("-o").arg(&obj_path);

            match cmd.output() {
                Ok(output) if output.status.success() && obj_path.exists() => {
                    return Ok(obj_path);
                }
                Ok(output) => attempts.push(format_attempt(&compiler, &args, &output)),
                Err(e) => attempts.push(format!("{compiler} {:?}: {e}", args)),
            }
        }
    }

    Err(format!(
        "could not build deterministic x86_64 ELF fixture {fixture_name}; tried {}",
        attempts.join("; ")
    ))
}

fn build_aarch64_elf_fixture_from_asm(
    dir: &Path,
    fixture_name: &str,
    asm: &str,
) -> Result<PathBuf, String> {
    let asm_path = dir.join(format!("{fixture_name}.s"));
    let obj_path = dir.join(format!("{fixture_name}.o"));
    fs::write(&asm_path, asm)
        .map_err(|e| format!("could not write fixture assembly {}: {e}", asm_path.display()))?;

    let mut attempts = Vec::new();
    for compiler in candidate_compilers() {
        let _ = fs::remove_file(&obj_path);
        let mut cmd = Command::new(&compiler);
        cmd.arg("--target=aarch64-unknown-linux-gnu")
            .arg("-c")
            .arg("-x")
            .arg("assembler")
            .arg(&asm_path)
            .arg("-o")
            .arg(&obj_path);

        match cmd.output() {
            Ok(output) if output.status.success() && obj_path.exists() => {
                return Ok(obj_path);
            }
            Ok(output) => attempts.push(format_attempt(
                &compiler,
                &["--target=aarch64-unknown-linux-gnu"],
                &output,
            )),
            Err(e) => attempts
                .push(format!("{compiler} {:?}: {e}", ["--target=aarch64-unknown-linux-gnu"])),
        }
    }

    Err(format!(
        "could not build deterministic AArch64 ELF fixture {fixture_name}; tried {}",
        attempts.join("; ")
    ))
}

#[derive(Debug)]
struct ExecutableFixture {
    path: PathBuf,
    architecture: &'static str,
    elf_machine: u16,
}

#[derive(Debug, Clone, Copy)]
struct HostExecutableTarget {
    asm: &'static str,
    architecture: &'static str,
    elf_machine: u16,
}

fn build_host_executable_fixture(dir: &Path) -> Result<ExecutableFixture, String> {
    let target = host_executable_target()?;
    let asm_path = dir.join("binary_to_trust_ir_entry.s");
    let exe_path = dir.join("binary_to_trust_ir_entry");
    fs::write(&asm_path, target.asm)
        .map_err(|e| format!("could not write fixture assembly {}: {e}", asm_path.display()))?;

    let mut attempts = Vec::new();
    for compiler in candidate_compilers() {
        for args in executable_link_arg_sets() {
            let _ = fs::remove_file(&exe_path);
            let mut cmd = Command::new(&compiler);
            cmd.args(&args).arg("-x").arg("assembler").arg(&asm_path);
            cmd.arg("-o").arg(&exe_path);

            match cmd.output() {
                Ok(output) if output.status.success() && exe_path.exists() => {
                    match validate_host_executable(&exe_path, target) {
                        Ok(()) => {
                            return Ok(ExecutableFixture {
                                path: exe_path,
                                architecture: target.architecture,
                                elf_machine: target.elf_machine,
                            });
                        }
                        Err(reason) => attempts
                            .push(format!("{compiler} {args:?} linked unusable fixture: {reason}")),
                    }
                }
                Ok(output) => attempts.push(format_attempt(&compiler, &args, &output)),
                Err(e) => attempts.push(format!("{compiler} {:?}: {e}", args)),
            }
        }
    }

    Err(format!(
        "could not link deterministic host ELF executable fixture; tried {}",
        attempts.join("; ")
    ))
}

fn validate_host_executable(path: &Path, target: HostExecutableTarget) -> Result<(), String> {
    let bytes = fs::read(path)
        .map_err(|e| format!("could not read linked fixture {}: {e}", path.display()))?;
    let elf = Elf64::parse(&bytes)
        .map_err(|e| format!("linked fixture {} was not parseable ELF: {e}", path.display()))?;

    if elf.header.e_type == 1 {
        return Err("linker produced a relocatable object, not an executable image".to_string());
    }
    if elf.header.e_machine != target.elf_machine {
        return Err(format!(
            "unexpected ELF machine 0x{:x}, expected 0x{:x}",
            elf.header.e_machine, target.elf_machine
        ));
    }
    if elf.entry_point() == 0 {
        return Err("linked executable has no entry point".to_string());
    }

    Ok(())
}

fn host_executable_target() -> Result<HostExecutableTarget, String> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("linux", "x86_64") => Ok(HostExecutableTarget {
            asm: X86_64_EXEC_ENTRY_ASM,
            architecture: "x86-64",
            elf_machine: 0x3e,
        }),
        ("linux", "aarch64") => Ok(HostExecutableTarget {
            asm: AARCH64_EXEC_ENTRY_ASM,
            architecture: "AArch64",
            elf_machine: 0xb7,
        }),
        (os, arch) => Err(format!(
            "default-entry executable fixture requires an ELF host supported by trust-lift; host is {arch}-{os}"
        )),
    }
}

fn executable_link_arg_sets() -> Vec<Vec<&'static str>> {
    vec![
        vec!["-nostdlib", "-static", "-no-pie", "-Wl,--build-id=none", "-Wl,-e,_start"],
        vec!["-nostdlib", "-no-pie", "-Wl,--build-id=none", "-Wl,-e,_start"],
        vec!["-nostdlib", "-Wl,-e,_start"],
    ]
}

fn candidate_compilers() -> Vec<String> {
    let mut compilers = Vec::new();
    if let Ok(cc) = std::env::var("TRUST_TEST_CC")
        && !cc.trim().is_empty() {
            compilers.push(cc);
        }
    compilers.push("clang".to_string());
    compilers.push("cc".to_string());
    compilers.dedup();
    compilers
}

fn compiler_arg_sets() -> Vec<Vec<&'static str>> {
    let mut arg_sets = vec![vec!["--target=x86_64-unknown-linux-gnu"]];
    if std::env::consts::OS == "linux" && std::env::consts::ARCH == "x86_64" {
        arg_sets.push(vec![]);
    }
    arg_sets
}

fn format_attempt(compiler: &str, args: &[&str], output: &Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stderr = stderr.trim();
    let detail = if stderr.is_empty() { "no stderr".to_string() } else { stderr.to_string() };
    format!("{compiler} {args:?} exited with {} ({detail})", output.status)
}

fn find_targo_trust_binary() -> Option<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent()?.parent()?;
    let bin_name = format!("targo-trust{}", std::env::consts::EXE_SUFFIX);

    if let Ok(target_dir) = std::env::var("CARGO_TARGET_DIR") {
        for profile in ["debug", "release"] {
            let candidate = PathBuf::from(&target_dir).join(profile).join(&bin_name);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    [
        repo_root.join("target/user/debug").join(&bin_name),
        repo_root.join("target/user/release").join(&bin_name),
        repo_root.join("target/debug").join(&bin_name),
        repo_root.join("target/release").join(&bin_name),
        repo_root.join("targo-trust/target/debug").join(&bin_name),
        repo_root.join("targo-trust/target/release").join(&bin_name),
    ]
    .into_iter()
    .find(|candidate| candidate.is_file())
}

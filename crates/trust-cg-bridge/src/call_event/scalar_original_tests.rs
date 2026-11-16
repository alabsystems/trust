#![cfg(feature = "kernel-recheck")]
use super::*;
#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use serde::{Deserialize, Serialize};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{CallingConv, Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty};

use crate::original_conjunction_certificate::without_production;

fn sample() -> &'static Fixture {
    static FIXTURE: std::sync::OnceLock<Fixture> = std::sync::OnceLock::new();
    FIXTURE.get_or_init(|| {
        // Hand-built explicit-ABI Compiler fixture. This is not a Rust-source
        // refinement or rustc FnAbi witness. Both full-width pointer domains
        // and all independent64 query/register variables must remain intact.
        let mut b = ModBuilder::new("scalar_original_identity");
        let pointer_signature = b.sig(&[Ty::Ptr], Some(Ty::Ptr));
        let pointer =
            b.define("pointer_leaf", pointer_signature, Linkage::External, |f| f.ret(f.p(0)));
        let scalar_signature = b.sig(&[Ty::U64], Some(Ty::U64));
        let scalar =
            b.define("scalar_leaf", scalar_signature, Linkage::External, |f| f.ret(f.p(0)));
        b.define("pointer_tail", pointer_signature, Linkage::External, |f| {
            let value = f.call(pointer, &[f.p(0)]);
            f.ret(value);
        });
        b.define("scalar_tail", scalar_signature, Linkage::External, |f| {
            let value = f.call(scalar, &[f.p(0)]);
            f.ret(value);
        });
        let mut module = b.finish();
        module.target_info = Some(TargetInfo {
            triple: DARWIN.into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        for function in &mut module.functions {
            function.calling_conv = CallingConv::C;
        }
        let object = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O3,
                emit_proofs: false,
                parallel: false,
                never_inline: ["pointer_leaf", "scalar_leaf"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                ..Default::default()
            },
            TargetSpec::parse(DARWIN).unwrap(),
        )
        .with_codegen_license(fixture_license())
        .compile(&module)
        .unwrap()
        .object_code;
        Fixture::with_object(module, object, DARWIN)
    })
}

fn report() -> &'static CerReport {
    static REPORT: std::sync::OnceLock<CerReport> = std::sync::OnceLock::new();
    REPORT.get_or_init(|| sample().report())
}
fn input(fixture: &Fixture) -> CerInput<'_> {
    CerInput {
        m_cg: &fixture.m_cg,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        object: &fixture.object,
        relocation_model: fixture.model,
    }
}
fn replay_without_production(
    input: &CerInput<'_>,
    sidecar: &[u8],
) -> Result<OriginalReplayReport, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, || {
                without_production(|| replay_original_certificates(input, sidecar))
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[derive(Serialize, Deserialize)]
struct Current {
    module: Module,
    producers: Vec<(Module, BTreeMap<FuncId, String>)>,
    bodies: Vec<(String, usize, FuncId)>,
    placements: BTreeMap<String, FnPlacement>,
    object: Vec<u8>,
}

#[test]
fn actual_pointer_scalar_leaves_and_tails_retain_full_original_and_replay_fresh() {
    if let Some(directory) = std::env::var_os("TRUST_SCALAR_ORIGINAL_REPLAY_CHILD") {
        let directory = std::path::PathBuf::from(directory);
        let current: Current =
            serde_json::from_slice(&std::fs::read(directory.join("current.json")).unwrap())
                .unwrap();
        let producers: Vec<_> = current
            .producers
            .into_iter()
            .map(|(module, symbols)| ProducerModule { module: Arc::new(module), symbols })
            .collect();
        let bodies = current
            .bodies
            .into_iter()
            .map(|(name, producer, func)| (name, ProducerBody { producer, func }))
            .collect();
        let input = CerInput {
            m_cg: &current.module,
            producers: &producers,
            bodies: &bodies,
            placements: &current.placements,
            object: &current.object,
            relocation_model: RelocationModel::Static,
        };
        let replay = replay_without_production(
            &input,
            &std::fs::read(directory.join("report.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(replay.rows.len(), 4);
        assert!(replay.all_replayed(), "{replay:?}");
        assert!(replay.unverified_sections.is_empty());
        std::fs::write(
            directory.join("fresh-replay.json"),
            serde_json::to_vec_pretty(&replay).unwrap(),
        )
        .unwrap();
        return;
    }
    let fixture = sample();
    let report = report();
    assert_eq!(report.certificates.len(), 4, "{}", explain(&report));
    assert_eq!(report.closure.closed_kernel.len(), 4, "{}", explain(&report));
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    for row in &report.certificates {
        assert!(row.is_kernel_proved());
        let original = row
            .original_proof
            .as_ref()
            .expect("every actual row retains its full original theorem")
            .original_equations();
        let query = Formula::Var(
            format!("CER_LEAF_QUERY@{}:{}", report.object_sha256, row.symbol),
            Sort::BitVec(64),
        );
        assert_eq!(
            original
                .iter()
                .filter(|(a, c)| matches!((a,c),
            (Formula::Select(_,q),Formula::Select(_,r)) if **q==query&&q==r))
                .count(),
            1
        );
        assert!(original.len() >= 23, "whole memory, all physical ABI locations and return remain");
        let mut names = BTreeMap::new();
        for (a, c) in original {
            for formula in [a, c] {
                formula.visit(&mut |term| {
                    if let Formula::Var(name, sort) = term {
                        names.insert(name.clone(), sort.clone());
                    }
                });
            }
        }
        for register in 19..=29 {
            assert_eq!(names.get(&format!("X{register}")), Some(&Sort::BitVec(64)));
        }
        for register in 8..=15 {
            assert_eq!(names.get(&format!("V{register}")), Some(&Sort::BitVec(128)));
        }
        assert_eq!(names.get("SP"), Some(&Sort::BitVec(64)));
        assert_eq!(names.get("X30"), Some(&Sort::BitVec(64)));
        if let Some(diagnostic) = &row.leaf_memory {
            assert_eq!(diagnostic.source_accesses, 0);
            assert_eq!(diagnostic.machine_accesses, 0);
            assert_eq!(diagnostic.source_coverage_bytes, 0, "no fabricated memory event");
        } else {
            // Complete M5 callers carry their own retained transition packet,
            // not the leaf-only diagnostic record. Its full M0 equation above
            // still ranges over the unrestricted original query.
            assert!(row.symbol.ends_with("_tail"));
        }
        if row.symbol.ends_with("_tail") {
            assert_eq!(row.call_sites.len(), 1);
            assert_eq!(row.call_sites[0].kind, CallSiteKind::Tail);
        }
    }
    let temporary = tempfile::tempdir().unwrap();
    let output = std::env::var_os("TRUST_SCALAR_ORIGINAL_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| temporary.path().to_owned());
    std::fs::create_dir_all(&output).unwrap();
    std::fs::write(output.join("actual-compiler.o"), &fixture.object).unwrap();
    std::fs::write(output.join("report.json"), report.to_json()).unwrap();
    let current = Current {
        module: (*fixture.m_cg).clone(),
        producers: fixture
            .producers
            .iter()
            .map(|p| ((*p.module).clone(), p.symbols.clone()))
            .collect(),
        bodies: fixture.bodies.iter().map(|(n, p)| (n.clone(), p.producer, p.func)).collect(),
        placements: fixture.placements.clone(),
        object: fixture.object.clone(),
    };
    std::fs::write(output.join("current.json"), serde_json::to_vec(&current).unwrap()).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact",
        "call_event::scalar_original_tests::actual_pointer_scalar_leaves_and_tails_retain_full_original_and_replay_fresh",
        "--nocapture","--test-threads=1"]).env("TRUST_SCALAR_ORIGINAL_REPLAY_CHILD",&output).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
}

#[test]
fn valid_weaker_query_packet_cannot_fall_back_to_legacy_scalar_production() {
    let fixture = sample();
    let report = report();
    let row = report.certificate("pointer_leaf").unwrap();
    let original = row.original_proof.as_ref().unwrap().original_equations();
    let query = format!("CER_LEAF_QUERY@{}:pointer_leaf", report.object_sha256);
    let weaker: Vec<_> = original
        .iter()
        .map(|(a, c)| {
            let mut narrow = |term: Formula| match term {
                Formula::Var(ref name, _) if name == &query => {
                    Formula::BitVec { value: 0, width: 64 }
                }
                other => other,
            };
            (a.clone().map(&mut narrow), c.clone().map(&mut narrow))
        })
        .collect();
    assert_ne!(weaker, original);
    let checked = crate::verify_output_instantiate::try_original_conjunction_discharge(&weaker)
        .expect("a real valid kernel proof at q=0 is deliberately insufficient");
    let weak = crate::original_conjunction_certificate::OriginalConjunctionCertificate::bind(
        &checked,
        &input(fixture),
        row,
    )
    .unwrap();
    weak.require_subject(&input(fixture), row).unwrap();
    let mut sidecar: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    let row = sidecar["certificates"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row["symbol"] == "pointer_leaf")
        .unwrap();
    row["original_proof"] = serde_json::to_value(weak).unwrap();
    row["grade"] = serde_json::json!("[PROVED]");
    let replay =
        replay_without_production(&input(fixture), &serde_json::to_vec(&sidecar).unwrap()).unwrap();
    assert_eq!(replay.rows.len(), 4);
    let refused = replay.rows.iter().find(|row| row.symbol == "pointer_leaf").unwrap();
    assert!(!refused.replayed);
    assert!(
        refused.detail.contains("independently expected original equations mismatch"),
        "{}",
        refused.detail
    );
    assert!(!replay.all_replayed());
}

#[test]
fn unsupported_scalar_source_retains_only_its_legacy_grade_and_never_replays() {
    let mut b = ModBuilder::new("scalar_legacy_two_blocks");
    let signature = b.sig(&[Ty::U64], Some(Ty::U64));
    b.define("two_blocks", signature, Linkage::External, |f| {
        let (next, _) = f.block(&[]);
        f.br(next, &[]);
        f.switch_to(next);
        f.ret(f.p(0));
    });
    let mut module = b.finish();
    module.target_info = sample().m_cg.target_info.clone();
    module.functions[0].calling_conv = CallingConv::C;
    let fixture = Fixture::new(module, DARWIN, OptLevel::O3);
    let report = fixture.report();
    let row = report.certificate("two_blocks").unwrap();
    assert!(row.is_kernel_proved(), "legacy scalar statement: {}", explain(&report));
    assert!(row.original_proof.is_none());
    assert!(row.leaf_memory.as_ref().unwrap().status.contains("legacy scalar verification only"));
    let replay = replay_without_production(&input(&fixture), report.to_json().as_bytes()).unwrap();
    assert_eq!(replay.rows.len(), 1);
    assert!(!replay.all_replayed());
}

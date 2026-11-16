//! Observed actual rustc input model, not a deserialized source/FnAbi capability.
#![cfg(feature = "kernel-recheck")]
use super::*;
use crate::compiler_input_capture::{CompilerInputCapture, DecodedCompilerInputs};
use crate::original_conjunction_certificate::without_production;

const CAPTURE: &[u8] = include_bytes!("closure_original/strict-pointer-input.json");
const BODY: &str = "_RNCNvCs9fbHIKxautU_16fn_once_identity14closure_return0B3_";

fn inputs() -> DecodedCompilerInputs {
    CompilerInputCapture::from_bytes(CAPTURE).unwrap().decode_inputs().unwrap()
}
fn report() -> &'static CerReport {
    static REPORT: std::sync::OnceLock<CerReport> = std::sync::OnceLock::new();
    REPORT.get_or_init(|| verify_compiled_module(&inputs().input()).unwrap())
}
fn replay(input: &CerInput<'_>, bytes: &[u8]) -> OriginalReplayReport {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, || {
                without_production(|| replay_original_certificates(input, bytes))
            })
            .unwrap()
            .join()
            .unwrap()
            .unwrap()
    })
}

#[test]
fn actual_rust_nominal_closure_retains_every_complete_original_and_replays_fresh() {
    let data = inputs();
    if let Some(directory) = std::env::var_os("TRUST_CLOSURE_ORIGINAL_REPLAY_CHILD") {
        let path = std::path::PathBuf::from(directory);
        let replay = replay(&data.input(), &std::fs::read(path.join("report.json")).unwrap());
        assert_eq!(replay.rows.len(), 3);
        assert!(replay.all_replayed(), "{replay:?}");
        assert!(replay.unverified_sections.is_empty());
        std::fs::write(path.join("fresh-replay.json"), serde_json::to_vec_pretty(&replay).unwrap())
            .unwrap();
        return;
    }
    let report = report();
    assert_eq!(report.certificates.len(), 3);
    assert_eq!(report.closure.closed_kernel.len(), 3, "{}", report.to_json());
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    assert_eq!(
        report.object_sha256,
        "e4985dd7eee84986c6d0c8b3efcf8c4712cd5c05f15a64d89c329dfbb3df4f3e"
    );
    assert_eq!(data.object.len(), 719);
    // The nominal environment is preserved in both current source models.
    for module in [&data.m_cg, data.producers[0].module.as_ref()] {
        let body = module.functions.iter().find(|f| f.name == BODY).unwrap();
        assert!(matches!(body.blocks[0].params[0].1, IrTy::Closure(_)));
        assert!(matches!(
            body.blocks[0].body[0].inst,
            Inst::ExtractField { ty: IrTy::Ptr, field: 0, .. }
        ));
        assert_eq!(module.closure_types[0].captures, [IrTy::Ptr]);
        assert_eq!(module.closure_layouts[0].capture_offsets, [0]);
    }
    let temporary = tempfile::tempdir().unwrap();
    let output = std::env::var_os("TRUST_CLOSURE_ORIGINAL_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| temporary.path().to_owned());
    std::fs::create_dir_all(&output).unwrap();
    std::fs::write(output.join("actual-rust-compiler.o"), &data.object).unwrap();
    std::fs::write(output.join("current-input.json"), CAPTURE).unwrap();
    std::fs::write(output.join("report.json"), report.to_json()).unwrap();
    if std::env::var_os("TRUST_CLOSURE_ORIGINAL_BASELINE").is_some() {
        assert!(report.certificates.iter().all(|row| row.original_proof.is_none()));
        return;
    }
    for row in &report.certificates {
        let original = row
            .original_proof
            .as_ref()
            .expect("all actual Rust rows retain complete original")
            .original_equations();
        assert_eq!(original.len(), if row.symbol == BODY { 23 } else { 24 });
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
        if let Some(diagnostic) = &row.leaf_memory {
            assert_eq!(diagnostic.source_accesses, 0);
            assert_eq!(diagnostic.machine_accesses, 0);
            assert_eq!(diagnostic.source_coverage_bytes, 0);
        } else {
            assert_eq!(row.call_sites.len(), 1);
            assert_eq!(row.call_sites[0].kind, CallSiteKind::Tail);
        }
    }
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "call_event::closure_original_tests::actual_rust_nominal_closure_retains_every_complete_original_and_replays_fresh", "--nocapture", "--test-threads=1"])
        .env("TRUST_CLOSURE_ORIGINAL_REPLAY_CHILD", &output).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
}

#[test]
fn actual_rust_closure_wrong_field_or_layout_cannot_retain_or_replay() {
    let good = report().to_json();
    for mutation in 0..4 {
        let mut data = inputs();
        match mutation {
            0 => {
                let module = Arc::make_mut(&mut data.producers[0].module);
                let body = module.functions.iter_mut().find(|f| f.name == BODY).unwrap();
                let Inst::ExtractField { field, .. } = &mut body.blocks[0].body[0].inst else {
                    unreachable!()
                };
                *field = 1;
            }
            1 => {
                Arc::make_mut(&mut data.producers[0].module).closure_layouts[0].capture_offsets =
                    vec![8]
            }
            2 => data.m_cg.closure_layouts[0].size = 16,
            3 => data.m_cg.closure_types[0].captures = vec![IrTy::U64],
            _ => unreachable!(),
        }
        let fresh = verify_compiled_module(&data.input()).unwrap();
        assert!(
            fresh.certificates.iter().all(|row| row.original_proof.is_none()),
            "mutation{mutation}: {}",
            fresh.to_json()
        );
        let replay = replay(&data.input(), good.as_bytes());
        assert!(!replay.all_replayed(), "mutation{mutation}: {replay:?}");
        assert!(replay.rows.iter().all(|row| !row.replayed), "mutation{mutation}: {replay:?}");
    }
}

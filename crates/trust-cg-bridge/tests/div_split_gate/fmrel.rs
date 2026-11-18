//! Actual Compiler objects, complete original conjunctions and retained CER replay.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use trust_cg_bridge::call_event::replay_original_certificates;
use trust_cg_bridge::direct_ir_observation::without_original_production;

use super::*;

struct Case {
    subject: &'static str,
    ir: &'static str,
    rem: bool,
    triple: &'static str,
    opt: OptLevel,
    fixture: Fixture,
    report: CerReport,
}

fn key(subject: &str, triple: &str, opt: OptLevel) -> String {
    format!("{subject}-{}-{opt:?}", triple.replace('-', "_"))
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

fn cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        let mut cases = Vec::new();
        for (subject, ir, rem) in [("sdiv_var", SDIV_IR, false), ("srem_var", SREM_IR, true)] {
            for triple in BOTH {
                for opt in OPTS {
                    let fixture = signed_fixture(ir, ir, triple, opt);
                    assert_signed_guard_constants(&fixture, opt);
                    let (report, conjunctions) = verify_recording_conjunctions(&fixture);
                    let report = report.unwrap();
                    assert_eq!(conjunctions.len(), 1, "{subject} {triple} {opt:?}");
                    assert_eq!(conjunctions[0].1, unit_fixture(subject, opt));
                    let certificate = report.certificate("rung").unwrap();
                    assert!(certificate.is_kernel_proved(), "{}", explain(&report));
                    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", explain(&report));
                    let original = certificate.original_proof.as_ref().expect("actual source proof retained");
                    assert_eq!(serde_json::to_value(original).unwrap()["packet"]["model"], 4);
                    eprintln!("FMREL CER {}: exact original, final source proof and strict consumer admission", key(subject, triple, opt));
                    cases.push(Case { subject, ir, rem, triple, opt, fixture, report });
                }
            }
        }
        assert_eq!(cases.len(), 8, "the original complete two-target/two-opt population");
        cases
    })
}

fn fresh_replay(directory: &Path) {
    let mut seen = 0;
    for (subject, ir) in [("sdiv_var", SDIV_IR), ("srem_var", SREM_IR)] {
        for triple in BOTH {
            for opt in OPTS {
                let key = key(subject, triple, opt);
                // Original source and P are selected here independently of the
                // sidecar. No compiler, solver or proof producer is called.
                let fixture = Fixture::with_object(
                    targeted(&parse(ir), triple),
                    std::fs::read(directory.join(format!("{key}.o"))).unwrap(),
                    triple,
                );
                let sidecar = std::fs::read(directory.join(format!("{key}.json"))).unwrap();
                let observed: serde_json::Value = serde_json::from_slice(&sidecar).unwrap();
                let observed_unverified: Vec<String> =
                    serde_json::from_value(observed["unverified_sections"].clone()).unwrap();
                let result = std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(8 << 20)
                        .spawn_scoped(scope, || {
                            without_original_production(|| {
                                replay_original_certificates(&input(&fixture), &sidecar)
                            })
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                })
                .unwrap();
                assert_eq!(result.rows.len(), 1, "{key}: {result:?}");
                assert!(result.all_replayed(), "{key}: {result:?}");
                // Function proof replay reports auxiliary unwind sections
                // separately. Preserve the actual object's existing disclosure;
                // these arithmetic/ABI proofs grant no unwind-metadata claim.
                assert_eq!(result.unverified_sections, observed_unverified, "{key}: {result:?}");
                std::fs::write(
                    directory.join(format!("{key}.fresh.json")),
                    serde_json::to_vec_pretty(&result).unwrap(),
                )
                .unwrap();
                eprintln!(
                    "FMREL fresh CER {key}: retained source proof replayed with production disabled"
                );
                seen += 1;
            }
        }
    }
    assert_eq!(seen, 8);
}

#[test]
fn original_signed_objects_replay_in_a_fresh_process() {
    if let Some(directory) = std::env::var_os("TRUST_FMREL_CONSUMER_REPLAY_ONLY") {
        fresh_replay(Path::new(&directory));
        return;
    }
    let temporary = tempfile::tempdir().unwrap();
    let directory = std::env::var_os("TRUST_FMREL_CONSUMER_OUTPUT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| temporary.path().to_owned());
    std::fs::create_dir_all(&directory).unwrap();
    for case in cases() {
        let key = key(case.subject, case.triple, case.opt);
        std::fs::write(directory.join(format!("{key}.o")), &case.fixture.object).unwrap();
        std::fs::write(directory.join(format!("{key}.json")), case.report.to_json()).unwrap();
    }
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "fmrel::original_signed_objects_replay_in_a_fresh_process",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("TRUST_FMREL_CONSUMER_REPLAY_ONLY", &directory)
        .output()
        .unwrap();
    std::fs::write(directory.join("child.stdout"), &child.stdout).unwrap();
    std::fs::write(directory.join("child.stderr"), &child.stderr).unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let count = String::from_utf8_lossy(&child.stderr).matches("FMREL fresh CER ").count();
    assert_eq!(count, 8, "every independently rebuilt object must replay in the fresh process");
}

#[test]
fn original_signed_mutation_population_stays_fail_closed() {
    let mut seen = Vec::new();
    for case in cases() {
        let mut cell = 0;
        visit_signed_mutants(&case.fixture, case.ir, case.rem, |mutant, what| {
            let (report, calls) = verify_recording(mutant);
            let report = report.unwrap_or_else(|error| panic!("{} {what}: {error}", case.subject));
            let row = report.certificate("rung").unwrap();
            let equivalent = EQUIVALENT_SIGNED_MUTANTS.contains(&(case.subject, what));
            if !equivalent {
                assert!(!row.is_kernel_proved(), "{} {what}: {}", case.subject, explain(&report));
                assert!(
                    report.ships(EmitPolicy::StrictProvenOnly).is_err(),
                    "{} {what}: {}",
                    case.subject,
                    explain(&report)
                );
                assert!(
                    !matches!(row.verdict, OutputVerdict::Proven { .. }),
                    "{} {what}: {}",
                    case.subject,
                    explain(&report)
                );
                assert!(!calls.contains(&true));
            }
            let key = format!("{} {what}", key(case.subject, case.triple, case.opt));
            eprintln!(
                "FMREL mutant {key}: {:?} {}; legacy calls={calls:?}; equivalent={equivalent}",
                row.verdict, row.grade
            );
            if let Some(output) = std::env::var_os("TRUST_FMREL_CONSUMER_OUTPUT_DIR") {
                let output =
                    PathBuf::from(output).join("mutants").join(format!("{:03}", seen.len()));
                std::fs::create_dir_all(&output).unwrap();
                std::fs::write(output.join("object.o"), &mutant.object).unwrap();
                std::fs::write(output.join("report.json"), report.to_json()).unwrap();
                std::fs::write(
                    output.join("module.json"),
                    serde_json::to_vec_pretty(&*mutant.m_cg).unwrap(),
                )
                .unwrap();
                std::fs::write(
                    output.join("placement.json"),
                    serde_json::to_vec_pretty(&mutant.placements).unwrap(),
                )
                .unwrap();
                std::fs::write(output.join("case.json"), serde_json::to_vec_pretty(&serde_json::json!({"key":key,"equivalent":equivalent,"legacy_calls":calls})).unwrap()).unwrap();
            }
            seen.push(key);
            cell += 1;
        });
        assert_eq!(cell, if case.rem { 14 } else { 12 });
    }
    assert_eq!(
        seen.len(),
        104,
        "26 original mutation types across both triples and both opt levels"
    );
    let unique: std::collections::BTreeSet<_> = seen.iter().collect();
    assert_eq!(unique.len(), seen.len(), "no mutation cell may be duplicated");
}

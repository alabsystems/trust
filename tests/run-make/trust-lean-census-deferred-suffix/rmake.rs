// Trust (LEAN-CENSUS-IMPORT-BATCH-1): `-Ztrust-lean-census` on a crate whose
// Clean islands have a NON-EMPTY deferred suffix (every island from the first
// one naming `trust_import_` on). TG14 checks that suffix as ONE header-first
// import batch after program admissions are minted, and TG3 mints them in both
// lanes, `-Ztrust-verify=off` included. Census v3 records exactly that. Before
// it, the observer stopped every such build with "Lean island census: kernel
// roster check mode/outcome mismatch", and a rejected suffix died on that fatal
// before Clean's own errors were emitted.
//
// Each lane compiles three suffixes: one ACCEPTED, one REFUSED before
// elaboration (an import no function admits) and one FALSE (the import exists,
// the theorem does not hold). A rejection must fail the build with Clean's own
// error, never the census fatal, and its transcript must read as an incomplete
// observation under the v3 reader, never as a malformed one.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off

use std::path::Path;

use run_make_support::serde_json::{self, Value, json};
use run_make_support::{cwd, python_command, rfs, rustc, source_root};

/// `first` is the body the suffix imports; `headerProof` is checked in the
/// pre-walk batch, before any admission exists.
const PREFIX: &str = "pub fn first(a: u64, _b: u64) -> u64 {\n    a\n}\n\
    clean { theorem headerProof : True := True.intro }\n";
/// Deferred too (it follows the first import), and accepted in every case:
/// TG14 excludes a refused unit and checks the survivors together.
const FOLLOWING: &str = "clean { theorem following : True := headerProof }\n";

struct Case {
    name: &'static str,
    suffix: &'static str,
    /// The suffix's own theorem, which is registered only when it is accepted.
    theorem: &'static str,
    /// `None`: accepted. `Some(text)`: an error the refused unit's build must
    /// print (for `false`, only the compiler's deferred-island note; Clean's own
    /// elaboration error is pinned by `clean_error`).
    error: Option<&'static str>,
    /// Clean's own error for a FALSE theorem, so the case cannot pass when the
    /// unit is refused for another reason.
    clean_error: Option<&'static str>,
    /// A refusal that must NOT be the reason (the import exists in `false`).
    wrong_reason: Option<&'static str>,
}

/// Clean's elaboration error for `suffixFalse`'s `rfl` (observed at stage 1 of
/// 37bae13ff7 under both lanes: "`suffixFalse` did not elaborate: Type mismatch:
/// expected trust_import_census_suffix__first fvar#0 fvar#1 = fvar#1, got ...").
const CLEAN_FALSE_ERROR: &str = "`suffixFalse` did not elaborate: Type mismatch";

const CASES: [Case; 3] = [
    Case {
        name: "accepted",
        suffix: "clean { theorem suffixProof (a b : UInt64) :\n    \
                 trust_import_census_suffix__first a b = a := rfl }\n",
        theorem: "suffixProof",
        error: None,
        clean_error: None,
        wrong_reason: None,
    },
    Case {
        name: "refused",
        suffix: "clean {\n    def retainedBeforeFailure : Nat := 7\n    \
                 theorem missingImport : True := trust_import_census_suffix__absent\n}\n",
        theorem: "missingImport",
        error: Some("`trust_import_census_suffix__absent` has no checked E6 program admission"),
        clean_error: None,
        wrong_reason: None,
    },
    Case {
        name: "false",
        suffix: "clean { theorem suffixFalse (a b : UInt64) :\n    \
                 trust_import_census_suffix__first a b = b := rfl }\n",
        theorem: "suffixFalse",
        error: Some("this island names the kernel-import namespace"),
        clean_error: Some(CLEAN_FALSE_ERROR),
        wrong_reason: Some("has no checked E6 program admission"),
    },
];

fn lane(verification: bool) -> &'static str {
    if verification { "on" } else { "off" }
}

/// Compile `<tag>.rs` with the census; return stderr, the exit code and the
/// transcript's records.
fn compile(
    tag: &str,
    source: &str,
    verification: bool,
    accepted: bool,
) -> (String, i32, Vec<Value>) {
    rfs::write(format!("{tag}.rs"), source);
    let mut command = rustc();
    command
        .input(format!("{tag}.rs"))
        .crate_name("census_suffix")
        .crate_type("lib")
        .output(format!("lib{tag}.rlib"))
        .arg(format!("-Ztrust-verify={}", lane(verification)))
        // Session::trust_ir_lower_enabled_by_flags: verification on implies
        // direct lowering; with it off this explicit `off` holds. The reader's
        // expected lane is bound from these flags, never from the transcript.
        .arg("-Ztrust-ir-lower=off")
        .arg(format!("-Ztrust-lean-census={tag}.jsonl"))
        .arg("-Zchecksum-hash-algorithm=sha256")
        .env_remove("TRUST_NO_VERIFY");
    let result = if accepted { command.run() } else { command.run_fail() };
    let stderr = result.stderr_utf8();
    rfs::write(format!("{tag}.stderr"), &stderr);
    let code = result.status().code().expect("the compiler exited with a code");
    let records = rfs::read_to_string(format!("{tag}.jsonl"))
        .lines()
        .map(|line| serde_json::from_str(line).expect("census JSONL record"))
        .collect();
    (stderr, code, records)
}

/// The strict reader, exactly as a consumer runs it. It exits 2 on a malformed
/// transcript, which fails `run()`.
fn read(tag: &str, verification: bool, code: i32) -> Value {
    let report = python_command()
        .arg("-I")
        .arg(source_root().join("scripts/lean_island_census.py"))
        .arg("--census")
        .arg(cwd().join(format!("{tag}.jsonl")))
        .arg("--input")
        .arg(cwd().join(format!("{tag}.rs")))
        .arg("--verification")
        .arg(lane(verification))
        .arg("--lowering")
        .arg(lane(verification))
        .arg("--compiler-exit-code")
        .arg(code.to_string())
        .run()
        .stdout_utf8();
    serde_json::from_str(&report).expect("reader JSON report")
}

fn main() {
    for verification in [false, true] {
        let suffix_mode = if verification {
            "post-admission-import-batch"
        } else {
            "verification-disabled-import-batch"
        };
        for case in &CASES {
            let tag = format!("{}_{}", case.name, lane(verification));
            let source = format!("{PREFIX}{}{FOLLOWING}", case.suffix);
            let (stderr, code, records) =
                compile(&tag, &source, verification, case.error.is_none());
            assert!(!stderr.contains("Lean island census"), "{tag}: the census refused: {stderr}");
            assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
            assert!(!stderr.contains("internal:"), "{tag}: {stderr}");

            // Exactly two HIR checks: the header batch [0], then ONE import
            // batch over the whole suffix [1, 2], after the boundary.
            let checks: Vec<&Value> = records.iter().filter(|r| r["event"] == "check").collect();
            assert_eq!(checks.len(), 2, "{tag}: {records:#?}");
            assert_eq!(checks[0]["mode"], "pre-walk-header-first", "{tag}");
            assert_eq!(checks[0]["islands"], json!([0]), "{tag}");
            assert_eq!(checks[1]["mode"], suffix_mode, "{tag}");
            assert_eq!(checks[1]["islands"], json!([1, 2]), "{tag}");
            let boundaries: Vec<usize> = records
                .iter()
                .enumerate()
                .filter(|(_, r)| r["event"] == "program_admissions_boundary")
                .map(|(index, _)| index)
                .collect();
            let suffix_at = records.iter().position(|r| r["mode"] == suffix_mode).unwrap();
            assert_eq!(boundaries.len(), 1, "{tag}: one boundary in either lane");
            assert!(boundaries[0] < suffix_at, "{tag}: the boundary precedes the suffix");

            let roster = &checks[1]["kernel_roster"];
            assert_eq!(roster["check_mode"], "header-first-batch", "{tag}");
            assert_eq!(roster["registration_semantics"], "transactional-module", "{tag}");
            assert_eq!(roster["source_declaration_metadata"], "unavailable-from-import-wrapper");
            assert_eq!(roster["import_recovery"]["all_original_sources_retained"], true, "{tag}");
            assert_eq!(roster["inputs"].as_array().map(Vec::len), Some(2), "{tag}");
            let names: Vec<&str> = roster["declarations"]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row["name"].as_str().unwrap())
                .collect();
            assert!(names.contains(&"following"), "{tag}: {names:?}");

            let report = read(&tag, verification, code);
            assert_eq!(report["missing_islands"], json!([]), "{tag}: {report}");
            let rlib = format!("lib{tag}.rlib");
            match case.error {
                None => {
                    assert_eq!(code, 0, "{tag}");
                    assert!(stderr.contains("kernel-checked after program admission"), "{stderr}");
                    assert_eq!(checks[1]["rejected"], false, "{tag}");
                    assert_eq!(roster["import_recovery"]["refused_units"], json!([]), "{tag}");
                    assert!(names.contains(&case.theorem), "{tag}: {names:?}");
                    assert_eq!(records.last().unwrap()["event"], "complete", "{tag}");
                    assert_eq!(report["record_status"], "observed-complete", "{tag}: {report}");
                    assert!(Path::new(&rlib).exists(), "{tag}");
                }
                Some(error) => {
                    assert_ne!(code, 0, "{tag}");
                    assert!(
                        stderr.contains(error),
                        "{tag}: Clean's own error is missing: {stderr}"
                    );
                    assert!(
                        stderr.contains("this island names the kernel-import namespace"),
                        "{tag}: {stderr}"
                    );
                    if let Some(clean_error) = case.clean_error {
                        assert!(stderr.contains(clean_error), "{tag}: Clean's error: {stderr}");
                    }
                    if let Some(wrong) = case.wrong_reason {
                        assert!(!stderr.contains(wrong), "{tag}: refused for {wrong:?}: {stderr}");
                    }
                    assert_eq!(checks[1]["rejected"], true, "{tag}");
                    // TG14: the refused unit is excluded transactionally and
                    // named; it does not taint the session.
                    assert_eq!(roster["import_recovery"]["refused_units"], json!([0]), "{tag}");
                    assert_eq!(roster["session_tainted"], false, "{tag}");
                    assert!(!names.contains(&case.theorem), "{tag}: {names:?}");
                    assert!(!names.contains(&"retainedBeforeFailure"), "{tag}: {names:?}");
                    assert!(!records.iter().any(|r| r["event"] == "complete"), "{tag}");
                    assert_eq!(report["record_status"], "incomplete", "{tag}: {report}");
                    assert_eq!(report["process_status"], "failed", "{tag}: {report}");
                    assert!(!Path::new(&rlib).exists(), "{tag}");
                }
            }
        }
    }
}

//! Trust: C-ROWS-PRECISION-1's Farkas Sub support reaches the live compiler's
//! certificate publication and overflow-check elision seams, beyond the retained
//! real-MIR fixtures. Exercise checked subtraction at O0 and O3.
//!
//! A safe sub-slice subtraction must carry a real CleanCic payload. The audit
//! must record its actual decision: ELIDED, or KEPT because the hardened twin
//! was not proved, or because optimization left a statement instead of an
//! overflow Assert. Certification alone does not override those seam gates.
//! An off-by-one twin must be refused by strict verification, have no kernel
//! certificate for the failing operation, retain its check under advisory,
//! and actually panic there. Each compilation has its own audit directory.
//!
//! Audit columns follow trust_verify/elide_audit.rs and
//! targo-trust/src/audit_comparison/tests.rs. The JSON payload assertions use
//! the same transport as trust-e9-kernel-discharge-transport.

//@ ignore-cross-compile
//@ needs-unwind

use std::path::{Path, PathBuf};

use run_make_support::{
    CompletedProcess, bin_name, cmd, rfs, run, run_fail, rust_lib_name, rustc_path, serde_json,
};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    let source = rfs::read_to_string("subtraction.rs");
    let line = source.lines().position(|s| s.contains("Some(rest.len() - 4)")).unwrap() + 1;

    for opt in [0, 3] {
        for twin in [false, true] {
            let name = if twin { "twin" } else { "safe" };
            let out = PathBuf::from(format!("o{opt}-{name}"));
            rfs::create_dir_all(&out);
            let result = compile(&trustc, &out, opt, twin, false);
            let report = function_report(&result.stderr_utf8());
            let row = subtraction_row(&report, line);
            let location = audit_location(&row["location"]);
            let decisions = decisions(&out.join("audit"), &location);
            assert_eq!(decisions.len(), 1, "o{opt}/{name}: one decision for the exact Sub row");
            let decision = &decisions[0];
            if twin {
                assert_eq!(
                    row["outcome"], "failed",
                    "o{opt}: the underflow must be refuted: {row}"
                );
                assert_no_clean_cic(row);
                assert_eq!(decision[0], "KEPT", "a failing Sub check was removed: {decision:?}");
                assert_eq!(decision[5], "uncertified", "{decision:?}");
                let refused = compile(&trustc, &out.join("strict"), opt, true, true);
                let refused_report = function_report(&refused.stderr_utf8());
                let refused_row = subtraction_row(&refused_report, line);
                assert_eq!(
                    refused_row["outcome"], "failed",
                    "strict refused another row: {refused_row}"
                );
                assert_no_clean_cic(refused_row);
            } else {
                assert_eq!(row["outcome"], "proved", "o{opt}: safe Sub was not proved: {row}");
                assert_clean_cic(row);
                let twins: Vec<_> = report["results"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|twin| {
                        twin["typed_kind"]["HardenedBoundary"]["callee"]
                            == "mir_assert::Overflow(Sub)"
                            && twin["location"] == row["location"]
                    })
                    .collect();
                let twin_unproved = twins.iter().any(|twin| twin["outcome"] != "proved");
                match decision[0].as_str() {
                    "ELIDED" => {
                        assert!(
                            !twins.is_empty(),
                            "eliding an overflow Assert requires its exact hardened twin: {report}"
                        );
                        assert!(decision[5].starts_with("bb"), "{decision:?}");
                        assert!(
                            !twin_unproved,
                            "an unproved hardened twin must keep the check: {report}"
                        );
                    }
                    "KEPT" => assert!(
                        (decision[5] == "twin" && twin_unproved)
                            || (opt == 3 && decision[5] == "statement"),
                        "a certified Sub was kept without a justified seam gate: {decision:?}"
                    ),
                    _ => unreachable!(),
                }
            }

            // The caller is verification-off; it must execute the very rlib
            // whose advisory build and audit were checked above.
            let executable = bin_name(&format!("o{opt}-{name}-run"));
            let mut caller = cmd(&trustc);
            caller
                .env_remove("TRUST_NO_VERIFY")
                .arg("main.rs")
                .arg("--edition=2021")
                .arg("-Ztrust-verify=off")
                .arg("-Coverflow-checks=on")
                .arg("-Cpanic=unwind")
                .arg(format!("-Copt-level={opt}"))
                .arg(format!(
                    "--extern=subtraction={}",
                    out.join(rust_lib_name("subtraction")).display()
                ))
                .arg("-o")
                .arg(&executable);
            if twin {
                caller.arg("--cfg=twin");
            }
            caller.run();
            if twin {
                run_fail(&executable)
                    .assert_exit_code(101)
                    .assert_stderr_contains("attempt to subtract with overflow");
            } else {
                run(&executable).assert_stdout_equals("Some(0)\n");
            }
        }
    }
}

fn compile(trustc: &Path, out: &Path, opt: u8, twin: bool, strict: bool) -> CompletedProcess {
    rfs::create_dir_all(out.join("audit"));
    let audit = out.join("audit").canonicalize().unwrap();
    let mut compiler = cmd(trustc);
    compiler
        .env_remove("TRUST_NO_VERIFY")
        .env("TRUST_ELIDE_AUDIT", &audit)
        .arg("subtraction.rs")
        .arg("--crate-type=rlib")
        .arg("--crate-name=subtraction")
        .arg("--edition=2021")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-profile=unix_hardened")
        .arg("-Ztrust-verify-level=2")
        .arg("-Ztrust-verify-output=both")
        .arg(if strict { "-Ztrust-policy=strict" } else { "-Ztrust-policy=advisory" })
        .arg("-Coverflow-checks=on")
        .arg("-Cpanic=unwind")
        .arg(format!("-Copt-level={opt}"))
        .arg(if strict { "--emit=metadata" } else { "--emit=link,mir" })
        .arg("--out-dir")
        .arg(out);
    if twin {
        compiler.arg("--cfg=twin");
    }
    if strict {
        let result = compiler.run_fail();
        result.assert_exit_code(1);
        result
    } else {
        compiler.run()
    }
}

fn function_report(stderr: &str) -> serde_json::Value {
    let functions: Vec<serde_json::Value> = stderr
        .lines()
        .filter_map(|line| line.strip_prefix("TRUST_JSON:"))
        .map(|line| serde_json::from_str(line).expect("valid TRUST_JSON object"))
        .filter(|row: &serde_json::Value| row["function"] == "subtraction::subtract")
        .collect();
    assert_eq!(functions.len(), 1, "one published function_result:\n{stderr}");
    functions.into_iter().next().unwrap()
}

fn subtraction_row(report: &serde_json::Value, line: usize) -> &serde_json::Value {
    let hits: Vec<_> = report["results"]
        .as_array()
        .expect("results array")
        .iter()
        .filter(|row| {
            row["kind"] == "overflow:sub"
                && row["location"]["line_start"].as_u64() == Some(line as u64)
        })
        .collect();
    assert_eq!(hits.len(), 1, "one primary row for the authored subtraction: {report}");
    assert_eq!(hits[0]["typed_kind"]["ArithmeticOverflow"]["op"], "Sub", "{}", hits[0]);
    hits[0]
}

fn assert_clean_cic(row: &serde_json::Value) {
    let proof = &row["proof_evidence"];
    assert_eq!(proof["suite"], "trust-certify", "{row}");
    assert_eq!(proof["backend"], "clean-kernel", "{row}");
    let proof_id = proof["proof_id"].as_str().expect("content-addressed proof id");
    assert!(proof_id.starts_with("clean-cic:v2:"), "{row}");
    let artifacts = proof["artifacts"].as_array().expect("proof artifacts");
    let candidates: Vec<_> = artifacts.iter().filter(|a| a["kind"] == "clean_cic").collect();
    assert_eq!(candidates.len(), 1, "one CleanCic artifact for the exact Sub row: {row}");
    let artifact = candidates[0];
    assert_eq!(artifact["format"], "trust-ir-cleancic-v2", "{row}");
    assert_eq!(artifact["artifact_id"].as_str(), Some(proof_id), "{row}");
    let payload = &artifact["metadata"]["CleanCic"];
    assert!(payload["term"].as_array().is_some_and(|term| !term.is_empty()), "{row}");
    assert!(payload["context"].as_array().is_some_and(|context| !context.is_empty()), "{row}");
    assert!(!payload["lineage"].is_null(), "{row}");
}

fn assert_no_clean_cic(row: &serde_json::Value) {
    let proof = &row["proof_evidence"];
    assert!(
        proof["suite"] != "trust-certify" || proof["backend"] != "clean-kernel",
        "a real underflow cannot carry a kernel-proof envelope: {row}"
    );
    if let Some(artifacts) = proof["artifacts"].as_array() {
        for artifact in artifacts {
            assert!(
                artifact["kind"] != "clean_cic" && artifact["metadata"]["CleanCic"].is_null(),
                "a real underflow cannot carry a CleanCic artifact, even malformed: {row}"
            );
        }
    }
}

fn audit_location(span: &serde_json::Value) -> String {
    format!(
        "{}:{}:{}-{}:{}",
        span["file"].as_str().unwrap(),
        span["line_start"],
        span["col_start"],
        span["line_end"],
        span["col_end"]
    )
}

fn decisions(directory: &Path, location: &str) -> Vec<Vec<String>> {
    let mut decisions = Vec::new();
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if !path.file_name().unwrap().to_string_lossy().starts_with("elide-audit-") {
            continue;
        }
        for line in rfs::read_to_string(&path).lines() {
            let row: Vec<String> = line.split('\t').map(str::to_owned).collect();
            if matches!(row[0].as_str(), "ELIDED" | "KEPT") {
                assert_eq!(row.len(), 9, "malformed audit row: {line}");
                // Trust: the audit records the crate and function in separate columns.
                if row[3] == "subtraction"
                    && row[4] == "subtract"
                    && row[6] == "Sub"
                    && row[7] == location
                {
                    assert!(row[8].starts_with('k') && row[8] != "k-", "no exact row key: {line}");
                    decisions.push(row);
                }
            }
        }
    }
    decisions
}

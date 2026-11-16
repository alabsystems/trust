//! Regression for source-bound reified-pointer call accounting.
//! Runtime witnesses and per-function rows matter even when another root makes
//! the whole crate fail. The guarded division theorem does not prove its call.
use run_make_support::{rfs, run, rustc, rustc_path, serde_json};
use serde_json::{json, Value};
use std::collections::BTreeMap;

const FUNCTIONS: &[&str] = &[
    "panic_add", "total_leaf", "reified_bare", "reified_counted",
    "direct_counted", "total_counted", "guarded_counted", "unknown_counted",
    "total_defined_after", "total_defined_after_counted", "reassigned_counted",
    "borrowed_counted", "parameter_maybe_overwritten", "later_total", "constructor_pointer",
];

fn sha256_spelling(value: &Value) -> bool {
    value.as_str().is_some_and(|s| s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit()))
}

fn inspect(policy: &str) -> BTreeMap<String, Value> {
    let mut command = rustc();
    command.input("reified_charge.rs")
        .crate_name("reified_charge").crate_type("lib").emit("metadata")
        .arg("--edition=2021").arg("-Copt-level=0").arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=on").arg("-Ztrust-verify-output=json")
        .arg("--error-format=human")
        .arg("-Zdump-mir=TrustVerify")
        .arg(format!("-Zdump-mir-dir={policy}-mir"))
        .arg(format!("-Ztrust-dump=mir:{policy}-portable"))
        .output(format!("{policy}.rmeta"));
    if policy == "certify" { command.arg("-Ztrust-policy=certify"); }
    command.inspect(|actual| {
        rfs::write(format!("{policy}.command.json"), serde_json::to_vec_pretty(&json!({
            "program":actual.get_program().to_string_lossy(),
            "arguments":actual.get_args().map(|v| v.to_string_lossy().into_owned()).collect::<Vec<_>>(),
            "scope":"run-make command before its standard target finalizer; no environment dump"
        })).unwrap());
    });
    let output = command.run_unchecked();
    let stderr = output.stderr_utf8();
    rfs::write(format!("{policy}.stdout"), output.stdout());
    rfs::write(format!("{policy}.stderr"), output.stderr());
    rfs::write(format!("{policy}.exit.json"),
        serde_json::to_vec_pretty(&json!({"code":output.status().code(),
            "success":output.status().success(),"policy":policy})).unwrap());

    // This negative matrix includes panic_add's own refuted overflow root.
    // Default permits runtime-backed completeness gaps, not refutations, so
    // both policies must refuse this crate. Preserve the actual output first.
    output.assert_exit_code(1);

    // Retain the actual command and original output before any assertion.
    let mut reports = BTreeMap::new();
    for line in stderr.lines().filter_map(|line| line.strip_prefix("TRUST_JSON:")) {
        let report: Value = serde_json::from_str(line).expect("canonical raw transport JSON");
        if report["type"] != "function_result" { continue; }
        let name = report["function"].as_str().expect("function identity").to_owned();
        if !name.starts_with("reified_charge::") { continue; }
        assert!(sha256_spelling(&report["source_sha256"]), "source digest missing: {report}");
        assert!(report.get("transport_budget").is_none_or(Value::is_null),
            "transport was withheld; retain raw failure and investigate: {report}");
        let rows = report["results"].as_array().expect("untruncated row vector");
        assert_eq!(report["total"].as_u64(), Some(rows.len() as u64), "{report}");
        assert!(reports.insert(name, report).is_none(), "duplicate function envelope");
    }
    for name in FUNCTIONS {
        assert!(reports.contains_key(&format!("reified_charge::{name}")),
            "missing {name}, incomplete regression; raw stderr retained in {policy}.stderr");
    }
    assert_eq!(reports.len(), FUNCTIONS.len(), "unexpected own source-body population");
    rfs::write(format!("{policy}.functions.json"), serde_json::to_vec_pretty(&reports).unwrap());
    let compact: BTreeMap<_, _> = reports.iter().map(|(name, report)| {
        let rows: Vec<_> = report["results"].as_array().unwrap().iter().map(|row| json!({
            "kind":row["kind"], "outcome":row["outcome"], "location":row["location"],
            "description":row["description"], "proof_backend":row["proof_evidence"]["backend"],
            "strength":row["proof_evidence"]["strength"], "native":row["native_trust_ir"]["status"],
            "grade":row["grade"], "obligation_id":row["obligation_id"],
            "claim_digest_sha256":row["claim_digest_sha256"]
        })).collect();
        (name.clone(), json!({"source_sha256":report["source_sha256"],
            "stable_ids":report["stable_ids"], "proved":report["proved"],
            "failed":report["failed"], "unknown":report["unknown"],
            "timed_out":report["timed_out"], "skipped":report["skipped"],
            "runtime_checked":report["runtime_checked"], "total":report["total"], "rows":rows}))
    }).collect();
    rfs::write(format!("{policy}.summary.json"), serde_json::to_vec_pretty(&compact).unwrap());
    println!("FNPTR_CHARGE {}", serde_json::to_string(&json!({
        "policy":policy,"exit":output.status().code(),"functions":compact})).unwrap());
    reports
}

fn main() {
    assert!(std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_none(),
        "this regression requires the actual Trust compiler; no vanilla skip");
    rfs::write("selected-compiler.txt", format!("{}\n", rustc_path()));
    let default = inspect("default");
    let certify = inspect("certify");
    for (policy, reports) in [("default", &default), ("certify", &certify)] {
        // An independently proved division remains visible, but cannot erase
        // the unproved call. Guarding its argument is outside this repair's
        // unconditional-registry route and stays honestly charged.
        for name in ["reified_counted", "direct_counted", "guarded_counted", "unknown_counted",
                     "reassigned_counted", "borrowed_counted", "parameter_maybe_overwritten"] {
            let report = &reports[&format!("reified_charge::{name}")];
            let rows = report["results"].as_array().unwrap();
            assert!(rows.iter().any(|row| row["kind"] == "divzero" && row["outcome"] == "proved"),
                "{policy} lost the real independent division theorem for {name}");
            assert!(rows.iter().any(|row| row["kind"] == "assert" && row["outcome"] != "proved"),
                "{policy} hid the call obligation for {name}: {report}");
            assert!(!rows.iter().any(|row| row["kind"] == "assert" && row["outcome"] == "proved"),
                "{policy} falsely discharged an unproved/mutated target for {name}");
        }
        let bare = &reports["reified_charge::reified_bare"];
        let rows = bare["results"].as_array().unwrap();
        assert!(rows.iter().any(|row| row["kind"] == "assert" && row["outcome"] != "proved"),
            "{policy} hid the bare pointer's panic-freedom carrier: {bare}");
        assert!(!rows.iter().any(|row| row["kind"] == "assert" && row["outcome"] == "proved"),
            "{policy} falsely discharged the bare pointer's unproved target: {bare}");
        for name in ["total_counted", "total_defined_after", "total_defined_after_counted"] {
            let report = &reports[&format!("reified_charge::{name}")];
            let rows = report["results"].as_array().unwrap();
            assert!(rows.iter().all(|row| row["outcome"] == "proved"),
                "{policy} lost the legitimate total target for {name}: {report}");
            let composed: Vec<_> = rows.iter().filter(|row| row["kind"] == "assert").collect();
            assert_eq!(composed.len(), 1, "{policy} changed the exact call carrier for {name}");
            for row in composed {
                // The live private closure authority is Trusted/Deductive. Its
                // complete public grade names the unvalidated encoder and both
                // compiler-composition premises. This is not a backend/kernel
                // certificate: that envelope is deliberately withheld for a
                // closed-world derivation. Require the exact disclosure rather
                // than a status label or a nonexistent native proof strength.
                assert_eq!(row["grade"], json!({
                    "encoding":"unvalidated-encoder", "discharge":"compiler-composed",
                    "premises":["panic-free-callee-registry", "sibling-rows"]
                }), "{policy} lost the Trusted registry-composition grade for {name}: {row}");
                assert!(row.get("proof_evidence").is_none_or(Value::is_null),
                    "{policy} published a standalone certificate for a composition: {row}");
                assert!(row.get("native_trust_ir").is_none_or(Value::is_null),
                    "{policy} attached a native proof envelope to a composition: {row}");
                assert_eq!(row["obligation_id"],
                    format!("vc:reified_charge__{name}:assertion:panic-freedom:0"),
                    "{policy} moved the whole-function call carrier for {name}");
                assert!(sha256_spelling(&row["claim_digest_sha256"]),
                    "{policy} omitted the exact claim identity for {name}");
                let original = &row["original_vc_snapshot"];
                assert_eq!(original["obligation_id"], row["obligation_id"],
                    "{policy} detached the original claim's obligation identity for {name}");
                assert_eq!(original["claim_digest_sha256"], row["claim_digest_sha256"],
                    "{policy} detached the original claim digest for {name}");
                assert_eq!(original["overflow_checks"], true,
                    "{policy} changed the original arithmetic semantics for {name}");
                let other = if policy == "default" { &certify } else { &default };
                let same = other[&format!("reified_charge::{name}")]["results"]
                    .as_array().unwrap().iter().find(|candidate|
                        candidate["obligation_id"] == row["obligation_id"])
                    .expect("both policies retain the same exact call carrier");
                assert_eq!(same["claim_digest_sha256"], row["claim_digest_sha256"],
                    "policy changed the exact original claim for {name}");
            }
        }
    }
    for name in FUNCTIONS {
        let path = format!("reified_charge::{name}");
        assert_eq!(default[&path]["source_sha256"], certify[&path]["source_sha256"],
            "policy must not change original body identity: {path}");
    }
    // An explicit unverified LLVM runtime oracle establishes the source witness;
    // it makes no statement about proof authority or TrustCG output.
    let compiler = rustc().input("runtime.rs").output("runtime-oracle")
        .arg("--edition=2021").arg("-Copt-level=0").arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=off").arg("-Zcodegen-backend=llvm").run_unchecked();
    rfs::write("runtime-build.stdout", compiler.stdout());
    rfs::write("runtime-build.stderr", compiler.stderr());
    compiler.assert_exit_code(0);
    let output = run("runtime-oracle");
    rfs::write("runtime.stdout", output.stdout());
    rfs::write("runtime.stderr", output.stderr());
    output.assert_stdout_contains("pointer_panics=true direct_panics=true guarded=128 total=255");
    println!("FNPTR_CHARGE_RUNTIME {}", output.stdout_utf8().trim());
}

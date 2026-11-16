//! Trust: root-row proof never accounts for members of a discarded native bundle.
//! These are actual source-produced rows and strict compiler exits. This is a
//! regression for the evidence boundary, not a measured former false acceptance.

use run_make_support::{rfs, run, rustc, serde_json};

fn report(stderr: &str, function: &str) -> serde_json::Value {
    let reports: Vec<serde_json::Value> = stderr
        .lines()
        .filter_map(|line| line.strip_prefix("TRUST_JSON:"))
        .map(|line| serde_json::from_str(line).expect("canonical transport JSON"))
        .filter(|row: &serde_json::Value| {
            row["type"] == "function_result" && row["function"] == function
        })
        .collect();
    assert_eq!(reports.len(), 1, "one complete function report for {function}:\n{stderr}");
    reports.into_iter().next().unwrap()
}

fn rows(report: &serde_json::Value) -> &[serde_json::Value] {
    report["results"].as_array().expect("complete result array")
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rfs::write(
        "discarded.rs",
        r#"
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]
fn debt(divisor: u32) -> u32 { 100 / divisor }
// A direct N is a modeled SymArray. N+1 is an unresolved non-Param
// array length in this generic body, so it exercises the actual refusal.
fn root<const N: usize>(_: [u8; N + 1], x: u8, divisor: u32) -> u16
where [(); N + 1]: Sized,
{
    let _ = debt(divisor);
    x as u16 + 1
}
pub fn entry() -> u16 { root::<3>([0; 4], 8, 0) }
"#,
    );
    let refused = rustc()
        .input("discarded.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=strict")
        .arg("-Ztrust-verify-output=json")
        .arg("-Coverflow-checks=off")
        .env_remove("TRUST_NO_VERIFY")
        .run_fail();
    refused.assert_exit_code(1);
    let stderr = refused.stderr_utf8();
    assert!(stderr.contains("Trust full verification failed for `discarded::root`"), "{stderr}");
    assert!(stderr.contains("is not a concrete target usize"), "actual generic lowering refusal: {stderr}");
    assert!(!stderr.contains("abort SUPPRESSED"), "{stderr}");
    let root = report(&stderr, "discarded::root");
    let root_rows = rows(&root);
    let arithmetic: Vec<_> = root_rows
        .iter()
        .filter(|row| row["kind"] == "overflow:add")
        .collect();
    assert_eq!(arithmetic.len(), 1, "the widening add has one real source row: {root}");
    assert_eq!(arithmetic[0]["outcome"], "proved", "{root}");
    assert_eq!(arithmetic[0]["proof_evidence"]["backend"], "clean-kernel", "{root}");
    let gaps: Vec<_> = root_rows
        .iter()
        .filter(|row| row["kind"] == "native-verification-gap")
        .collect();
    assert_eq!(gaps.len(), 1, "exactly one debt row for the discarded bundle: {root}");
    assert_eq!(gaps[0]["outcome"], "unknown", "{root}");
    let member = report(&stderr, "discarded::debt");
    assert!(rows(&member).iter().any(|row| {
        row["kind"] == "divzero" && row["outcome"] != "proved"
    }), "the discarded member's own source obligation remains unproved: {member}");

    // Closing a verifier bypass does not reject this valid Rust program when
    // verification is explicitly off. No panic-freedom claim is made here.
    rustc()
        .input("discarded.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=off")
        .arg("--emit=metadata")
        .run();

    // Complete native bundles retain genuine sealed R1 row propagation. All
    // calls establish the helper's precondition, so its division is proved.
    rfs::write(
        "retained.rs",
        r#"
fn helper(x: u32, divisor: u32) -> u32 { x / divisor }
fn main() { let _ = helper(10, 5); }
"#,
    );
    let retained = rustc()
        .input("retained.rs")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=strict")
        .arg("-Ztrust-verify-output=json")
        .env("TRUST_R1_TRACE", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run();
    let stderr = retained.stderr_utf8();
    assert!(stderr.contains("ADMITTED FLIP"), "the sealed R1 lane still runs: {stderr}");
    let helper = report(&stderr, "retained::helper");
    assert!(!rows(&helper).is_empty(), "{helper}");
    assert!(rows(&helper).iter().all(|row| row["outcome"] == "proved"), "{helper}");
    assert!(rows(&helper).iter().all(|row| row["kind"] != "native-verification-gap"), "{helper}");
    run("retained");
}

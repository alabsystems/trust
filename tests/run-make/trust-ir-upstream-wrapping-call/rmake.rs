//! Trust: std IR metadata keeps the real wrapping-add call and its effects.
//! Requires the std producer (`rust.trust-ir-metadata=true`); missing metadata
//! is a failed qualification, not a skipped test or authority from the model.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64
use run_make_support::{rfs, rustc, serde_json};

fn main() {
    rfs::write("wrapper.rs", "pub fn wrapper(a: u64, b: u64) -> u64 { a.wrapping_add(b) }\n");
    rfs::create_dir("ir");
    rustc().input("wrapper.rs").crate_type("lib").emit("trust-ir")
        .out_dir("ir").arg("-Ztrust-verify=on").arg("-Coverflow-checks=on")
        .env_remove("TRUST_NO_VERIFY").run();
    let text = rfs::read_to_string("ir/wrapper.trust-ir.txt");
    let marker = "; #display-path: \"wrapper\"\n";
    let body = text.split_once(marker).expect("recorded wrapper").1
        .split_once("\n}\n").expect("wrapper end").0;
    assert_eq!(body.matches("call ").count(), 1, "preserve the actual call: {body}");
    assert!(!body.contains("= add "), "the model must not erase this call: {body}");
    let data: serde_json::Value = serde_json::from_str(
        &rfs::read_to_string("ir/wrapper.trust-ir.effect-conservation.json"),
    ).expect("conservation sidecar");
    let rows: Vec<_> = data["functions"].as_array().expect("function roster").iter()
        .filter(|row| row["def_path"] == "wrapper").collect();
    assert_eq!(rows.len(), 1, "one actual wrapper body");
    assert_eq!(rows[0]["verdict"], "conserved", "{}", rows[0]);
    assert_eq!(rows[0]["tags"], serde_json::json!([]));
    assert_eq!(rows[0]["equivalences"], serde_json::json!({}),
        "a kept call needs no model equivalence");

    // A kept call alone cannot establish that std supplied metadata: an SDK
    // outside the model's fingerprints also takes the generic call path.
    // Require successful sealed upstream readmission and strict native codegen.
    rfs::create_dir("native");
    rustc().input("wrapper.rs").crate_type("rlib").out_dir("native")
        .arg("-Cpanic=abort").arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=on").arg("-Ztrust-ir-lower=on")
        .arg("-Zcodegen-backend=trust-cg").arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-f1-backend=compiler").arg("-Ztrust-cg-output-gate=strict")
        .env_remove("TRUST_NO_VERIFY").run();
    let coverage = rfs::read_to_string("native/wrapper.trust-instance-coverage.json");
    for expected in ["\"kind\": \"upstream-entry\"", "content SHA256",
                     "rebound module SHA256", "conservation re-derived"] {
        assert!(coverage.contains(expected), "missing {expected}: {coverage}");
    }
}

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};
use std::path::PathBuf;

const SUPPORTED: [&str; 8] = [
    "entry_field", "retyped_field", "local_retyped", "nested_signed", "read_after_store",
    "alias_after_store", "borrowed_control", "identity",
];
const REFUSED: [&str; 8] = [
    "integer_origin", "call_origin", "derived_origin", "packed_field", "float_field",
    "retyped_address_integer", "borrowed_retype", "fat_origin",
];

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    cmd(&trustc)
        .args([
            "-Ztrust-verify=off", "-Ztrust-ir-lower", "--edition=2021", "--crate-type=lib",
            "--crate-name=raw_field_read", "--emit=metadata", "-Ztrust-dump=ir:raw-field-read",
            "subject.rs", "-o", "raw-field-read.rmeta",
        ])
        .run();
    let report: serde_json::Value = serde_json::from_slice(&rfs::read(
        PathBuf::from("raw-field-read").join("raw_field_read.coverage.json"),
    ))
    .unwrap();
    assert_eq!(report["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(report["publication"]["commit_marker"], true);
    let bodies = report["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), SUPPORTED.len() + REFUSED.len(), "complete source body census");
    for name in SUPPORTED.into_iter().chain(REFUSED) {
        let rows: Vec<_> = bodies.iter().filter(|row| row["def_path"].as_str()
            .is_some_and(|path| path.rsplit("::").next() == Some(name))).collect();
        assert_eq!(rows.len(), 1, "exact owner {name}");
        if SUPPORTED.contains(&name) {
            assert_eq!(rows[0]["lowered"], true, "{name}: {}", rows[0]);
            assert_eq!(rows[0]["unsupported"], serde_json::json!([]), "{name}: {}", rows[0]);
        } else {
            assert_eq!(rows[0]["lowered"], false, "{name}: {}", rows[0]);
            assert_eq!(rows[0]["spliced"], false, "unsupported source cannot be spliced");
        }
    }
    let ir = String::from_utf8(rfs::read(
        PathBuf::from("raw-field-read").join("raw_field_read.trust-ir.txt"),
    ))
    .unwrap();
    for (name, load) in [
        ("entry_field", "load u64"), ("retyped_field", "load u64"),
        ("local_retyped", "load u64"), ("nested_signed", "load i16"),
        ("read_after_store", "load u64"), ("alias_after_store", "load u64"),
    ] {
        // Functions are named by their actual link symbols after assembly.
        let matching: Vec<_> = ir.split("\n}\n").filter(|body| body.lines().any(|line| {
            let Some(path) = line.trim().strip_prefix("; #display-path: ") else { return false; };
            let path: String = serde_json::from_str(path).unwrap();
            path.rsplit("::").next() == Some(name)
        })).collect();
        assert_eq!(matching.len(), 1, "one canonical function for {name}");
        let body = matching[0];
        assert!(body.contains("gep i8") && body.contains(load), "selected integer field: {body}");
        assert!(!body.contains("load struct"), "must not read sibling fields: {body}");
        if name.ends_with("after_store") {
            assert!(body.find("store u64").unwrap() < body.find(load).unwrap(), "store before read");
        }
    }
}

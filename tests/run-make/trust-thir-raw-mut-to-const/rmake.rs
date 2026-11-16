use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};
use std::path::PathBuf;

const SUPPORTED: [&str; 7] = [
    "identity", "array", "unit", "nested", "local", "entry_field", "source_once",
];
const UNCHANGED: [&str; 1] = ["borrowed"];
const REFUSED: [&str; 8] = [
    "fat", "unresolved", "borrowed_retype", "local_escape", "pointer_int", "integer_field",
    "write_retyped", "unsafe_fn",
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
            "--crate-name=raw_mut_to_const", "--emit=metadata", "-Ztrust-dump=ir:raw-mut-to-const",
            "subject.rs", "-o", "raw-mut-to-const.rmeta",
        ])
        .run();
    let report: serde_json::Value = serde_json::from_slice(&rfs::read(
        PathBuf::from("raw-mut-to-const").join("raw_mut_to_const.coverage.json"),
    ))
    .unwrap();
    assert_eq!(report["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(report["publication"]["commit_marker"], true);
    let bodies = report["bodies"].as_array().unwrap();
    // The array source and destination each contain a real anonymous length
    // body. Retain them in the denominator along with every function owner.
    assert_eq!(bodies.len(), 18, "complete source body census");
    assert_eq!(bodies.iter().filter(|row| row["kind"] == "const-init").count(), 2);
    for name in SUPPORTED.into_iter().chain(UNCHANGED).chain(REFUSED) {
        let rows: Vec<_> = bodies.iter().filter(|row| row["def_path"].as_str()
            .is_some_and(|path| path.rsplit("::").next() == Some(name))).collect();
        assert_eq!(rows.len(), 1, "exact owner {name}");
        if SUPPORTED.contains(&name) || UNCHANGED.contains(&name) {
            assert_eq!(rows[0]["lowered"], true, "{name}: {}", rows[0]);
            assert_eq!(rows[0]["unsupported"], serde_json::json!([]), "{name}: {}", rows[0]);
        } else {
            assert_eq!(rows[0]["lowered"], false, "{name}: {}", rows[0]);
            assert_eq!(rows[0]["spliced"], false, "unsupported source cannot be spliced");
        }
    }
    let ir = String::from_utf8(rfs::read(
        PathBuf::from("raw-mut-to-const").join("raw_mut_to_const.trust-ir.txt"),
    ))
    .unwrap();
    for name in SUPPORTED {
        // Canonical module functions use link symbols. Join the human path
        // directive instead of assuming the source name is a linker symbol.
        let matching: Vec<_> = ir.split("\n}\n").filter(|body| body.lines().any(|line| {
            let Some(path) = line.trim().strip_prefix("; #display-path: ") else { return false; };
            let path: String = serde_json::from_str(path).unwrap();
            path.rsplit("::").next() == Some(name)
        })).collect();
        assert_eq!(matching.len(), 1, "one canonical function for {name}");
        let body = matching[0];
        assert_eq!(body.matches("ptrtoptr").count(), 1, "one address identity: {body}");
        assert!(!body.contains("ptrtoint") && !body.contains("inttoptr"), "no integer authority: {body}");
        if name == "entry_field" {
            assert_eq!(body.matches("load u64").count(), 1, "one selected field load: {body}");
            assert!(body.contains("gep i8") && !body.contains("load struct"));
        }
        if name == "source_once" {
            assert_eq!(body.matches("store u64").count(), 1, "source evaluated once: {body}");
            assert!(body.find("store u64").unwrap() < body.find("ptrtoptr").unwrap());
        }
    }
}

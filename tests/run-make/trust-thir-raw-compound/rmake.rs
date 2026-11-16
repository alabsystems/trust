use std::path::PathBuf;
use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

const SUPPORTED: [&str; 7] = [
    "scalar_update", "header_update", "nested_update", "rhs_update",
    "reassign_update", "shift_update", "header_store",
];
const REFUSED: [&str; 3] = ["derived_update", "float_update", "packed_update"];

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    for checks in ["off", "on"] {
        let dump = format!("raw-compound-{checks}");
        cmd(&trustc)
            .args(["-Ztrust-verify=off", "-Ztrust-ir-lower", "--edition=2021",
                "--crate-type=lib", "--crate-name=raw_compound", "--emit=metadata"])
            .arg(format!("-Coverflow-checks={checks}"))
            .arg(format!("-Ztrust-dump=ir:{dump}"))
            .arg("subject.rs").arg("-o").arg(format!("{dump}.rmeta")).run();
        let report: serde_json::Value = serde_json::from_slice(
            &rfs::read(PathBuf::from(&dump).join("raw_compound.coverage.json")),
        ).unwrap();
        assert_eq!(report["schema"], "trust.thir-lower.crate-module.coverage.v2");
        assert_eq!(report["publication"]["commit_marker"], true);
        let bodies = report["bodies"].as_array().unwrap();
        assert_eq!(bodies.len(), SUPPORTED.len() + REFUSED.len(), "full body census: {report}");
        for name in SUPPORTED.into_iter().chain(REFUSED) {
            let rows: Vec<_> = bodies.iter().filter(|row| row["def_path"].as_str()
                .is_some_and(|path| path.rsplit("::").next() == Some(name))).collect();
            assert_eq!(rows.len(), 1, "exact source owner {name}");
            let row = rows[0];
            if SUPPORTED.contains(&name) {
                assert_eq!(row["lowered"], true, "{checks}: {name}: {row}");
                assert_eq!(row["unsupported"], serde_json::json!([]), "{name}: {row}");
            } else {
                assert_eq!(row["lowered"], false, "{name} must retain its refusal: {row}");
                assert_eq!(row["spliced"], false, "unsupported source cannot be spliced: {row}");
            }
        }
        // Pointer-memory interpreter sampling is not proof authority. The direct
        // typed producer must retain field addressing and leave siblings untouched.
        let ir = String::from_utf8(rfs::read(PathBuf::from(&dump).join("raw_compound.trust-ir.txt"))).unwrap();
        for name in ["header_update", "nested_update", "rhs_update", "reassign_update", "shift_update"] {
            let body = ir.split(&format!("fn @{name}(" )).nth(1).unwrap().split("\n}").next().unwrap();
            assert!(body.contains("gep i8"), "selected field byte address: {body}");
            assert!(body.contains("load u64"), "read only selected field: {body}");
            assert!(body.contains("store u64"), "write only selected field: {body}");
            assert!(!body.contains("load struct"), "must not read uninitialized siblings: {body}");
        }
    }
}

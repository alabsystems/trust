use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json};

pub fn check() {
    let coverage = super::compile("prepass.rs", "prepass", "prepass-ir", None);
    super::no_proof(&coverage);
    for (name, expected) in [
        ("bodies", 8), ("lowered", 5), ("spliced", 5),
        ("initializer_bodies", 0), ("symbolic", 0), ("unsupported", 6),
    ] {
        assert_eq!(coverage["totals"][name], expected, "{name}: {coverage}");
    }
    let names: std::collections::BTreeSet<_> = coverage["bodies"].as_array().unwrap()
        .iter().map(|row| row["def_path"].as_str().unwrap()).collect();
    assert_eq!(names, std::collections::BTreeSet::from([
        "dead_half_write", "dead_union_write", "rejected_before_valid",
        "valid_before_rejected", "reached_half", "reached_union", "reached_fat",
        "prepass_runtime",
    ]));
    for name in ["dead_half_write", "dead_union_write", "rejected_before_valid", "valid_before_rejected", "prepass_runtime"] {
        let row = super::row(&coverage, name);
        assert_eq!(row["lowered"], true, "{row}");
        assert_eq!(row["spliced"], true, "{row}");
        assert_eq!(row["kind"], "fn");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{row}");
    }
    for name in ["dead_half_write", "dead_union_write"] {
        let row = super::row(&coverage, name);
        assert_eq!(row["differentials"]["interpreter"]["verdict"], "agreed", "{row}");
        assert_eq!(row["differentials"]["interpreter"]["samples"], 1);
        assert_eq!(row["differentials"]["derived_mir"]["verdict"], "agreed", "{row}");
    }
    for name in ["reached_half", "reached_union", "reached_fat"] {
        let row = super::row(&coverage, name);
        assert_eq!(row["lowered"], false, "{row}");
        assert_eq!(row["spliced"], false, "{row}");
        let expected = if name == "reached_half" {
            serde_json::json!([["Assign(whole struct incomplete type)", 1], ["Ty(float-width)", 3]])
        } else {
            serde_json::json!([["Assign(whole struct incomplete type)", 1]])
        };
        assert_eq!(row["unsupported"], expected, "{row}");
    }

    let text = rfs::read_to_string("prepass-ir/prepass.trust-ir.txt");
    assert!(!text.contains("struct @Half {"));
    assert!(!text.contains("struct @WithUnion {"));
    let declarations: Vec<_> = text.lines().filter(|line| line.starts_with("struct @Cell {")).collect();
    assert_eq!(declarations.len(), 1, "one accepted Cell descriptor");
    let sid = declarations[0].rsplit_once("id=").unwrap().1;
    for name in ["dead_half_write", "dead_union_write"] {
        let body = super::body(&text, name);
        assert!(!body.contains("store ") && !body.contains("alloca "), "{body}");
    }
    for name in ["rejected_before_valid", "valid_before_rejected"] {
        let body = super::body(&text, name);
        assert!(body.contains(&format!("store struct.{sid} ")), "{body}");
        assert!(body.contains(&format!("load struct.{sid},")), "{body}");
        assert!(!body.contains("call "), "{body}");
    }

    // With verification off, strict is a producer coverage comparison, not a proof.
    cmd(rustc_path()).args([
        "prepass.rs", "--edition=2021", "--crate-type=lib", "--crate-name=prepass",
        "--emit=mir", "-Copt-level=0", "-Coverflow-checks=on", "-Ztrust-verify=off",
        "-Ztrust-ir-lower=strict", "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:prepass-strict-ir",
        "-o", "prepass-strict.mir",
    ]).env_remove("TRUST_CONTRACT_CARRY_SHADOW").run();
    let strict: serde_json::Value = serde_json::from_slice(&rfs::read(
        "prepass-strict-ir/prepass.coverage.json",
    )).unwrap();
    assert_eq!(coverage, strict);

    rfs::create_dir("prepass-shadow");
    assert_eq!(coverage, super::compile("prepass.rs", "prepass", "prepass-shadow-ir", Some("prepass-shadow")));
    assert_eq!(rfs::read("prepass-ir/prepass.trust-ir.bin"),
        rfs::read("prepass-shadow-ir/prepass.trust-ir.bin"));
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "prepass-shadow/prepass.contract-carry.shadow.json",
    )).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for name in ["duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries"] {
        assert!(shadow[name].as_array().unwrap().is_empty(), "{name}: {shadow}");
    }
    let values = shadow["interpreted"].as_array().unwrap();
    assert_eq!(values.len(), 1);
    assert_eq!(values[0]["display_path"], "prepass_runtime");
    assert_eq!(values[0]["function"], super::row(&coverage, "prepass_runtime")["func_id"]);
    assert_eq!(values[0]["value"], serde_json::json!({"raw": "1224"}));

    let flags = ["--edition=2021", "-Copt-level=0", "-Coverflow-checks=on",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=off", "-Ztrust-ir-flip=no", "-Zcodegen-backend=llvm"];
    cmd(rustc_path()).args(flags).args(["prepass.rs", "--crate-type=rlib",
        "--crate-name=prepass_reference", "-o", "libprepass_reference.rlib"])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW").run();
    rfs::write("prepass_driver.rs", r#"
fn main() {
    use prepass_reference::*;
    unsafe {
        println!("{} {} {} {} {}", dead_half_write(0usize as *mut Half),
            dead_union_write(0usize as *mut WithUnion),
            rejected_before_valid(0usize as *mut WithUnion),
            valid_before_rejected(0usize as *mut WithUnion), prepass_runtime());
    }
}
"#);
    let binary = bin_name("prepass_driver");
    cmd(rustc_path()).args(flags).args(["prepass_driver.rs", "--extern",
        "prepass_reference=libprepass_reference.rlib", "-o", &binary])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW").run();
    assert_eq!(run(&binary).stdout_utf8().trim(), "7 9 604 604 1224");
}

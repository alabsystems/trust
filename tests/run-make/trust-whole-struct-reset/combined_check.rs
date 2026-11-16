use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json};

pub fn check() {
    let coverage = super::compile("combined.rs", "combined", "combined-ir", None);
    super::no_proof(&coverage);
    for (name, expected) in [
        ("bodies", 1), ("lowered", 1), ("spliced", 1),
        ("initializer_bodies", 0), ("symbolic", 0), ("unsupported", 0),
    ] {
        assert_eq!(coverage["totals"][name], expected, "{name}");
    }
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 1);
    let row = super::row(&coverage, "combined_type_registration");
    assert_eq!(row["kind"], "fn");
    assert!(row["unsupported"].as_array().unwrap().is_empty());
    let text = rfs::read_to_string("combined-ir/combined.trust-ir.txt");
    let declarations: Vec<_> = text.lines().filter(|line| line.starts_with("struct @Cell {")).collect();
    assert_eq!(declarations.len(), 1, "one shared complete Cell descriptor");
    let sid = declarations[0].rsplit_once("id=").unwrap().1;
    let body = super::body(&text, "combined_type_registration");
    assert!(body.contains(&format!("store struct.{sid} ")), "{body}");
    assert!(body.contains(&format!("extractelement struct.{sid} ")), "{body}");
    assert!(body.contains(&format!("insertfield struct.{sid} ")), "{body}");

    rfs::create_dir("combined-shadow");
    assert_eq!(coverage, super::compile("combined.rs", "combined", "combined-shadow-ir", Some("combined-shadow")));
    assert_eq!(rfs::read("combined-ir/combined.trust-ir.bin"),
        rfs::read("combined-shadow-ir/combined.trust-ir.bin"));
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "combined-shadow/combined.contract-carry.shadow.json",
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
    assert_eq!(values[0]["display_path"], "combined_type_registration");
    assert_eq!(values[0]["function"], row["func_id"]);
    assert_eq!(values[0]["value"], serde_json::json!({"raw": "21123868"}));

    let flags = ["--edition=2021", "-Copt-level=0", "-Coverflow-checks=on",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=off", "-Ztrust-ir-flip=no", "-Zcodegen-backend=llvm"];
    cmd(rustc_path()).args(flags).args(["combined.rs", "--crate-type=rlib",
        "--crate-name=combined_reference", "-o", "libcombined_reference.rlib"])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW").run();
    rfs::write("combined_driver.rs", "fn main() { println!(\"{}\", combined_reference::combined_type_registration()); }\n");
    let binary = bin_name("combined_driver");
    cmd(rustc_path()).args(flags).args(["combined_driver.rs", "--extern",
        "combined_reference=libcombined_reference.rlib", "-o", &binary])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW").run();
    assert_eq!(run(&binary).stdout_utf8().trim(), "21123868");
}

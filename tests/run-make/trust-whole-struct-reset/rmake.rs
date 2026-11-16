//! Complete aggregate types survive a scalar read followed by whole replacement.

use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json};

mod combined_check;
mod prepass_check;

const EXPECTED: [(&str, u64); 5] = [
    ("reset_and_observe", 905),
    ("effectful_rhs", 230503),
    ("repeated_reset", 906),
    ("alias_observes_replacement", 170905),
    ("borrowed_field_reset", 170905),
];

fn compile(file: &str, name: &str, directory: &str, shadow: Option<&str>) -> serde_json::Value {
    let mut compiler = cmd(rustc_path());
    compiler.args([
        file,
        "--edition=2021",
        "--crate-type=lib",
        "--crate-name",
        name,
        "--emit=mir",
        "-Copt-level=0",
        "-Coverflow-checks=on",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no",
        &format!("-Ztrust-dump=ir:{directory}"),
        "-o",
        &format!("{name}.mir"),
    ]);
    if let Some(directory) = shadow {
        compiler.env("TRUST_CONTRACT_CARRY_SHADOW", directory);
    } else {
        compiler.env_remove("TRUST_CONTRACT_CARRY_SHADOW");
    }
    let output = compiler.run();
    assert!(!output.stderr_utf8().contains("semantic finalization failed"));
    serde_json::from_slice(&rfs::read(format!("{directory}/{name}.coverage.json"))).unwrap()
}

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows: Vec<_> = coverage["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["def_path"] == name)
        .collect();
    assert_eq!(rows.len(), 1, "one source row for {name}");
    rows[0]
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let header = format!("; #display-path: {name:?}\n");
    assert_eq!(text.matches(&header).count(), 1, "one body for {name}");
    text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0
}

fn no_proof(coverage: &serde_json::Value) {
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
}

fn check_container(coverage: &serde_json::Value, text: &str, ty: &str, function: &str) {
    let declarations: Vec<_> = text
        .lines()
        .filter(|line| line.starts_with(&format!("struct @{ty} {{")))
        .filter(|line| line.contains("values: struct."))
        .collect();
    assert_eq!(declarations.len(), 1, "one complete {ty} layout");
    let id = declarations[0].rsplit_once("id=").unwrap().1;
    let reset = body(text, function);
    assert!(reset.contains(&format!("load struct.{id},")), "{reset}");
    let callee = format!("<{ty} as std::default::Default>::default");
    let callee = row(coverage, &callee)["func_id"].as_u64().unwrap();
    let call = format!("call @func.{callee}()");
    let calls: Vec<_> = reset.lines().filter(|line| line.contains(&call)).collect();
    assert_eq!(calls.len(), 1, "one Default call: {reset}");
    let result = calls[0].trim().split_once(" = ").unwrap().0;
    assert!(reset.contains(&format!("store struct.{id} {result}, ptr %0")), "{reset}");
    let source = row(coverage, function);
    assert_eq!(source["lowered"], true);
    assert_eq!(source["spliced"], true);
    assert!(source["unsupported"].as_array().unwrap().is_empty());
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let containers = compile("containers.rs", "containers", "containers-ir", None);
    no_proof(&containers);
    assert_eq!(containers["bodies"].as_array().unwrap().len(), 8);
    assert_eq!(containers["totals"]["bodies"], 8);
    assert_eq!(containers["totals"]["lowered"], 8);
    assert_eq!(containers["totals"]["spliced"], 8);
    assert_eq!(containers["totals"]["symbolic"], 0);
    let text = rfs::read_to_string("containers-ir/containers.trust-ir.txt");
    check_container(&containers, &text, "VecCache", "vec_reset");
    check_container(&containers, &text, "MapCache", "map_reset");

    let refused = compile("refusals.rs", "refusals", "refusals-ir", None);
    no_proof(&refused);
    assert_eq!(refused["totals"]["bodies"], 2);
    assert_eq!(refused["totals"]["lowered"], 0);
    assert_eq!(refused["totals"]["spliced"], 0);
    for name in ["fat_replacement", "union_replacement"] {
        let source = row(&refused, name);
        assert_eq!(source["lowered"], false);
        assert_eq!(source["spliced"], false);
        assert!(source["unsupported"].as_array().unwrap().iter().any(|entry| {
            entry[0] == "Assign(whole struct incomplete type)" && entry[1] == 1
        }));
    }

    let boundaries = compile("boundaries.rs", "boundaries", "boundaries-ir", None);
    no_proof(&boundaries);
    assert_eq!(boundaries["totals"]["bodies"], 2);
    assert_eq!(boundaries["totals"]["lowered"], 1);
    assert_eq!(boundaries["totals"]["spliced"], 1);
    assert_eq!(boundaries["totals"]["symbolic"], 1);
    let dead = row(&boundaries, "no_store");
    assert_eq!(dead["lowered"], true);
    assert_eq!(dead["spliced"], true);
    assert!(dead["unsupported"].as_array().unwrap().is_empty());
    let generic = row(&boundaries, "generic_replacement");
    assert_eq!(generic["lowered"], false);
    assert_eq!(generic["spliced"], false);
    assert!(generic["unsupported"].as_array().unwrap().iter().any(|entry| {
        entry[0] == "Assign(whole struct incomplete type)" && entry[1] == 1
    }));
    let dead_text = rfs::read_to_string("boundaries-ir/boundaries.trust-ir.txt");
    let dead_body = body(&dead_text, "no_store");
    assert!(!dead_body.contains("store "), "{dead_body}");

    let runtime = compile("runtime.rs", "runtime", "runtime-ir", None);
    no_proof(&runtime);
    assert_eq!(runtime["totals"]["bodies"], 10);
    assert_eq!(runtime["totals"]["lowered"], 10);
    assert_eq!(runtime["totals"]["spliced"], 10);
    assert_eq!(runtime["totals"]["symbolic"], 0);
    rfs::create_dir("runtime-shadow");
    assert_eq!(runtime, compile("runtime.rs", "runtime", "runtime-shadow-ir", Some("runtime-shadow")));
    assert_eq!(
        rfs::read("runtime-ir/runtime.trust-ir.bin"),
        rfs::read("runtime-shadow-ir/runtime.trust-ir.bin")
    );
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "runtime-shadow/runtime.contract-carry.shadow.json",
    ))
    .unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for name in [
        "duplicate_registrations",
        "install_errors",
        "validate_module",
        "validate_module_with_authority",
        "validate_linked_module",
        "text_losses",
        "staged_rung_errors",
        "rows",
        "summaries",
    ] {
        assert!(shadow[name].as_array().unwrap().is_empty(), "{name}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    assert_eq!(interpreted.len(), EXPECTED.len());
    let native = llvm_reference();
    for ((name, expected), native) in EXPECTED.iter().zip(native) {
        let function = row(&runtime, name)["func_id"].as_u64().unwrap();
        let matches: Vec<_> = interpreted.iter().filter(|row| row["display_path"] == *name).collect();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0]["function"].as_u64(), Some(function));
        assert_eq!(interpreted.iter().filter(|row| row["function"] == function).count(), 1);
        assert_eq!(matches[0]["value"], serde_json::json!({"raw": expected.to_string()}));
        assert_eq!(*expected, native);
        eprintln!("whole reset {name}: trust-ir={expected} llvm={native}");
    }
    combined_check::check();
    prepass_check::check();
}

fn llvm_reference() -> Vec<u64> {
    let flags = [
        "--edition=2021",
        "-Copt-level=0",
        "-Coverflow-checks=on",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off",
        "-Ztrust-ir-flip=no",
        "-Zcodegen-backend=llvm",
    ];
    cmd(rustc_path())
        .args(flags)
        .args(["runtime.rs", "--crate-type=rlib", "--crate-name=reference", "-o", "libreference.rlib"])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW")
        .run();
    let calls: String = EXPECTED
        .iter()
        .map(|(name, _)| format!("println!(\"{name}={{}}\", reference::{name}());\n"))
        .collect();
    rfs::write("driver.rs", format!("fn main() {{ {calls} }}\n"));
    let binary = bin_name("driver");
    cmd(rustc_path())
        .args(flags)
        .args(["driver.rs", "--extern", "reference=libreference.rlib", "-o", &binary])
        .env_remove("TRUST_CONTRACT_CARRY_SHADOW")
        .run();
    let output = run(&binary).stdout_utf8();
    assert_eq!(output.lines().count(), EXPECTED.len());
    EXPECTED
        .iter()
        .zip(output.lines())
        .map(|((name, expected), line)| {
            let (actual_name, actual) = line.split_once('=').unwrap();
            assert_eq!(actual_name, *name);
            let actual = actual.parse::<u64>().unwrap();
            assert_eq!(actual, *expected);
            actual
        })
        .collect()
}

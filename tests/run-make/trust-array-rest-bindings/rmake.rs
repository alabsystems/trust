//! By-value array rests retain their own storage and all positional bindings.

use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json};

const SHADOW: &str = "TRUST_CONTRACT_CARRY_SHADOW";
const EXPECTED: [(&str, u64); 4] = [
    ("constant_prefix_and_len", 2055),
    ("constant_prefix_suffix_and_len", 2061),
    ("runtime_repeat_once", 42487),
    ("borrowed_rest_copy", 780173),
];
const INITIALIZERS: [(&str, u64); 5] = [
    ("constant_prefix_and_len::{constant#0}", 2049),
    ("constant_prefix_suffix_and_len::{constant#0}", 2049),
    ("runtime_repeat_once::{constant#0}", 2049),
    ("borrowed_rest_copy::{constant#0}", 4),
    ("pointer_rest_refused::{constant#0}", 3),
];

fn compile(directory: &str, shadow: Option<&str>) -> serde_json::Value {
    let mut compiler = cmd(rustc_path());
    compiler.args([
        "array_rest.rs",
        "--edition=2021",
        "--crate-type=lib",
        "--crate-name=array_rest",
        "--emit=mir",
        "-Coverflow-checks=on",
        "-Copt-level=0",
        "-Zthreads=1",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no",
        &format!("-Ztrust-dump=ir:{directory}"),
        "-o",
        &format!("{directory}.mir"),
    ]);
    match shadow {
        Some(path) => {
            compiler.env(SHADOW, path);
        }
        None => {
            compiler.env_remove(SHADOW);
        }
    }
    let output = compiler.run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    serde_json::from_slice(&rfs::read(format!("{directory}/array_rest.coverage.json"))).unwrap()
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

fn assert_execution(
    interpreted: &[serde_json::Value],
    source_row: &serde_json::Value,
    display_path: &str,
    expected: u64,
) {
    let function = source_row["func_id"].as_u64().unwrap();
    let found: Vec<_> = interpreted.iter().filter(|r| r["display_path"] == display_path).collect();
    assert_eq!(found.len(), 1, "one execution for {display_path}");
    assert_eq!(found[0]["function"].as_u64(), Some(function));
    assert_eq!(
        interpreted.iter().filter(|r| r["function"].as_u64() == Some(function)).count(),
        1,
        "unique function identity for {display_path}"
    );
    assert_eq!(found[0]["value"], serde_json::json!({"raw": expected.to_string()}));
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let coverage = compile("array-rest-ir", None);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 10);
    assert_eq!(coverage["totals"]["bodies"], 10);
    assert_eq!(coverage["totals"]["initializer_bodies"], 5);
    assert_eq!(coverage["totals"]["lowered"], 9);
    assert_eq!(coverage["totals"]["spliced"], 9);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let text = rfs::read_to_string("array-rest-ir/array_rest.trust-ir.txt");
    for (name, _) in EXPECTED {
        let row = row(&coverage, name);
        assert_eq!(row["kind"], "fn");
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty());
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        assert!(!body.contains("undef"));
        // N=2049 must not turn the compact repeat or rest into per-element IR.
        assert!(body.lines().count() < 160, "rest materialized by element: {body}");
    }
    let refused = row(&coverage, "pointer_rest_refused");
    assert_eq!(refused["lowered"], false);
    assert_eq!(refused["spliced"], false);
    assert_eq!(
        refused["unsupported"],
        serde_json::json!([
            ["Call(unsupported arg)", 1],
            ["Slice(non-scalar element)", 2],
            ["SliceLen(unsupported receiver)", 1],
        ])
    );

    rfs::create_dir("array-rest-shadow");
    assert_eq!(coverage, compile("array-rest-shadow-ir", Some("array-rest-shadow")));
    let binary = rfs::read("array-rest-ir/array_rest.trust-ir.bin");
    assert!(!binary.is_empty());
    assert_eq!(binary, rfs::read("array-rest-shadow-ir/array_rest.trust-ir.bin"));
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "array-rest-shadow/array_rest.contract-carry.shadow.json",
    ))
    .unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for key in [
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
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    // The shadow interpreter executes the five array-length initializers too.
    // Account for every row, including the initializer of the refused function.
    assert_eq!(interpreted.len(), EXPECTED.len() + INITIALIZERS.len());
    for (name, expected) in INITIALIZERS {
        let initializer = row(&coverage, name);
        assert_eq!(initializer["kind"], "const-init");
        assert_eq!(initializer["lowered"], true);
        assert_eq!(initializer["spliced"], true);
        assert_eq!(initializer["symbolic"], false);
        assert!(initializer["unsupported"].as_array().unwrap().is_empty());
        assert_execution(interpreted, initializer, &format!("{name}::{{const-init}}"), expected);
    }
    let native = llvm_reference();
    for ((name, expected), native) in EXPECTED.iter().zip(native) {
        assert_execution(interpreted, row(&coverage, name), name, *expected);
        assert_eq!(*expected, native);
        eprintln!("array rest {name}: trust-ir={expected} llvm={native}");
    }
}

fn llvm_reference() -> Vec<u64> {
    let flags = [
        "--edition=2021",
        "-Coverflow-checks=on",
        "-Copt-level=0",
        "-Zthreads=1",
        "-Zcodegen-backend=llvm",
        "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off",
        "-Ztrust-ir-flip=no",
    ];
    cmd(rustc_path())
        .args(flags)
        .args(["array_rest.rs", "--crate-type=rlib", "--crate-name=array_rest_reference", "-o", "libarray_rest_reference.rlib"])
        .env_remove(SHADOW)
        .run();
    let calls: String = EXPECTED
        .iter()
        .map(|(name, _)| format!("println!(\"{name}={{}}\", array_rest_reference::{name}());\n"))
        .collect();
    rfs::write("array_rest_driver.rs", format!("fn main() {{ {calls} }}\n"));
    let binary = bin_name("array_rest_driver");
    cmd(rustc_path())
        .args(flags)
        .args(["array_rest_driver.rs", "--extern", "array_rest_reference=libarray_rest_reference.rlib", "-o", &binary])
        .env_remove(SHADOW)
        .run();
    let output = run(&binary).stdout_utf8();
    assert_eq!(output.lines().count(), EXPECTED.len());
    EXPECTED
        .iter()
        .zip(output.lines())
        .map(|((name, expected), line)| {
            let (found, value) = line.split_once('=').unwrap();
            assert_eq!(found, *name);
            let value = value.parse::<u64>().unwrap();
            assert_eq!(value, *expected);
            value
        })
        .collect()
}

//! Retain the complete projected-place census; execute only emitted reference controls.

use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json};

mod indexed_field;

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    cmd(rustc_path())
        .args([
            "projected_places.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=array_projected_actual",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:array-ir",
            "-o",
            "projected.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("array-ir/array_projected_actual.coverage.json"))
            .unwrap();
    let names = [
        "reseat_deref_pointee",
        "reseat_deref_pointee::{constant#0}",
        "reseat_deref_pointee::{constant#1}",
        "reseat_tuple_field",
        "reseat_tuple_field::{constant#0}",
        "reseat_tuple_field::{constant#1}",
        "change_pointer_not_pointee",
        "change_pointer_not_pointee::{constant#0}",
        "change_pointer_not_pointee::{constant#1}",
        "make_array",
        "make_array::{constant#0}",
        "call_base_runs_once",
    ];
    let rows = report["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    assert_eq!(report["totals"]["bodies"], 12);
    // RE-PINNED 2026-09-16, 11 -> 10. One body here lowered "fully" only because a
    // reference-typed call argument whose borrow could not become a pointer was
    // carried into the call AS A VALUE. That call edge does not type-check, and it
    // was invisible only while declarations wore the v41-outlawed
    // unknown-signature spelling, which made the argument/parameter comparison run
    // zero times. The carrier is now refused for a reference-typed argument, so
    // that body reports its real refusal instead of a false full-lowering. The
    // trade is deliberate and measured: three ui/trust fixtures whose WHOLE MODULE
    // was refused (`CallArgTypeMismatch`) now lower, against one body's localized
    // coverage here and one in `trust_ir_lower_box_deref`.
    // The complete borrow prepass now gives `count` its real slot even when
    // its only mutable borrow is inside the index base. The signed call uses
    // that pointer, so call_base_runs_once now lowers with its full bounds row.
    assert_eq!(report["totals"]["lowered"], 11);
    assert_eq!(report["totals"]["spliced"], 11);
    assert_eq!(report["totals"]["symbolic"], 0);
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate source body {name}");
        let row = found[0];
        assert_eq!(row["symbolic"], false);
        match name {
            "reseat_tuple_field" => {
                assert_eq!(row["lowered"], false);
                assert_eq!(row["spliced"], false);
                assert!(!row["unsupported"].as_array().unwrap().is_empty());
            }
            _ => {
                assert_eq!(row["lowered"], true);
                assert_eq!(row["spliced"], true);
                assert!(row["unsupported"].as_array().unwrap().is_empty());
            }
        }
    }
    let text = rfs::read_to_string("array-ir/array_projected_actual.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|line| line.starts_with("obligation ")).collect();
    assert_eq!(obligations.len(), 3);
    assert!(
        obligations.iter().all(|l| l.contains(" bounds_check pending ") && l.contains(" site f"))
    );
    for name in ["reseat_deref_pointee", "change_pointer_not_pointee"] {
        // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
        let header = format!("; #display-path: {name:?}\n");
        assert_eq!(text.matches(&header).count(), 1);
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        let loads: Vec<_> = body.match_indices("load ").map(|(i, _)| i).collect();
        let stores: Vec<_> = body.match_indices("store ").map(|(i, _)| i).collect();
        assert_eq!(loads.len(), 1);
        assert_eq!(stores.len(), 2);
        assert_eq!(body.matches("assert ").count(), 1);
        assert_eq!(body.matches("#proof: in_bounds").count(), 1);
        let assertion = body.find("assert ").unwrap();
        assert!(stores[1] < assertion && assertion < loads[0]);
        assert!(loads[0] < body.find("extractelement u8 ").unwrap());
    }
    let header = "; #display-path: \"call_base_runs_once\"\n";
    let body = text.split_once(header).unwrap().1.split_once("\n}\n").unwrap().0;
    let code: Vec<_> = body.lines()
        .map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let slot = code.iter().find_map(|line| line.split_once(" = alloca usize").map(|x| x.0))
        .expect("count has real storage");
    let make = rows.iter().find(|row| row["def_path"] == "make_array").unwrap()["func_id"]
        .as_u64().expect("make_array has a signed emitted body");
    let needle = format!("call @func.{make}({slot})");
    let calls: Vec<_> = code.iter().enumerate().filter(|(_, line)| line.contains(&needle)).collect();
    assert_eq!(calls.len(), 1, "base call executes exactly once with count's address");
    let read = code.iter().position(|line| line.contains(" = load usize, ptr ")
        && line.ends_with(slot)).expect("index reads the count changed by the call");
    let reset = code.iter().rposition(|line| line.starts_with("store usize ")
        && line.ends_with(&format!(", ptr {slot}"))).unwrap();
    let bounds = code.iter().position(|line| line.starts_with("assert ")).unwrap();
    let extract = code.iter().position(|line| line.contains("extractelement u8 ")).unwrap();
    assert!(calls[0].0 < read && read < reset && reset < bounds && bounds < extract,
        "call, index effects, bounds and element read preserve source order: {body}");
    check_indexed_assignment_order();
    indexed_field::check();
}

const SHADOW_ENV: &str = "TRUST_CONTRACT_CARRY_SHADOW";

fn compile_indexed(directory: &str, shadow: Option<&str>) -> serde_json::Value {
    let mut compiler = cmd(rustc_path());
    compiler.args([
        "indexed_assign.rs", "--edition=2021", "--crate-type=lib",
        "--crate-name=indexed_assign", "--emit=mir", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no", &format!("-Ztrust-dump=ir:{directory}"),
        "-o", &format!("{directory}.mir"),
    ]);
    match shadow {
        Some(path) => { compiler.env(SHADOW_ENV, path); }
        None => { compiler.env_remove(SHADOW_ENV); }
    }
    let output = compiler.run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    serde_json::from_slice(&rfs::read(format!("{directory}/indexed_assign.coverage.json"))).unwrap()
}

fn indexed_row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(rows.len(), 1, "one source row for {name}");
    rows[0]
}

fn indexed_body<'a>(text: &'a str, name: &str) -> &'a str {
    let header = format!("; #display-path: {name:?}\n");
    assert_eq!(text.matches(&header).count(), 1, "one published body for {name}");
    text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0
}

fn check_indexed_assignment_order() {
    let coverage = compile_indexed("indexed-ir", None);
    let expected = [
        ("reference_index_order", 21u64),
        ("reference_index_return", 9),
        ("reference_bounds_return", 9),
        ("ssa_fallback_once", 21),
        ("field_fallback_once", 1),
        ("reference_retarget", 7),
        ("index_return_after_rhs", 11),
        ("nested_rhs_once", 123),
        ("nested_index_once", 123),
    ];
    let initializers = [
        "Holder::items::{constant#0}",
        "reference_index_order::{constant#0}",
        "reference_index_return::{constant#0}",
        "reference_bounds_return::{constant#0}",
        "ssa_fallback_once::{constant#0}",
        "reference_retarget::{constant#0}",
        "reference_retarget::{constant#1}",
        "index_return_after_rhs::{constant#0}",
        "nested_rhs_once::{constant#0}",
        "nested_rhs_once::{constant#1}",
        "nested_index_once::{constant#0}",
        "nested_index_once::{constant#1}",
    ];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 22);
    assert_eq!(coverage["totals"]["bodies"], 22);
    assert_eq!(coverage["totals"]["initializer_bodies"], 12);
    assert_eq!(coverage["totals"]["lowered"], 21);
    assert_eq!(coverage["totals"]["spliced"], 21);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    assert_eq!(coverage["direct_obligation_capability"], "obligation-bearing-pending-v2");
    let text = rfs::read_to_string("indexed-ir/indexed_assign.trust-ir.txt");
    for name in expected.iter().map(|entry| entry.0).chain(initializers) {
        let row = indexed_row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let path = if name.ends_with('}') { format!("{name}::{{const-init}}") } else { name.into() };
        assert!(!indexed_body(&text, &path).contains("undef"));
    }
    // An unsupported local aggregate borrow stays refused. This is not an
    // opportunity to narrow or widen the existing storage/provenance lanes.
    let refused = indexed_row(&coverage, "field_index_order");
    assert_eq!(refused["lowered"], false);
    assert_eq!(refused["spliced"], false);
    assert_eq!(refused["symbolic"], false);
    assert_eq!(refused["unsupported"], serde_json::json!([
        ["Assign(non-local place)", 1], ["Borrow(&mut slot missing)", 1],
        ["Promote(non-scalar &mut local)", 1],
    ]));
    for name in initializers {
        let row = indexed_row(&coverage, name);
        assert_eq!(row["kind"], "const-init");
        assert_eq!(row["instr_count"], 2);
        let path = format!("{name}::{{const-init}}");
        let code: Vec<_> = indexed_body(&text, &path).lines()
            .map(|line| line.split(" ;").next().unwrap().trim())
            .filter(|line| !line.is_empty() && !line.starts_with(';') && !line.ends_with(':'))
            .collect();
        assert_eq!(code, ["%0 = const usize 1", "ret %0"]);
    }
    for name in ["reference_index_return", "reference_bounds_return", "index_return_after_rhs"] {
        let body = indexed_body(&text, name);
        assert!(!body.contains("bounds_check"), "divergence must precede bounds: {body}");
        assert!(!body.contains("gep "), "divergence must precede destination address: {body}");
        assert!(!body.contains("store u32 "), "no element store after divergence: {body}");
    }

    rfs::create_dir("indexed-shadow");
    let shadow_coverage = compile_indexed("indexed-shadow-ir", Some("indexed-shadow"));
    assert_eq!(coverage, shadow_coverage, "shadow must not change coverage");
    let published = rfs::read("indexed-ir/indexed_assign.trust-ir.bin");
    assert!(!published.is_empty());
    assert_eq!(published, rfs::read("indexed-shadow-ir/indexed_assign.trust-ir.bin"),
        "shadow must execute the unchanged published module");
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "indexed-shadow/indexed_assign.contract-carry.shadow.json"
    )).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["crate"], "indexed_assign");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for key in [
        "duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries",
    ] {
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    assert_eq!(interpreted.len(), 21, "all published noarg bodies execute");
    let native = indexed_llvm_reference(&expected);
    for ((name, expected_value), native_value) in expected.iter().zip(native) {
        let row = indexed_row(&coverage, name);
        assert_eq!(row["kind"], "fn");
        let function = row["func_id"].as_u64().unwrap();
        let found: Vec<_> = interpreted.iter().filter(|value| value["display_path"] == *name).collect();
        assert_eq!(found.len(), 1, "one actual execution of {name}");
        assert_eq!(found[0]["function"].as_u64(), Some(function));
        assert_eq!(interpreted.iter().filter(|value| value["function"].as_u64() == Some(function)).count(), 1);
        let value = found[0]["value"].as_object().unwrap();
        assert_eq!(value.len(), 1, "successful raw return, not an interpreter error: {found:?}");
        let actual = value["raw"].as_str().unwrap().parse::<u64>().unwrap();
        assert_eq!(actual, *expected_value, "published IR return for {name}");
        assert_eq!(actual, native_value, "published IR versus independent LLVM for {name}");
        eprintln!("indexed assignment {name}: trust-ir={actual} llvm={native_value}");
    }
}

fn indexed_llvm_reference(expected: &[(&str, u64)]) -> Vec<u64> {
    // Compile both reference artifacts with lowering disabled; never link a
    // candidate-lowered library into the independent LLVM executable.
    let flags = [
        "--edition=2021", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Zcodegen-backend=llvm", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
        "-Ztrust-ir-flip=no",
    ];
    cmd(rustc_path()).args(flags).args([
        "indexed_assign.rs", "--crate-type=rlib", "--crate-name=indexed_reference",
        "-o", "libindexed_reference.rlib",
    ]).env_remove(SHADOW_ENV).run();
    let calls: String = expected.iter().map(|(name, _)| {
        format!("    println!(\"{name}={{}}\", indexed_reference::{name}());\n")
    }).collect();
    rfs::write("indexed_driver.rs", format!("fn main() {{\n{calls}}}\n"));
    let executable = bin_name("indexed_driver");
    cmd(rustc_path()).args(flags).args([
        "indexed_driver.rs", "--extern", "indexed_reference=libindexed_reference.rlib",
        "-o", &executable,
    ]).env_remove(SHADOW_ENV).run();
    let output = run(&executable).stdout_utf8();
    assert_eq!(output.lines().count(), expected.len(), "{output}");
    expected.iter().zip(output.lines()).map(|((name, expected_value), line)| {
        let (actual_name, raw) = line.split_once('=').unwrap();
        assert_eq!(actual_name, *name);
        let value = raw.parse::<u64>().unwrap();
        assert_eq!(value, *expected_value, "LLVM reference for {name}");
        value
    }).collect()
}

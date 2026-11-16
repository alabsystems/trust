use std::collections::BTreeMap;

use run_make_support::{bin_name, cmd, rfs, run, run_fail, rustc_path, serde_json};

const SHADOW: &str = "TRUST_CONTRACT_CARRY_SHADOW";
const EXPECTED: [(&str, u64); 9] = [
    ("field_index_effectful_order", 211734),
    ("rhs_replaces_array", 5978),
    ("index_replaces_array", 5978),
    ("nested_index_assignment", 1231738),
    ("loop_field_update", 2244),
    ("float_fields_update", 1),
    ("rhs_return_before_bounds", 29),
    ("index_return_after_rhs", 11),
    // Retain the original fixture's name while admitting its nested sibling.
    ("non_scalar_sibling_refused", 127),
];

fn compile(source: &str, crate_name: &str, directory: &str, shadow: Option<&str>) -> serde_json::Value {
    let mut compiler = cmd(rustc_path());
    compiler.args([
        source, "--edition=2021", "--crate-type=lib",
        &format!("--crate-name={crate_name}"), "--emit=mir", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no", &format!("-Ztrust-dump=ir:{directory}"),
        "-o", &format!("{directory}.mir"),
    ]);
    match shadow {
        Some(path) => { compiler.env(SHADOW, path); }
        None => { compiler.env_remove(SHADOW); }
    }
    let output = compiler.run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    serde_json::from_slice(&rfs::read(format!("{directory}/{crate_name}.coverage.json")))
        .unwrap()
}

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let matches: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(matches.len(), 1, "one source row for {name}");
    matches[0]
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let header = format!("; #display-path: {name:?}\n");
    assert_eq!(text.matches(&header).count(), 1, "one published body for {name}");
    text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0
}

// Check the actual update chain, not only the presence of aggregate operations
// also used to build the initial array. Both projections must use the same
// post-operand array and index, and the updated field must be descriptor field 1.
fn updates(body: &str) -> usize {
    let lines: Vec<_> = body.lines()
        .map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let definitions: BTreeMap<_, _> = lines.iter().filter_map(|line| line.split_once(" = "))
        .collect();
    let mut updates = 0;
    for (position, line) in lines.iter().enumerate() {
        let Some((_, operation)) = line.split_once(" = ") else { continue };
        let Some(rest) = operation.strip_prefix("insertelement ") else { continue };
        let (array_ty, operands) = rest.split_once("] ").unwrap();
        let (_, len) = array_ty.rsplit_once(" x ").unwrap();
        let operands: Vec<_> = operands.split(", ").collect();
        assert_eq!(operands.len(), 3);
        let Some(field) = definitions.get(operands[2]) else { continue };
        let Some(field) = field.strip_prefix("insertfield ") else { continue };
        let (_, field) = field.split_once(' ').unwrap();
        let field: Vec<_> = field.split(", ").collect();
        assert_eq!(field.len(), 3);
        let Some(element) = definitions.get(field[0]) else { continue };
        let Some(element) = element.strip_prefix("extractelement ") else { continue };
        let (_, element) = element.split_once(' ').unwrap();
        let element: Vec<_> = element.split(", ").collect();
        assert_eq!(field[1], "1", "write the nonzero-offset field");
        assert_eq!(element, operands[..2], "same live array and index for read/update");
        let extract = lines.iter().position(|line| line.starts_with(&format!("{} = ", field[0])))
            .unwrap();
        assert!(extract < position);
        assert!(lines[..extract].iter().any(|line| {
            let Some(assertion) = line.strip_prefix("assert ") else { return false };
            let Some((condition, operands)) = assertion.split_once(", bounds_check ") else {
                return false;
            };
            let Some((checked_index, length)) = operands.split_once(", ") else { return false };
            checked_index == element[1]
                && definitions.get(condition)
                    == Some(&format!("icmp ult usize {checked_index}, {length}").as_str())
                && definitions.get(length) == Some(&format!("const usize {len}").as_str())
        }),
            "bounds assertion precedes the projected read: {body}");
        updates += 1;
    }
    updates
}

pub fn check() {
    let coverage = compile("indexed_field_assign.rs", "indexed_field_assign", "indexed-field-ir", None);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 15);
    assert_eq!(coverage["totals"]["bodies"], 15);
    assert_eq!(coverage["totals"]["initializer_bodies"], 0);
    assert_eq!(coverage["totals"]["lowered"], 12);
    assert_eq!(coverage["totals"]["spliced"], 12);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    assert_eq!(coverage["direct_obligation_capability"], "obligation-bearing-pending-v2");
    let text = rfs::read_to_string("indexed-field-ir/indexed_field_assign.trust-ir.txt");
    for name in EXPECTED.iter().map(|entry| entry.0)
        .chain(["bounds_panic", "bounds_panic_predecessor", "<Droppy as std::ops::Drop>::drop"])
    {
        let row = row(&coverage, name);
        assert_eq!(row["kind"], "fn");
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert!(!body(&text, name).contains("undef"));
    }
    for name in ["rhs_borrow_refused", "index_borrow_refused"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false);
        assert_eq!(row["spliced"], false);
        assert_eq!(row["unsupported"], serde_json::json!([
            ["Assign(non-local place)", 1], ["Field(unsupported lhs)", 1],
            ["Index(unsupported base)", 1], ["Promote(non-scalar &mut local)", 1],
            ["VarRef(promoted slot missing)", 1],
        ]));
    }
    for name in ["needs_drop_refused"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false);
        assert_eq!(row["spliced"], false);
        assert_eq!(row["unsupported"], serde_json::json!([["Assign(non-local place)", 1]]));
    }
    for name in ["field_index_effectful_order", "rhs_replaces_array", "index_replaces_array", "loop_field_update"] {
        assert_eq!(updates(body(&text, name)), 1, "one real projected update for {name}");
    }
    assert_eq!(updates(body(&text, "nested_index_assignment")), 2);
    for name in ["rhs_return_before_bounds", "index_return_after_rhs"] {
        let body = body(&text, name);
        assert!(!body.contains("bounds_check"), "divergence precedes bounds: {body}");
        assert_eq!(updates(body), 0, "no projected update after divergence");
    }
    rfs::create_dir("indexed-field-shadow");
    assert_eq!(coverage, compile("indexed_field_assign.rs", "indexed_field_assign",
        "indexed-field-shadow-ir", Some("indexed-field-shadow")));
    let binary = rfs::read("indexed-field-ir/indexed_field_assign.trust-ir.bin");
    assert!(!binary.is_empty());
    assert_eq!(binary, rfs::read("indexed-field-shadow-ir/indexed_field_assign.trust-ir.bin"));
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "indexed-field-shadow/indexed_field_assign.contract-carry.shadow.json"
    )).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["crate"], "indexed_field_assign");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for key in ["duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries"]
    {
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    assert_eq!(interpreted.len(), 11, "nine normal returns and two bounds panics");
    let native = llvm_reference("indexed_field_assign.rs", "indexed_field_reference",
        &EXPECTED, &["bounds_panic", "bounds_panic_predecessor"]);
    for ((name, expected), native) in EXPECTED.iter().zip(native) {
        let function = row(&coverage, name)["func_id"].as_u64().unwrap();
        let found: Vec<_> = interpreted.iter().filter(|value| value["display_path"] == *name).collect();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0]["function"].as_u64(), Some(function));
        assert_eq!(interpreted.iter().filter(|value| value["function"].as_u64() == Some(function)).count(), 1);
        assert_eq!(found[0]["value"], serde_json::json!({"raw": expected.to_string()}));
        assert_eq!(*expected, native);
        eprintln!("indexed field {name}: trust-ir={expected} llvm={native}");
    }
    for name in ["bounds_panic", "bounds_panic_predecessor"] {
        let panic: Vec<_> = interpreted.iter().filter(|value| value["display_path"] == name).collect();
        assert_eq!(panic.len(), 1);
        assert_eq!(panic[0]["function"], row(&coverage, name)["func_id"]);
        assert_eq!(panic[0]["value"], serde_json::json!({"error": "Panic"}));
        let code = body(&text, name);
        assert!(code.contains("bounds_check"));
        assert!(code.contains("unreachable"));
        assert_eq!(updates(code), 0, "no invalid element operations after a known panic");
    }
    check_storage_refusals();
    check_compound();
    check_nested_siblings();
}

fn check_compound() {
    let expected = [
        ("compound_effect_order", 211934),
        ("compound_rhs_replaces_array", 51578),
        ("compound_index_replaces_array", 51578),
        ("compound_nested", 1231942),
        ("compound_loop", 2244),
        ("compound_float", 1),
        ("compound_rhs_return_before_bounds", 29),
        ("compound_index_return_after_rhs", 11),
    ];
    let parameterized = [
        "compound_mixed_shift", "compound_bounds", "compound_checked_add", "compound_divisor",
        "compound_signed_divisor", "compound_bit_ops", "compound_sub_mul_rem",
        "compound_nested_sibling_refused",
    ];
    rfs::create_dir("compound-field-shadow");
    let coverage = compile("indexed_field_compound_assign.rs", "indexed_field_compound",
        "compound-field-ir", Some("compound-field-shadow"));
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 19);
    assert_eq!(coverage["totals"]["bodies"], 19);
    assert_eq!(coverage["totals"]["initializer_bodies"], 0);
    assert_eq!(coverage["totals"]["lowered"], 17);
    assert_eq!(coverage["totals"]["spliced"], 17);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    assert_eq!(coverage["direct_obligation_capability"], "obligation-bearing-pending-v2");
    let text = rfs::read_to_string("compound-field-ir/indexed_field_compound.trust-ir.txt");
    for name in expected.iter().map(|(name, _)| *name)
        .chain(parameterized).chain(["<Droppy as std::ops::Drop>::drop"])
    {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert!(!body(&text, name).contains("undef"));
    }
    for name in ["compound_borrowed_refused", "compound_drop_refused"]
    {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false, "retain storage/layout refusal: {name}: {row}");
        assert_eq!(row["spliced"], false);
        assert!(row["unsupported"].as_array().unwrap().iter()
            .any(|tag| tag[0] == "AssignOp(non-local place)"));
    }
    for name in ["compound_effect_order", "compound_rhs_replaces_array",
        "compound_index_replaces_array", "compound_loop", "compound_mixed_shift",
        "compound_bounds", "compound_checked_add", "compound_divisor", "compound_signed_divisor"]
    {
        assert_eq!(updates(body(&text, name)), 1, "one checked projected update: {name}");
    }
    assert_eq!(updates(body(&text, "compound_nested")), 2);
    assert_eq!(updates(body(&text, "compound_bit_ops")), 4);
    assert_eq!(updates(body(&text, "compound_sub_mul_rem")), 3);
    for name in ["compound_rhs_return_before_bounds", "compound_index_return_after_rhs"] {
        let code = body(&text, name);
        assert!(!code.contains("bounds_check"), "no bounds or update after divergence: {code}");
        assert_eq!(updates(code), 0);
    }
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "compound-field-shadow/indexed_field_compound.contract-carry.shadow.json"
    )).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for key in ["duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries"]
    {
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    assert_eq!(interpreted.len(), expected.len(), "all eight zero-argument executable controls");
    let native = llvm_reference("indexed_field_compound_assign.rs", "compound_field_reference",
        &expected, &[]);
    for ((name, expected), native) in expected.iter().zip(native) {
        let found: Vec<_> = interpreted.iter().filter(|value| value["display_path"] == *name).collect();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0]["function"], row(&coverage, name)["func_id"]);
        assert_eq!(found[0]["value"], serde_json::json!({"raw": expected.to_string()}));
        assert_eq!(*expected, native);
    }
}

fn check_nested_siblings() {
    let expected = [
        ("nested_assignment", 409),
        ("nested_compound_effects", 21_672_000),
        ("nested_tuple_siblings", 1177),
        ("nested_array_siblings", 203),
    ];
    rfs::create_dir("nested-sibling-shadow");
    let coverage = compile("indexed_field_nested_siblings.rs", "indexed_field_nested_siblings",
        "nested-sibling-ir", Some("nested-sibling-shadow"));
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 10);
    assert_eq!(coverage["totals"]["bodies"], 10);
    assert_eq!(coverage["totals"]["initializer_bodies"], 2);
    assert_eq!(coverage["totals"]["lowered"], 7);
    assert_eq!(coverage["totals"]["spliced"], 7);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let text = rfs::read_to_string("nested-sibling-ir/indexed_field_nested_siblings.trust-ir.txt");
    for name in expected.iter().map(|(name, _)| *name) {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false);
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert!(!body(&text, name).contains("undef"));
        assert_eq!(updates(body(&text, name)), 1);
    }
    let initializers = [
        "ArraySibling::before::{constant#0}",
        "ArraySibling::after::{constant#0}",
    ];
    for name in initializers {
        let row = row(&coverage, name);
        assert_eq!(row["kind"], "const-init");
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true);
        assert_eq!(row["symbolic"], false);
        assert!(row["unsupported"].as_array().unwrap().is_empty());
    }
    for name in ["nested_drop_refused", "nested_pointer_refused", "nested_enum_refused"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert_eq!(row["spliced"], false);
        assert!(row["unsupported"].as_array().unwrap().iter()
            .any(|tag| tag[0] == "AssignOp(non-local place)"), "{name}: {row}");
    }
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(
        "nested-sibling-shadow/indexed_field_nested_siblings.contract-carry.shadow.json"
    )).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["published"], true);
    assert_eq!(shadow["binary_round_trip"], true);
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    for key in ["duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries"]
    {
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    assert_eq!(interpreted.len(), expected.len() + initializers.len(),
        "all nested-value and type-length initializer executions");
    let native = llvm_reference("indexed_field_nested_siblings.rs", "nested_sibling_reference",
        &expected, &[]);
    for ((name, expected), native) in expected.iter().zip(native) {
        let found: Vec<_> = interpreted.iter().filter(|value| value["display_path"] == *name).collect();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0]["function"], row(&coverage, name)["func_id"]);
        assert_eq!(found[0]["value"], serde_json::json!({"raw": expected.to_string()}));
        assert_eq!(*expected, native);
    }
    for name in initializers {
        let display = format!("{name}::{{const-init}}");
        let found: Vec<_> = interpreted.iter()
            .filter(|value| value["display_path"] == display).collect();
        assert_eq!(found.len(), 1, "one exact initializer execution: {display}");
        assert_eq!(found[0]["function"], row(&coverage, name)["func_id"]);
        assert_eq!(found[0]["value"], serde_json::json!({"raw": "2"}));
    }
}

fn check_storage_refusals() {
    let expected = [
        ("rhs_mut_reseat", 3132417), ("index_mut_reseat", 3132417),
        ("rhs_mut_field", 3112217), ("index_mut_field", 3112217),
        ("rhs_mut_loan_read", 1112222), ("shared_identity_then_store", 11112217),
    ];
    let coverage = compile("indexed_field_storage.rs", "indexed_field_storage",
        "indexed-field-storage-ir", None);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 8);
    assert_eq!(coverage["totals"]["bodies"], 8);
    assert_eq!(coverage["totals"]["initializer_bodies"], 2);
    assert_eq!(coverage["totals"]["lowered"], 2);
    assert_eq!(coverage["totals"]["spliced"], 2);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for (name, _) in expected {
        let row = row(&coverage, name);
        assert_eq!(row["kind"], "fn");
        assert_eq!(row["lowered"], false);
        assert_eq!(row["spliced"], false);
        let unsupported = if name == "shared_identity_then_store" {
            serde_json::json!([
                ["Assign(non-local place)", 1], ["Borrow(shared local lacks stable storage)", 2],
                ["Promote(non-scalar &mut local)", 1], ["VarRef(unbound)", 1],
            ])
        } else {
            serde_json::json!([
                ["Assign(non-local place)", 1], ["Field(unsupported lhs)", 1],
                ["Index(unsupported base)", 1], ["Promote(non-scalar &mut local)", 1],
                ["VarRef(promoted slot missing)", 1],
            ])
        };
        assert_eq!(row["unsupported"], unsupported, "{name}: {row}");
    }
    for name in ["shared_identity_then_store::{constant#0}", "shared_identity_then_store::{constant#1}"] {
        let row = row(&coverage, name);
        assert_eq!(row["kind"], "const-init");
        assert_eq!(row["lowered"], true);
        assert_eq!(row["spliced"], true);
        assert!(row["unsupported"].as_array().unwrap().is_empty());
    }
    // The six functions stay refused; these native values bind the test's
    // intended Rust semantics without claiming a Trust execution for them.
    llvm_reference("indexed_field_storage.rs", "indexed_field_storage_reference", &expected, &[]);
}

fn llvm_reference(source: &str, crate_name: &str, expected: &[(&str, u64)], panics: &[&str]) -> Vec<u64> {
    let flags = ["--edition=2021", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Zcodegen-backend=llvm", "-Ztrust-verify=off", "-Ztrust-ir-lower=off", "-Ztrust-ir-flip=no"];
    let library = format!("lib{crate_name}.rlib");
    let external = format!("{crate_name}={library}");
    cmd(rustc_path()).args(flags).args([source, "--crate-type=rlib",
        &format!("--crate-name={crate_name}"), "-o", &library])
        .env_remove(SHADOW).run();
    let calls: String = expected.iter().map(|(name, _)| {
        format!("println!(\"{name}={{}}\", {crate_name}::{name}());\n")
    }).collect();
    let driver = format!("{crate_name}_driver.rs");
    rfs::write(&driver, format!("fn main() {{ {calls} }}\n"));
    let executable = bin_name(&format!("{crate_name}_driver"));
    cmd(rustc_path()).args(flags).args([&driver, "--extern", &external, "-o", &executable])
        .env_remove(SHADOW).run();
    let output = run(&executable).stdout_utf8();
    assert_eq!(output.lines().count(), expected.len());
    let values = expected.iter().zip(output.lines()).map(|((name, expected), line)| {
        let (actual_name, raw) = line.split_once('=').unwrap();
        assert_eq!(actual_name, *name);
        let value = raw.parse::<u64>().unwrap();
        assert_eq!(value, *expected);
        value
    }).collect();
    for panic in panics {
        let driver = format!("{crate_name}_{panic}.rs");
        rfs::write(&driver, format!("fn main() {{ {crate_name}::{panic}(); }}\n"));
        let executable = bin_name(&format!("{crate_name}_{panic}"));
        cmd(rustc_path()).args(flags).args([&driver, "--extern", &external, "-o", &executable])
            .env_remove(SHADOW).run();
        run_fail(&executable).assert_stderr_contains("index out of bounds: the len is 1 but the index is 9");
    }
    values
}

//! An evaluated FRU base must request the storage used by its scalar borrows.
//! Inspect the direct producer's values and order; verification grants no proof here.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{rfs, rustc, serde_json, trust_ir};

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = coverage["bodies"]
        .as_array()
        .expect("complete body inventory")
        .iter()
        .filter(|row| row["def_path"] == name)
        .collect();
    assert_eq!(found.len(), 1, "one source body for {name}");
    found[0]
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let plain = format!("fn @{name}(");
    let quoted = format!("fn @\"{name}\"(");
    let (_, tail) = text
        .split_once(&plain)
        .or_else(|| text.split_once(&quoted))
        .expect("emitted source function");
    tail.split_once("\n}\n").expect("complete function body").0
}

fn definition<'a>(definitions: &'a BTreeMap<String, String>, value: &str) -> &'a str {
    definitions.get(value).expect("defined SSA value")
}

fn extract_field(instruction: &str) -> Option<(&str, usize)> {
    let rest = instruction.strip_prefix("extractfield ")?;
    let (_, arguments) = rest.split_once(' ')?;
    let mut arguments = arguments.split(',').map(str::trim);
    let aggregate = arguments.next()?;
    let field = arguments.next()?.parse().ok()?;
    assert!(arguments.next().is_none(), "one aggregate and field");
    Some((aggregate, field))
}

fn aggregate_field(
    definitions: &BTreeMap<String, String>,
    aggregate: &str,
    field: usize,
    fuel: usize,
) -> String {
    assert!(fuel > 0, "bounded aggregate definition chain");
    let rest = definition(definitions, aggregate)
        .strip_prefix("insertfield ")
        .expect("the requested field must be initialized, not read from a seed");
    let (_, arguments) = rest.split_once(' ').expect("typed insertfield");
    let arguments: Vec<_> = arguments.split(',').map(str::trim).collect();
    assert_eq!(arguments.len(), 3, "base, field and inserted value");
    let inserted: usize = arguments[1].parse().expect("field index");
    if inserted == field {
        arguments[2].to_owned()
    } else {
        aggregate_field(definitions, arguments[0], field, fuel - 1)
    }
}

fn scalar_origin(
    definitions: &BTreeMap<String, String>,
    value: &str,
    fuel: usize,
) -> String {
    assert!(fuel > 0, "bounded field-copy chain");
    if let Some((aggregate, field)) = extract_field(definition(definitions, value)) {
        let source = aggregate_field(definitions, aggregate, field, fuel - 1);
        scalar_origin(definitions, &source, fuel - 1)
    } else {
        value.to_owned()
    }
}

fn check_storage_and_fields(body: &str, ordered: bool) {
    let lines: Vec<_> = body
        .lines()
        .map(|line| line.split(';').next().unwrap().trim())
        .filter(|line| !line.is_empty())
        .collect();
    let arguments = lines
        .iter()
        .find_map(|line| {
            line.starts_with("bb")
                .then(|| line.split_once('(')?.1.strip_suffix("):"))
                .flatten()
        })
        .expect("entry block arguments");
    let (input, ty) = arguments.split_once(':').expect("typed input argument");
    assert_eq!(ty.trim(), "u32", "one scalar input: {body}");
    let definitions: BTreeMap<_, _> = lines
        .iter()
        .filter_map(|line| line.split_once(" = "))
        .map(|(value, instruction)| (value.to_owned(), instruction.to_owned()))
        .collect();
    let allocations: Vec<_> = definitions
        .iter()
        .filter(|(_, instruction)| instruction.starts_with("alloca "))
        .collect();
    assert_eq!(allocations.len(), 1, "one real local slot, no fresh snapshots: {body}");
    let (slot, allocation) = allocations[0];
    assert_eq!(allocation, "alloca u32", "the slot stores the original scalar");
    let stores: Vec<_> = lines
        .iter()
        .enumerate()
        .filter_map(|(position, line)| {
            line.strip_prefix("store u32 ")?
                .strip_suffix(&format!(", ptr {slot}"))
                .map(|value| (position, value))
        })
        .collect();
    assert_eq!(stores.len(), if ordered { 3 } else { 2 }, "all scalar stores: {body}");
    assert_eq!(stores[0].1, input.trim(), "initialize from the original input: {body}");
    let loads: Vec<_> = lines
        .iter()
        .enumerate()
        .filter_map(|(position, line)| {
            line.strip_suffix(&format!(" = load u32, ptr {slot}"))
                .map(|value| (position, value))
        })
        .collect();
    assert_eq!(loads.len(), 1, "read the FRU base's field from the same slot: {body}");
    let (load_position, loaded) = loads[0];
    if ordered {
        assert_eq!(definition(&definitions, stores[1].1), "const u32 3");
        assert_eq!(definition(&definitions, stores[2].1), "const u32 7");
        assert!(stores[0].0 < stores[1].0 && stores[1].0 < load_position
            && load_position < stores[2].0,
            "explicit field writes three before the base reads it and writes seven: {body}");
    } else {
        assert_eq!(definition(&definitions, stores[1].1), "const u32 7");
        assert!(stores[0].0 < stores[1].0 && stores[1].0 < load_position,
            "initialize, mutate, then read the FRU base field: {body}");
    }
    let returns: Vec<_> = lines.iter().filter_map(|line| line.strip_prefix("ret ")).collect();
    assert_eq!(returns.len(), 1, "one scalar return: {body}");
    let operands: Vec<_> = definition(&definitions, returns[0])
        .strip_prefix("xor u32 ")
        .expect("the scalar result must depend on both fields")
        .split(',')
        .map(str::trim)
        .collect();
    assert_eq!(operands.len(), 2);
    let (first_aggregate, first_field) =
        extract_field(definition(&definitions, operands[0])).expect("first field read");
    let (second_aggregate, second_field) =
        extract_field(definition(&definitions, operands[1])).expect("second field read");
    assert_eq!((first_field, second_field), (0, 1));
    assert_eq!(first_aggregate, second_aggregate, "read both fields of the final update");
    let first = scalar_origin(&definitions, operands[0], 32);
    let second = scalar_origin(&definitions, operands[1], 32);
    assert_eq!(definition(&definitions, &first), "const u32 1", "keep explicit field");
    assert_eq!(second, loaded, "the omitted field must retain the base's loaded value");
    assert!(!body.contains("undef"), "no missing-value substitute: {body}");
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let output = rustc()
        .input("subject.rs")
        .crate_name("fru_base_storage")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:ir")
        .run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/fru_base_storage.coverage.json"),
    ).expect("complete source coverage");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let names = [
        "parameter_bound", "parameter_hidden", "local_bound", "local_hidden",
        "explicit_field_before_base",
    ];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/fru_base_storage.trust-ir.txt"));
    for name in names {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        check_storage_and_fields(body(&text, name), name == "explicit_field_before_base");
    }
    // The producer change must not change the existing MIR-consumer boundary.
    // Native execution determines that boundary; this test requires paired parity.
    for (bound, hidden) in [("parameter_bound", "parameter_hidden"), ("local_bound", "local_hidden")] {
        assert!(row(&coverage, bound)["spliced"].is_boolean());
        assert_eq!(row(&coverage, bound)["spliced"], row(&coverage, hidden)["spliced"]);
    }
}

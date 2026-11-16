//! Raw/reference storage checks; no raw/reference splice equivalence is assumed.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(found.len(), 1, "one source body for {name}");
    found[0]
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    text.split_once(&format!("fn @{name}(")).or_else(|| text.split_once(&format!("fn @\"{name}\"(")))
        .unwrap().1.split_once("\n}\n").unwrap().0
}

fn storage(body: &str, mutates: bool) {
    let lines: Vec<_> = body.lines().map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let arguments = lines.iter().find_map(|line| {
        line.starts_with("bb").then(|| line.split_once('(')?.1.strip_suffix("):"))
            .flatten()
    }).expect("entry arguments");
    let (input, ty) = arguments.split_once(':').unwrap();
    assert_eq!(ty.trim(), "u32", "exactly one scalar input");
    let slots: Vec<_> = lines.iter().filter_map(|line| line.strip_suffix(" = alloca u32")).collect();
    assert_eq!(slots.len(), 1, "one original-object slot: {body}");
    let slot = slots[0];
    let stores: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.strip_prefix("store u32 ")?.strip_suffix(&format!(", ptr {slot}"))
            .map(|value| (position, value))
    }).collect();
    assert_eq!(stores.len(), if mutates { 2 } else { 1 }, "no extra snapshot store: {body}");
    assert_eq!(stores[0].1, input.trim(), "initialize from the actual argument");
    if mutates {
        let seven: Vec<_> = lines.iter().filter_map(|line| line.strip_suffix(" = const u32 7")).collect();
        assert_eq!(seven.len(), 1);
        assert_eq!(stores[1].1, seven[0], "write the original scalar slot");
        assert!(stores[0].0 < stores[1].0);
    }
    let loads: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.strip_suffix(&format!(" = load u32, ptr {slot}")).map(|value| (position, value))
    }).collect();
    assert_eq!(loads.len(), 1, "read the same original slot: {body}");
    assert!(stores.last().unwrap().0 < loads[0].0);
    assert!(lines.contains(&format!("ret {}", loads[0].1).as_str()));
    assert!(!body.contains("undef"));
}

fn compile(file: &str, name: &str, directory: &str) -> serde_json::Value {
    let output = cmd(rustc_path()).args([
        file, "--edition=2024", "--crate-type=lib", &format!("--crate-name={name}"),
        "--emit=mir", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        &format!("-Ztrust-dump=ir:{directory}"), "-o", &format!("{name}.mir"),
    ]).run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read(format!("{directory}/{name}.coverage.json")),
    ).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    coverage
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let coverage = compile("subject.rs", "raw_borrow_storage", "positive");
    let names = [
        ("parameter_ref_mut", true), ("parameter_raw_mut", true),
        ("local_ref_mut", true), ("local_raw_mut", true),
        ("parameter_ref_const", false), ("parameter_raw_const", false),
        ("local_ref_const", false), ("local_raw_const", false),
        ("parameter_raw_const_alias", true), ("local_raw_const_alias", true),
    ];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    assert_eq!(coverage["totals"]["bodies"], 10);
    assert_eq!(coverage["totals"]["lowered"], 10);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["totals"]["unsupported"], 0);
    let text = trust_ir::by_display_path(&rfs::read_to_string("positive/raw_borrow_storage.trust-ir.txt"));
    for (name, mutates) in names {
        let result = row(&coverage, name);
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        let spliced = result["spliced"].as_bool().expect("actual splice result is disclosed");
        if name.contains("_ref_") {
            assert!(spliced, "reference control retains its existing splice: {name}: {result}");
        }
        eprintln!("storage body {name}: lowered=true spliced={spliced}; no raw/reference splice parity claim");
        storage(body(&text, name), mutates);
    }

    let coverage = compile("refusals.rs", "raw_borrow_refusals", "negative");
    let expected = [
        ("packed_const", "RawBorrow(packed place)"),
        ("packed_mut", "RawBorrow(packed place)"),
        ("raw_parameter_address", "Promote(non-scalar &mut param)"),
        ("raw_parameter_deref", "Deref(non-borrow ptr)"),
        ("raw_escape", "Return(borrow ptr escapes tail)"),
    ];
    // The refusals plus the one lowered integer twin, `raw_parameter_integer_deref`.
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), expected.len() + 1);
    let integer = row(&coverage, "raw_parameter_integer_deref");
    assert_eq!(integer["lowered"], true, "typed integer raw-entry load lowers: {integer}");
    assert!(integer["unsupported"].as_array().unwrap().is_empty(), "{integer}");
    for (name, tag) in expected {
        let result = row(&coverage, name);
        assert_eq!(result["lowered"], false, "{name}: {result}");
        assert_eq!(result["spliced"], false, "{name}: {result}");
        assert!(result["unsupported"].to_string().contains(tag), "{name} preserves {tag}: {result}");
    }
    assert!(row(&coverage, "raw_parameter_address")["unsupported"].to_string()
        .contains("Borrow(shared local lacks stable storage)"));
}

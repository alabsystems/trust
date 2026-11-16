//! A supported numeric cast must not hide the storage needed by its operand.
//! Inspect the emitted program; verification stays off and grants no proof authority.
//@ ignore-cross-compile

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

fn check_storage(body: &str, cast: bool) {
    let lines: Vec<_> = body
        .lines()
        .map(|line| line.split(" ;").next().unwrap().trim())
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
    assert!(!ty.contains(','), "exactly one entry argument: {body}");
    assert_eq!(ty.trim(), "u32", "scalar input: {body}");
    let slots: Vec<_> = lines
        .iter()
        .filter_map(|line| line.split_once(" = alloca u32").map(|(value, _)| value))
        .collect();
    assert_eq!(slots.len(), 1, "one lifetime-long scalar slot: {body}");
    let slot = slots[0];
    let seven: Vec<_> = lines
        .iter()
        .filter_map(|line| line.strip_suffix(" = const u32 7"))
        .collect();
    assert_eq!(seven.len(), 1, "one mutation value: {body}");
    let stores: Vec<_> = lines
        .iter()
        .enumerate()
        .filter_map(|(position, line)| {
            line.strip_prefix("store u32 ")?
                .strip_suffix(&format!(", ptr {slot}"))
                .map(|value| (position, value))
        })
        .collect();
    assert_eq!(stores.len(), 2, "initialization and mutation use the same slot: {body}");
    assert_eq!(stores[0].1, input.trim(), "initialize from the original argument: {body}");
    assert_eq!(stores[1].1, seven[0], "the mutation stores seven: {body}");
    let loads: Vec<_> = lines
        .iter()
        .enumerate()
        .filter_map(|(position, line)| {
            line.strip_suffix(&format!(" = load u32, ptr {slot}"))
                .map(|value| (position, value))
        })
        .collect();
    assert_eq!(loads.len(), 1, "read the mutated value from its real slot: {body}");
    assert!(stores[0].0 < stores[1].0 && stores[1].0 < loads[0].0,
        "initialization precedes mutation, which precedes the load: {body}");
    let result = if cast {
        let casts: Vec<_> = lines
            .iter()
            .enumerate()
            .filter_map(|(position, line)| {
                line.strip_suffix(&format!(" = zext u32 {} to u64", loads[0].1))
                    .map(|value| (position, value))
            })
            .collect();
        assert_eq!(casts.len(), 1, "widen the value actually loaded after mutation: {body}");
        assert!(loads[0].0 < casts[0].0, "load precedes cast: {body}");
        casts[0].1
    } else {
        assert!(!lines.iter().any(|line| line.contains(" = zext ")),
            "the paired control has no cast: {body}");
        loads[0].1
    };
    assert!(lines.contains(&format!("ret {result}").as_str()),
        "return the loaded or widened value: {body}");
    assert!(!body.contains("undef"), "no missing-value substitute: {body}");
}

fn no_proof_claim(coverage: &serde_json::Value) {
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rustc().input("subject.rs").crate_name("cast_value_temporaries").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:positive").run();
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("positive/cast_value_temporaries.coverage.json"),
    ).expect("complete source coverage");
    no_proof_claim(&coverage);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 5);
    let text = trust_ir::by_display_path(
        &rfs::read_to_string("positive/cast_value_temporaries.trust-ir.txt"),
    );
    for (name, cast) in [
        ("parameter_direct", false),
        ("parameter_cast", true),
        ("local_direct", false),
        ("local_cast", true),
    ] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        check_storage(body(&text, name), cast);
    }
    let float = row(&coverage, "saturating_float");
    assert_eq!(float["lowered"], true, "{float}");
    assert_eq!(float["symbolic"], false, "{float}");
    assert!(float["unsupported"].as_array().unwrap().is_empty(), "{float}");
    // Assembly into the direct IR artifact is separate from re-deriving MIR.
    assert_eq!(float["spliced"], true, "the existing direct IR includes float casts: {float}");
    let differentials = &float["differentials"];
    assert_eq!(differentials["interpreter"]["verdict"], "agreed", "{float}");
    assert_eq!(differentials["interpreter"]["samples"].as_u64(), Some(8), "{float}");
    assert_eq!(differentials["derived_mir"]["verdict"], "unsupported", "{float}");
    assert_eq!(differentials["derived_mir"]["detail"],
        "shim: Cast op FPToSISat outside integer fragment", "{float}");
    let float_body = body(&text, "saturating_float");
    let float_lines: Vec<_> = float_body.lines()
        .map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let casts: Vec<_> = float_lines.iter()
        .filter_map(|line| line.split_once(" = fptosi.sat f64 ")).collect();
    assert_eq!(casts.len(), 1, "one saturating float conversion: {float_body}");
    assert!(casts[0].1.ends_with(" to i32"), "signed destination: {float_body}");
    assert!(float_lines.contains(&format!("ret {}", casts[0].0).as_str()),
        "return the saturating conversion: {float_body}");

    let output = rustc().input("refusals.rs").crate_name("cast_value_refusals").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:negative").run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("negative/cast_value_refusals.coverage.json"),
    ).expect("complete refusal coverage");
    no_proof_claim(&coverage);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 2);
    for (name, tag) in [
        ("retyped_pointer_to_integer", "Cast(ptr source)"),
        ("signed_integer_to_pointer", "Cast(ptr dest)"),
    ] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert_eq!(row["spliced"], false, "{name}: {row}");
        assert!(row["unsupported"].to_string().contains(tag), "{name} retains {tag}: {row}");
    }
}

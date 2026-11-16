//! Supported wrappers must preserve operand storage and values.
//! Verification is off. Array splice parity is reported without claiming admission.
//@ ignore-cross-compile

use run_make_support::{bin_name, cmd, rfs, run, rustc_path, serde_json, trust_ir};

const SHADOW_ENV: &str = "TRUST_CONTRACT_CARRY_SHADOW";

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(found.len(), 1, "one source body for {name}");
    found[0]
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let plain = format!("fn @{name}(");
    let quoted = format!("fn @\"{name}\"(");
    text.split_once(&plain).or_else(|| text.split_once(&quoted)).unwrap().1
        .split_once("\n}\n").unwrap().0
}

fn instruction<'a>(lines: &[&'a str], prefix: &str) -> (usize, &'a str, &'a str) {
    let found: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        let (result, operation) = line.split_once(" = ")?;
        (operation == prefix || (prefix.ends_with(' ') && operation.starts_with(prefix)))
            .then_some((position, result, operation))
    }).collect();
    assert_eq!(found.len(), 1, "one {prefix} instruction: {lines:?}");
    found[0]
}

fn check_const_initializer(coverage: &serde_json::Value, text: &str, name: &str) {
    let result = row(coverage, name);
    assert_eq!(result["kind"], "const-init", "{name}: {result}");
    assert_eq!(result["lowered"], true, "{name}: {result}");
    assert_eq!(result["symbolic"], false, "{name}: {result}");
    assert_eq!(result["spliced"], true, "{name}: {result}");
    assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
    let initializer = body(text, &format!("{name}::{{const-init}}"));
    let lines: Vec<_> = initializer.lines()
        .map(|line| line.split(" ;").next().unwrap().trim()).collect();
    assert!(lines.contains(&"bb0:"), "a constant initializer has no arguments: {initializer}");
    let (_, value, _) = instruction(&lines, "const usize 1");
    assert!(lines.contains(&format!("ret {value}").as_str()));
    let instructions: Vec<_> = lines.iter().filter(|line|
        !line.is_empty() && !line.starts_with(';') && !line.starts_with("bb")
            && !line.ends_with('{')).collect();
    assert_eq!(instructions.len(), 2, "only the length constant and return: {initializer}");
    let interpreter = &result["differentials"]["interpreter"];
    assert_eq!(interpreter["verdict"], "agreed", "{name}: {result}");
    assert_eq!(interpreter["samples"].as_u64(), Some(1), "{name}: {result}");
}

fn scalar_storage<'a>(lines: &[&'a str]) -> (usize, &'a str, &'a str) {
    let arguments = lines.iter().find_map(|line| {
        line.starts_with("bb").then(|| line.split_once('(')?.1.strip_suffix("):"))
            .flatten()
    }).expect("entry arguments");
    let (input, ty) = arguments.split_once(':').unwrap();
    assert_eq!(ty.trim(), "u32", "one original scalar argument");
    let (_, slot, _) = instruction(lines, "alloca u32");
    let (_, seven, _) = instruction(lines, "const u32 7");
    let stores: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.strip_prefix("store u32 ")?.strip_suffix(&format!(", ptr {slot}"))
            .map(|value| (position, value))
    }).collect();
    assert_eq!(stores.len(), 2, "exact initialization and mutation");
    assert_eq!(stores[0].1, input.trim(), "initialize from the incoming value");
    assert_eq!(stores[1].1, seven, "store the real mutation");
    let (load_at, loaded, operation) = instruction(lines, &format!("load u32, ptr {slot}"));
    assert_eq!(operation, format!("load u32, ptr {slot}"));
    assert!(stores[0].0 < stores[1].0 && stores[1].0 < load_at);
    (load_at, loaded, slot)
}

fn slice_value(text: &str, body: &str, lines: &[&str], scalar: (usize, &str, &str)) {
    let (parts_at, slice, parts) = instruction(lines, "ptr_from_parts ");
    let (fat_ty, operands) = parts.strip_prefix("ptr_from_parts ").unwrap()
        .split_once(" ptr ").unwrap();
    let element = fat_ty.strip_prefix("fatptr<slice ").unwrap().strip_suffix('>').unwrap();
    assert!(text.lines().any(|line| line == format!("type {element} = u32")));
    let array_ty = format!("[{element} x 1]");
    let (array_slot, length) = operands.split_once(", u64 ").unwrap();
    assert_ne!(array_slot, scalar.2, "array storage is distinct from the borrowed scalar");
    let (_, allocated, _) = instruction(lines, &format!("alloca {array_ty}"));
    assert_eq!(array_slot, allocated, "the slice uses the single original array slot");
    assert!(lines.contains(&format!("{length} = const u64 1").as_str()));

    let (insert_at, array_value, insert) = instruction(lines, &format!("insertelement {array_ty} "));
    let operands: Vec<_> = insert.strip_prefix(&format!("insertelement {array_ty} "))
        .unwrap().split(", ").collect();
    assert_eq!(operands.len(), 3);
    assert_eq!(operands[2], scalar.1, "array element is the value loaded after mutation");
    assert!(lines.contains(&format!("{} = const i64 0", operands[1]).as_str()));
    let stores: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        (*line == format!("store {array_ty} {array_value}, ptr {array_slot}").as_str())
            .then_some(position)
    }).collect();
    assert_eq!(stores.len(), 1, "store the actual constructed array");
    assert!(scalar.0 < insert_at && insert_at < stores[0] && stores[0] < parts_at);

    let (metadata_at, metadata, operation) = instruction(lines, "ptr_metadata ");
    assert_eq!(operation, format!("ptr_metadata {fat_ty} {slice} to u64"));
    let (cast_at, bound, operation) = instruction(lines, "bitcast u64 ");
    assert_eq!(operation, format!("bitcast u64 {metadata} to usize"));
    let (_, index, _) = instruction(lines, "const usize 0");
    let (compare_at, comparison, operation) = instruction(lines, "icmp ult usize ");
    assert_eq!(operation, format!("icmp ult usize {index}, {bound}"));
    let assertion = format!("assert {comparison}, bounds_check {index}, {bound}");
    let assertions: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        (*line == assertion.as_str()).then_some(position)
    }).collect();
    assert_eq!(assertions.len(), 1);
    assert_eq!(body.matches("#proof: in_bounds").count(), 1);
    let (data_at, data, operation) = instruction(lines, "ptr_data ");
    assert_eq!(operation, format!("ptr_data {fat_ty} {slice}"));
    let (gep_at, address, operation) = instruction(lines, "gep u32, ");
    assert_eq!(operation, format!("gep u32, ptr {data}, {index}"));
    let (read_at, value, operation) = instruction(lines, &format!("load u32, ptr {address}"));
    assert_eq!(operation, format!("load u32, ptr {address}"));
    assert!(parts_at < metadata_at && metadata_at < cast_at && cast_at < compare_at);
    assert!(compare_at < assertions[0] && assertions[0] < data_at);
    assert!(data_at < gep_at && gep_at < read_at);
    assert!(lines.contains(&format!("ret {value}").as_str()));
}

fn identity_storage(
    text: &str,
    body: &str,
    lines: &[&str],
    scalar: Option<(usize, &str, &str)>,
    copied: bool,
    caller: bool,
) {
    let parts: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        let (value, operation) = line.split_once(" = ")?;
        operation.strip_prefix("ptr_from_parts ").map(|operation| (position, value, operation))
    }).collect();
    assert_eq!(parts.len(), 2, "both source borrows produce slice values");
    let first_parts = parts[0].2;
    let (fat_ty, first_operands) = first_parts.split_once(" ptr ").unwrap();
    let element = fat_ty.strip_prefix("fatptr<slice ").unwrap().strip_suffix('>').unwrap();
    let element_ty = text.lines().find_map(|line| line.strip_prefix(&format!("type {element} = ")))
        .expect("slice element type is defined");
    let array_ty = format!("[{element} x 1]");
    let allocas: Vec<_> = lines.iter().filter_map(|line| {
        let (value, operation) = line.split_once(" = ")?;
        (operation == format!("alloca {array_ty}")).then_some(value)
    }).collect();
    assert_eq!(allocas.len(), if copied && !caller { 2 } else { 1 });
    let (original, _) = first_operands.split_once(", u64 ").unwrap();
    let (_, second_operands) = parts[1].2.split_once(" ptr ").unwrap();
    let (second, _) = second_operands.split_once(", u64 ").unwrap();
    if copied {
        assert_ne!(original, second, "an array-value temporary has its own address");
        assert!(allocas.contains(&second));
    } else {
        assert_eq!(original, second, "repeated named borrows share the original address");
    }
    if caller {
        assert!(copied);
        assert_eq!(element_ty, "u32", "caller copy retains its concrete element type");
        let entry = lines.iter().find_map(|line| {
            line.starts_with("bb").then(|| line.split_once('(')?.1.strip_suffix("):"))
                .flatten()
        }).expect("caller reference entry argument");
        let (input, ty) = entry.split_once(':').unwrap();
        assert_eq!(ty.trim(), "ptr");
        assert_eq!(original, input.trim(), "uncopied caller array keeps its incoming pointer");
    } else {
        assert!(allocas.contains(&original));
        let (insert_at, array_value, insert) = instruction(lines, &format!("insertelement {array_ty} "));
        let values: Vec<_> = insert.strip_prefix(&format!("insertelement {array_ty} "))
            .unwrap().split(", ").collect();
        assert_eq!(values.len(), 3);
        assert!(lines.contains(&format!("{} = const i64 0", values[1]).as_str()));
        if let Some(scalar) = scalar {
            assert_eq!(element_ty, "u32");
            assert_ne!(original, scalar.2);
            assert_eq!(values[2], scalar.1, "array stores the value loaded after mutation");
            assert!(scalar.0 < insert_at);
        } else {
            assert!(element_ty.starts_with("struct."), "NSA shared aggregate case");
            let definition = lines.iter().find_map(|line| {
                line.strip_prefix(&format!("{} = insertfield {element_ty} ", values[2]))
            }).expect("the original shared struct has initialized fields");
            let fields: Vec<_> = definition.split(", ").collect();
            assert_eq!(fields.len(), 3);
            assert_eq!(fields[1], "1", "initialize the count field by its declaration index");
            assert!(lines.contains(&format!("{} = const u32 7", fields[2]).as_str()));
        }
        let store = format!("store {array_ty} {array_value}, ptr {original}");
        let stores: Vec<_> = lines.iter().enumerate()
            .filter_map(|(i, line)| (*line == store).then_some(i)).collect();
        assert_eq!(stores.len(), 1, "initialize the original array exactly once");
        assert!(insert_at < stores[0] && stores[0] < parts[0].0);
    }
    if copied {
        let (load_at, loaded, _) = instruction(lines, &format!("load {array_ty}, ptr {original}"));
        let store = format!("store {array_ty} {loaded}, ptr {second}");
        let stores: Vec<_> = lines.iter().enumerate()
            .filter_map(|(i, line)| (*line == store).then_some(i)).collect();
        assert_eq!(stores.len(), 1, "copy current original value into the temporary");
        assert!(parts[0].0 < load_at && load_at < stores[0] && stores[0] < parts[1].0);
    }
    let mut reads = Vec::new();
    for (parts_at, slice, operation) in parts {
        let (actual_ty, operands) = operation.split_once(" ptr ").unwrap();
        assert_eq!(actual_ty, fat_ty);
        let (_, length) = operands.split_once(", u64 ").unwrap();
        assert!(lines.contains(&format!("{length} = const u64 1").as_str()));
        let (metadata_at, metadata, _) = instruction(lines, &format!("ptr_metadata {fat_ty} {slice} to u64"));
        let (cast_at, bound, _) = instruction(lines, &format!("bitcast u64 {metadata} to usize"));
        let comparisons: Vec<_> = lines.iter().enumerate().filter_map(|(i, line)| {
            let (value, operation) = line.split_once(" = ")?;
            let operands = operation.strip_prefix("icmp ult usize ")?;
            let index = operands.strip_suffix(&format!(", {bound}"))?;
            Some((i, value, index))
        }).collect();
        assert_eq!(comparisons.len(), 1);
        let (compare_at, comparison, index) = comparisons[0];
        assert!(lines.contains(&format!("{index} = const usize 0").as_str()));
        let assertion = format!("assert {comparison}, bounds_check {index}, {bound}");
        let assertions: Vec<_> = lines.iter().enumerate()
            .filter_map(|(i, line)| (*line == assertion).then_some(i)).collect();
        assert_eq!(assertions.len(), 1);
        let (data_at, data, _) = instruction(lines, &format!("ptr_data {fat_ty} {slice}"));
        assert!(parts_at < metadata_at && metadata_at < cast_at && cast_at < compare_at);
        assert!(compare_at < assertions[0] && assertions[0] < data_at);
        let (gep_at, address, _) = instruction(lines, &format!("gep {element_ty}, ptr {data}, {index}"));
        let (read_at, loaded, _) = instruction(lines, &format!("load {element_ty}, ptr {address}"));
        assert!(data_at < gep_at && gep_at < read_at);
        let (value_at, value) = if element_ty == "u32" {
            (read_at, loaded)
        } else {
            let (field_at, field, _) = instruction(lines, &format!("extractfield u32 {loaded}, 1"));
            assert!(read_at < field_at, "read the count field from the actual loaded struct");
            (field_at, field)
        };
        reads.push((value_at, value));
    }
    assert_eq!(body.matches("#proof: in_bounds").count(), 2);
    let (xor_at, result, _) = instruction(lines, &format!("xor u32 {}, {}", reads[0].1, reads[1].1));
    assert!(reads.iter().all(|(read_at, _)| *read_at < xor_at));
    assert!(lines.contains(&format!("ret {result}").as_str()));
}

fn no_proof(coverage: &serde_json::Value) {
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
}

fn compile(file: &str, name: &str, directory: &str) -> serde_json::Value {
    compile_with_shadow(file, name, directory, None)
}

fn compile_with_shadow(
    file: &str, name: &str, directory: &str, shadow: Option<&str>,
) -> serde_json::Value {
    let mut command = cmd(rustc_path());
    command.args([
        file, "--edition=2024", "--crate-type=lib", &format!("--crate-name={name}"),
        "--emit=mir", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        &format!("-Ztrust-dump=ir:{directory}"), "-o", &format!("{name}.mir"),
    ]);
    match shadow {
        Some(directory) => { command.env(SHADOW_ENV, directory); }
        None => { command.env_remove(SHADOW_ENV); }
    }
    let output = command.run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    serde_json::from_slice(&rfs::read(format!("{directory}/{name}.coverage.json"))).unwrap()
}

// Neither differential lane executes every call-containing body. Report their
// actual status; an agreement must still represent at least one executed sample.
fn report_differentials(result: &serde_json::Value, name: &str) {
    for lane in ["interpreter", "seam"] {
        let differential = &result["differentials"][lane];
        if differential["verdict"] == "agreed" {
            assert!(differential["samples"].as_u64().unwrap() > 0, "{name}: {lane}: {result}");
        }
        assert_ne!(differential["verdict"], "mismatch", "{name}: {lane}: {result}");
        eprintln!("full-range {name}: {lane}={differential}");
    }
}

// Compile the SAME fixture separately through LLVM, with candidate lowering and
// splicing disabled for both the library and executable. Never link the lowered
// fixture's artifact into the reference executable.
fn llvm_reference(file: &str, name: &str, expected: &[(&str, u64)]) -> Vec<u64> {
    let library = format!("lib{name}.rlib");
    let driver = format!("{name}_driver.rs");
    let executable = bin_name(&format!("{name}_driver"));
    let flags = [
        "--edition=2024", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Zcodegen-backend=llvm", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
        "-Ztrust-ir-flip=no",
    ];
    cmd(rustc_path()).args(flags).args([
        file, "--crate-type=rlib", &format!("--crate-name={name}"), "-o", &library,
    ]).env_remove(SHADOW_ENV).run();
    let calls: String = expected.iter().map(|(function, _)| {
        format!("    println!(\"{function}={{}}\", {name}::{function}());\n")
    }).collect();
    rfs::write(&driver, format!("fn main() {{\n{calls}}}\n"));
    cmd(rustc_path()).args(flags).args([
        &driver, "--extern", &format!("{name}={library}"), "-o", &executable,
    ]).env_remove(SHADOW_ENV).run();
    let stdout = run(&executable).stdout_utf8();
    assert_eq!(stdout.lines().count(), expected.len(), "native reference output: {stdout}");
    expected.iter().zip(stdout.lines()).map(|((function, expected_value), line)| {
        let (actual_name, actual_value) = line.split_once('=').unwrap();
        assert_eq!(actual_name, *function, "native reference output order and identity");
        let value = actual_value.parse::<u64>().unwrap();
        assert_eq!(value, *expected_value, "native source value for {function}");
        value
    }).collect()
}

// This is a zero-authority execution check, not a proof or a replacement for a
// differential verdict. The shadow interprets the published module, including
// real local calls, instead of inferring a return from structural IR patterns.
fn check_execution(
    file: &str, name: &str, directory: &str, coverage: &serde_json::Value,
    reference_name: &str, expected: &[(&str, u64)],
) {
    let shadow_dir = format!("{directory}-shadow");
    let shadow_ir = format!("{directory}-shadow-ir");
    rfs::create_dir(&shadow_dir);
    let with_shadow = compile_with_shadow(file, name, &shadow_ir, Some(&shadow_dir));
    assert_eq!(&with_shadow, coverage, "enabling the shadow changes no coverage verdict");
    let published = format!("{directory}/{name}.trust-ir.bin");
    let clone_run = format!("{shadow_ir}/{name}.trust-ir.bin");
    let published = rfs::read(published);
    assert!(!published.is_empty(), "published module must exist");
    assert_eq!(published, rfs::read(clone_run), "shadow changes no published module bytes");
    let shadow: serde_json::Value = serde_json::from_slice(&rfs::read(format!(
        "{shadow_dir}/{name}.contract-carry.shadow.json",
    ))).unwrap();
    assert_eq!(shadow["schema"], "trust.contract-carry.shadow/v1");
    assert_eq!(shadow["crate"], name);
    assert_eq!(shadow["published"], true, "{shadow}");
    assert!(shadow["authority"].as_str().unwrap().starts_with("NONE:"));
    assert_eq!(shadow["binary_round_trip"], true, "{shadow}");
    for key in [
        "duplicate_registrations", "install_errors", "validate_module",
        "validate_module_with_authority", "validate_linked_module", "text_losses",
        "staged_rung_errors", "rows", "summaries",
    ] {
        assert!(shadow[key].as_array().unwrap().is_empty(), "{key}: {shadow}");
    }
    let interpreted = shadow["interpreted"].as_array().unwrap();
    let resolutions = shadow["resolution"].as_array().unwrap();
    let native = llvm_reference(file, reference_name, expected);
    for ((function, expected_value), native_value) in expected.iter().zip(native) {
        let result = row(coverage, function);
        let function_id = result["func_id"].as_u64().expect("published coverage function id");
        let matches: Vec<_> = interpreted.iter()
            .filter(|value| value["display_path"] == *function).collect();
        assert_eq!(matches.len(), 1, "one actual interpretation of {function}: {shadow}");
        let execution = matches[0];
        assert_eq!(execution["function"].as_u64(), Some(function_id), "{execution}: {result}");
        assert_eq!(interpreted.iter().filter(|value|
            value["function"].as_u64() == Some(function_id)).count(), 1,
            "one interpretation per function id: {shadow}");
        for resolution in resolutions.iter().filter(|value| value["def_path"] == *function) {
            assert_eq!(resolution["function"].as_u64(), Some(function_id), "{resolution}");
            assert_eq!(resolution["def_index"], result["def_index"], "{resolution}: {result}");
        }
        let value = execution["value"].as_object().unwrap();
        assert_eq!(value.len(), 1, "one successful raw return, without an error: {execution}");
        let raw = value.get("raw").and_then(serde_json::Value::as_str)
            .expect("actual integer return, not an interpreter error");
        let actual = raw.parse::<u64>().unwrap();
        assert_eq!(actual, *expected_value, "source return of {function}: {execution}");
        assert_eq!(actual, native_value, "published Trust IR must execute like LLVM: {execution}");
        eprintln!("full-range executed {function}: trust-ir={actual} llvm={native_value}");
    }
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let coverage = compile("subject.rs", "wrapper_values", "positive");
    no_proof(&coverage);
    let names = [
        "parameter_array_bound", "parameter_unsize", "local_array_bound", "local_unsize",
        "parameter_value_direct", "parameter_value_ascribed", "local_value_direct", "local_value_ascribed",
        "parameter_place_direct", "parameter_place_ascribed", "local_place_direct", "local_place_ascribed",
    ];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    assert_eq!(coverage["totals"]["bodies"], 12);
    assert_eq!(coverage["totals"]["lowered"], 12);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["totals"]["unsupported"], 0);
    let text = trust_ir::by_display_path(&rfs::read_to_string("positive/wrapper_values.trust-ir.txt"));
    for name in names {
        let result = row(&coverage, name);
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        let body = body(&text, name);
        assert!(!body.contains("undef"));
        let lines: Vec<_> = body.lines().map(|line| line.split(" ;").next().unwrap().trim()).collect();
        let scalar = scalar_storage(&lines);
        if name.contains("array_bound") || name.ends_with("unsize") {
            slice_value(&text, body, &lines, scalar);
        } else {
            assert_eq!(result["spliced"], true, "scalar wrapper keeps its existing splice: {name}: {result}");
            assert!(lines.contains(&format!("ret {}", scalar.1).as_str()));
        }
    }
    for (direct, wrapped) in [("parameter_array_bound", "parameter_unsize"), ("local_array_bound", "local_unsize")] {
        let direct = row(&coverage, direct);
        let wrapped = row(&coverage, wrapped);
        assert_eq!(direct["spliced"].as_bool().unwrap(), wrapped["spliced"].as_bool().unwrap(),
            "unsize spelling must preserve splice parity: {direct} / {wrapped}");
        eprintln!("array unsize splice parity: direct={} wrapped={}", direct["spliced"], wrapped["spliced"]);
    }

    let repeated = compile("repeated.rs", "wrapper_repeated", "repeated");
    no_proof(&repeated);
    assert_eq!(repeated["bodies"].as_array().unwrap().len(), 10);
    assert_eq!(repeated["totals"]["bodies"], 10);
    assert_eq!(repeated["totals"]["initializer_bodies"], 4);
    assert_eq!(repeated["totals"]["lowered"], 10);
    assert_eq!(repeated["totals"]["symbolic"], 0);
    assert_eq!(repeated["totals"]["unsupported"], 0);
    let text = trust_ir::by_display_path(&rfs::read_to_string("repeated/wrapper_repeated.trust-ir.txt"));
    for (name, copied, caller) in [
        ("parameter_repeated_unsize", false, false),
        ("local_repeated_full_range", false, false),
        ("parameter_copied_unsize", true, false),
        ("local_copied_full_range", true, false),
        ("shared_struct_repeated_unsize", false, false),
        ("caller_array_copy", true, true),
    ] {
        let result = row(&repeated, name);
        assert_eq!(result["kind"], "fn", "{name}: {result}");
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        let body = body(&text, name);
        assert!(!body.contains("undef"));
        let lines: Vec<_> = body.lines().map(|line| line.split(" ;").next().unwrap().trim()).collect();
        let scalar = (!caller && name != "shared_struct_repeated_unsize")
            .then(|| scalar_storage(&lines));
        identity_storage(&text, body, &lines, scalar, copied, caller);
        eprintln!("array storage identity: {name}: spliced={}", result["spliced"]);
    }

    for name in [
        "parameter_copied_unsize::{constant#0}",
        "local_copied_full_range::{constant#0}",
        "caller_array_copy::{constant#0}",
        "caller_array_copy::{constant#1}",
    ] {
        check_const_initializer(&repeated, &text, name);
    }

    let ranges = compile("full_range_identity.rs", "wrapper_full_range_identity", "full-range-identity");
    no_proof(&ranges);
    assert_eq!(ranges["bodies"].as_array().unwrap().len(), 7);
    assert_eq!(ranges["totals"]["bodies"], 7);
    assert_eq!(ranges["totals"]["initializer_bodies"], 1);
    for result in ranges["bodies"].as_array().unwrap() {
        report_differentials(result, result["def_path"].as_str().unwrap());
    }
    let text = trust_ir::by_display_path(
        &rfs::read_to_string("full-range-identity/wrapper_full_range_identity.trust-ir.txt"),
    );
    check_const_initializer(&ranges, &text, "custom::{constant#0}");
    for name in ["builtin_literal", "builtin_bound"] {
        let result = row(&ranges, name);
        assert_eq!(result["kind"], "fn", "{name}: {result}");
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert_eq!(result["spliced"], true, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        let body = body(&text, name);
        assert!(!body.contains("undef"));
        let lines: Vec<_> = body.lines().map(|line| line.split(" ;").next().unwrap().trim()).collect();
        let (parts_at, slice, parts) = instruction(&lines, "ptr_from_parts ");
        let (fat_ty, operands) = parts.strip_prefix("ptr_from_parts ").unwrap()
            .split_once(" ptr ").unwrap();
        let (_, length) = operands.split_once(", u64 ").unwrap();
        let (length_at, _, _) = instruction(&lines, "const u64 1");
        assert!(lines.contains(&format!("{length} = const u64 1").as_str()));
        let (metadata_at, metadata, _) = instruction(&lines,
            &format!("ptr_metadata {fat_ty} {slice} to u64"));
        let (cast_at, returned, _) = instruction(&lines,
            &format!("bitcast u64 {metadata} to usize"));
        assert!(length_at < parts_at && parts_at < metadata_at && metadata_at < cast_at);
        assert!(lines.contains(&format!("ret {returned}").as_str()));
        let interpreter = &result["differentials"]["interpreter"];
        assert!(interpreter["verdict"].as_str().is_some());
        assert!(interpreter["samples"].as_u64().is_some());
    }
    for name in ["custom_call_is_not_index", "effectful_range_is_not_erased",
                 "effectful_callee_is_not_erased"] {
        let result = row(&ranges, name);
        assert_eq!(result["kind"], "fn", "{name}: {result}");
        if result["lowered"].as_bool().unwrap() {
            // A faithful ordinary-call fallback may lower this body. Mandatory
            // published-module execution below checks its actual return value.
            assert_eq!(result["symbolic"], false, "{name}: {result}");
            assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        } else {
            assert_eq!(result["spliced"], false, "{name}: {result}");
            assert!(!result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        }
        eprintln!("full-range non-shortcut {name}: {result}");
    }
    // The helper and its array-length initializer remain in the full inventory.
    assert_eq!(row(&ranges, "custom")["kind"], "fn");
    check_execution(
        "full_range_identity.rs", "wrapper_full_range_identity", "full-range-identity", &ranges,
        "wrapper_full_range_reference", &[
            ("builtin_literal", 1), ("builtin_bound", 1),
            ("custom_call_is_not_index", 0), ("effectful_range_is_not_erased", 1),
            ("effectful_callee_is_not_erased", 1),
        ],
    );

    // Separate fixture: keep the original seven-body inventory intact while
    // making copy-before-range ordering and divergence observable by execution.
    let order = compile("full_range_effect_order.rs", "wrapper_full_range_order", "full-range-order");
    no_proof(&order);
    assert_eq!(order["bodies"].as_array().unwrap().len(), 3);
    assert_eq!(order["totals"]["bodies"], 3);
    assert_eq!(order["totals"]["initializer_bodies"], 1);
    assert_eq!(order["totals"]["lowered"], 3);
    assert_eq!(order["totals"]["symbolic"], 0);
    assert_eq!(order["totals"]["unsupported"], 0);
    let text = trust_ir::by_display_path(
        &rfs::read_to_string("full-range-order/wrapper_full_range_order.trust-ir.txt"),
    );
    check_const_initializer(&order, &text, "copied_before_range_effect::{constant#0}");
    for name in ["copied_before_range_effect", "returning_range_stops_evaluation"] {
        let result = row(&order, name);
        assert_eq!(result["kind"], "fn", "{name}: {result}");
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        report_differentials(result, name);
    }
    check_execution(
        "full_range_effect_order.rs", "wrapper_full_range_order", "full-range-order", &order,
        "wrapper_full_range_order_reference", &[
            ("copied_before_range_effect", 7), ("returning_range_stops_evaluation", 9),
        ],
    );

    let refusals = compile("refusals.rs", "wrapper_refusals", "negative");
    no_proof(&refusals);
    // The two refusals plus the thin mut→const twin that 94502e4acc lowers.
    assert_eq!(refusals["bodies"].as_array().unwrap().len(), 3);
    let thin = row(&refusals, "mutable_to_const_thin");
    assert_eq!(thin["lowered"], true, "thin raw mut→const lowers: {thin}");
    assert!(thin["unsupported"].as_array().unwrap().is_empty(), "{thin}");
    for (name, tag) in [("mutable_to_const", "Coercion(mut→const raw ptr)"), ("safe_to_unsafe", "Coercion(safe→unsafe fn-ptr)")] {
        let result = row(&refusals, name);
        assert_eq!(result["lowered"], false, "{name}: {result}");
        assert_eq!(result["spliced"], false, "{name}: {result}");
        assert!(result["unsupported"].to_string().contains(tag), "{name} preserves {tag}: {result}");
    }
}

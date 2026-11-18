//! Trust: only a direct borrow proves the local object behind a reborrow. The original
//! shared value retains one address before and after mutation of another object.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc, serde_json, trust_ir};

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(found.len(), 1, "one body for {name}");
    found[0]
}

fn arguments(line: &str, callee: usize) -> Option<Vec<String>> {
    let marker = format!("call @func.{callee}(");
    let (_, args) = line.split_once(&marker)?;
    Some(args.trim_end().strip_suffix(')').unwrap().split(',')
        .map(|arg| arg.trim().to_owned()).collect())
}

/// Run the same source, storage-identity and refusal controls under libtest.
#[test]
fn shared_raw_parameter_homes_preserve_original_addresses_and_refusals() {
    main();
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rustc().input("subject.rs").crate_name("reborrow").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:positive").run();
    let coverage: serde_json::Value = serde_json::from_str(
        &rfs::read_to_string("positive/reborrow.coverage.json")).unwrap();
    let text = trust_ir::by_display_path(&rfs::read_to_string("positive/reborrow.trust-ir.txt"));
    let mut names = Vec::new();
    let mut bodies = Vec::<Vec<String>>::new();
    let mut in_body = false;
    for line in text.lines() {
        if let Some((_, rest)) = line.split_once("fn @") {
            let name = if let Some(quoted) = rest.strip_prefix('"') {
                quoted.split('"').next().unwrap()
            } else { rest.split('(').next().unwrap() };
            names.push(name.to_owned());
            bodies.push(Vec::new());
            in_body = line.ends_with('{');
        } else if line.starts_with('}') { in_body = false; }
        else if in_body { bodies.last_mut().unwrap().push(line.split(';').next().unwrap().trim().to_owned()); }
    }
    let index = |name: &str| {
        let found: Vec<_> = names.iter().enumerate().filter(|(_, n)| *n == name).collect();
        assert_eq!(found.len(), 1, "exactly one callee {name}");
        found[0].0
    };
    for name in ["shared_parameter_with_direct_reborrow", "shared_local_with_direct_reborrow"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{row}");
        assert_eq!(row["spliced"], true, "{row}");
        assert_eq!(row["unsupported"].as_array().unwrap().len(), 0, "{row}");
        let body = &bodies[index(name)];
        let calls: Vec<_> = body.iter().filter_map(|line| arguments(line, index("same_wide"))).collect();
        assert_eq!(calls.len(), 2, "one identity call before and one after mutation: {body:?}");
        assert!(calls.iter().all(|call| call.len() == 2), "two identity arguments: {body:?}");
        let address = &calls[0][0];
        assert!(calls.iter().all(|call| call.iter().all(|arg| arg == address)),
            "all four borrows share the original address: {body:?}");
        assert_eq!(body.iter().filter(|line| line.starts_with(&format!("{address} = alloca "))).count(), 1,
            "the common address comes from exactly one local allocation: {body:?}");
        let bump: Vec<_> = body.iter().filter_map(|line| arguments(line, index("bump"))).collect();
        assert_eq!(bump.len(), 1, "the mutation is retained: {body:?}");
        assert_eq!(bump[0].len(), 1, "{body:?}");
        assert_ne!(bump[0][0], *address, "the mutation addresses a different local: {body:?}");
        let identity_positions: Vec<_> = body.iter().enumerate()
            .filter(|(_, line)| arguments(line, index("same_wide")).is_some())
            .map(|(position, _)| position).collect();
        let mutation = body.iter().position(|line| arguments(line, index("bump")).is_some()).unwrap();
        assert!(identity_positions[0] < mutation && mutation < identity_positions[1],
            "the identity checks bracket the mutation: {body:?}");
        assert_eq!(body.iter().filter(|line| {
            line.starts_with("store ") && line.ends_with(&format!(", ptr {address}"))
        }).count(), 1, "one initialization, no fresh snapshot at either borrow: {body:?}");
    }
    let raw = row(&coverage, "shared_raw_pointer_parameter");
    assert_eq!(raw["lowered"], true, "{raw}");
    assert!(raw["unsupported"].as_array().unwrap().is_empty(), "{raw}");
    let body = &bodies[index("shared_raw_pointer_parameter")];
    let calls: Vec<_> = body.iter().filter_map(|line|
        arguments(line, index("same_raw_pointer_location"))).collect();
    assert_eq!(calls.len(), 2, "{body:?}");
    let address = &calls[0][0];
    assert!(calls.iter().all(|call| call.len() == 2 && call.iter().all(|arg| arg == address)),
        "all shared pointer borrows use the original parameter home: {body:?}");
    assert_eq!(body.iter().filter(|line| line.starts_with(&format!("{address} = alloca "))).count(), 1);
    rfs::write("native.rs", format!("{}\nfn main() {{ assert!(shared_raw_pointer_parameter(std::ptr::null())); }}",
        rfs::read_to_string("subject.rs").replace("#![crate_type = \"lib\"]", "")));
    rustc().input("native.rs").edition("2021").arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=off").run();
    run_make_support::cmd("./native").run();
    let output = rustc().input("refusals.rs").crate_name("reborrow_refusals").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:negative").run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_str(
        &rfs::read_to_string("negative/reborrow_refusals.coverage.json")).unwrap();
    for (name, tag) in [
        ("same_root_reborrow", "Promote(non-scalar &mut param)"),
        ("raw_parameter_with_mutable_borrow", "Promote(non-scalar &mut param)"),
        ("unknown_root_reborrow", "Promote(non-scalar &mut param)"),
        ("raw_root", "Promote(non-scalar &mut param)"),
        ("ref_mut_pattern", "Promote(non-scalar &mut param)"),
        ("empty_array_with_disjoint_mutation", "Promote(non-scalar &mut local)"),
    ] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert_eq!(row["spliced"], false, "{name}: {row}");
        assert!(row["unsupported"].to_string().contains(tag), "{name} must retain {tag}: {row}");
    }
    let escaped = row(&coverage, "raw_parameter_address_escape");
    assert_eq!(escaped["lowered"], false, "a parameter's local home must not escape: {escaped}");
    assert_eq!(escaped["spliced"], false, "{escaped}");
    // Trust: c5e73dac73 (THIR-FLOAT-REFERENCE-STORAGE-1) moved primitive f32/f64 locals and
    // by-value parameters onto the owned homes integers use, so the bounded shared-float lane's
    // no-mutable-borrow condition no longer applies to them; the empty-array lane keeps it above.
    for name in ["float_local_with_disjoint_mutation", "float_parameter_with_disjoint_mutation"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert_eq!(row["unsupported"].as_array().unwrap().len(), 0, "{name}: {row}");
    }
}

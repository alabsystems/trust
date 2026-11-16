//! A supported break value must not hide its operand's lifetime-long storage.
//! Verification is off; these structural assertions grant no proof authority.
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

fn check_storage_and_exit(body: &str, expected_blocks: usize) {
    let lines: Vec<_> = body.lines()
        .map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let blocks: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        let header = line.strip_suffix(':')?;
        let (name, params) = match header.split_once('(') {
            Some((name, params)) => (name, params.strip_suffix(')')?),
            None => (header, ""),
        };
        name.starts_with("bb").then_some((position, name, params))
    }).collect();
    assert_eq!(blocks.len(), expected_blocks, "entry, loop bodies and result exit: {body}");
    let block_lines = |index: usize| {
        let end = blocks.get(index + 1).map_or(lines.len(), |block| block.0);
        &lines[blocks[index].0 + 1..end]
    };
    let exits: Vec<_> = (0..blocks.len()).filter(|&index| {
        block_lines(index).iter().any(|line| line.starts_with("ret "))
    }).collect();
    assert_eq!(exits.len(), 1, "one actual return block: {body}");
    let exit_index = exits[0];
    let (input, ty) = blocks[0].2.split_once(':').expect("typed entry input");
    assert_eq!(ty.trim(), "u32", "one scalar input: {body}");
    for (index, block) in blocks.iter().enumerate().skip(1) {
        if index != exit_index {
            assert_eq!(block.2, "", "memory-backed value is not SSA loop-carried: {body}");
        }
    }
    let (result, ty) = blocks[exit_index].2.split_once(':').expect("typed loop result");
    assert_eq!(ty.trim(), "u32", "one scalar exit result: {body}");
    let slots: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.split_once(" = alloca u32").map(|(value, _)| (position, value))
    }).collect();
    assert_eq!(slots.len(), 1, "one lifetime-long scalar slot: {body}");
    let slot = slots[0].1;
    let seven: Vec<_> = lines.iter().filter_map(|line| {
        line.strip_suffix(" = const u32 7")
    }).collect();
    assert_eq!(seven.len(), 1, "one mutation value: {body}");
    let stores: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.strip_prefix("store u32 ")?
            .strip_suffix(&format!(", ptr {slot}")).map(|value| (position, value))
    }).collect();
    assert_eq!(stores.len(), 2, "initialize and mutate the same slot: {body}");
    assert_eq!(stores[0].1, input.trim(), "initialize from original input: {body}");
    assert_eq!(stores[1].1, seven[0], "mutation stores seven: {body}");
    let body_index = blocks.iter().rposition(|block| block.0 < stores[1].0)
        .expect("mutation belongs to a block");
    let loads: Vec<_> = lines.iter().enumerate().filter_map(|(position, line)| {
        line.strip_suffix(&format!(" = load u32, ptr {slot}"))
            .map(|value| (position, value))
    }).collect();
    assert_eq!(loads.len(), 1, "load the mutated value from the real slot: {body}");
    let enter = format!("br {}", blocks[1].1);
    let exit = format!("br {}({})", blocks[exit_index].1, loads[0].1);
    let enter_pos = lines.iter().position(|line| *line == enter)
        .expect("entry branches to loop body with no invented SSA state");
    let exit_pos = lines.iter().position(|line| *line == exit)
        .expect("break passes the actual loaded value to the result block");
    assert!(blocks[0].0 < slots[0].0 && slots[0].0 < stores[0].0
        && stores[0].0 < enter_pos && enter_pos < blocks[1].0
        && blocks[body_index].0 < stores[1].0 && stores[1].0 < loads[0].0
        && loads[0].0 < exit_pos,
        "initialization precedes entry; mutation, load and branch share order: {body}");
    assert!(block_lines(body_index).contains(&exit.as_str()),
        "mutation block branches to the actual return block: {body}");
    assert_eq!(block_lines(body_index).iter().rev().find(|line| !line.is_empty()),
        Some(&exit.as_str()), "the storage path ends with the result edge: {body}");
    // Block allocation/printing order is not control-flow order: an outer
    // exit can be allocated before the inner loop body. Follow exact edges.
    let mut current = 0;
    let mut visited = Vec::new();
    while current != body_index {
        assert!(!visited.contains(&current), "cycle before mutation: {body}");
        visited.push(current);
        assert_ne!(current, exit_index, "return before mutation: {body}");
        let branches: Vec<_> = block_lines(current).iter()
            .filter_map(|line| line.strip_prefix("br ")).collect();
        assert_eq!(branches.len(), 1, "one unconditional edge before mutation: {body}");
        current = blocks.iter().position(|block| block.1 == branches[0])
            .expect("edge names an existing block without invented state");
    }
    visited.push(body_index);
    assert_eq!(visited.len() + 1, blocks.len(),
        "every non-return block lies on the storage path: {body}");
    let returns: Vec<_> = lines.iter().filter_map(|line| line.strip_prefix("ret ")).collect();
    assert_eq!(returns, vec![result.trim()],
        "return the scalar received by the exit block: {body}");
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
    rustc().input("subject.rs").crate_name("break_value_temporaries").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:positive").run();
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("positive/break_value_temporaries.coverage.json"),
    ).expect("complete source coverage");
    no_proof_claim(&coverage);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 4);
    let text = trust_ir::by_display_path(
        &rfs::read_to_string("positive/break_value_temporaries.trust-ir.txt"),
    );
    for name in ["parameter_before_break", "parameter_in_break", "local_before_break", "local_in_break"] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["spliced"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        check_storage_and_exit(body(&text, name), 3);
    }

    let output = rustc().input("refusals.rs").crate_name("break_value_refusals").edition("2021")
        .arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:negative").run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("negative/break_value_refusals.coverage.json"),
    ).expect("complete refusal coverage");
    no_proof_claim(&coverage);
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 2);
    for (name, tag) in [("borrowed_result", "Break(borrow ptr value)")] {
        let row = row(&coverage, name);
        assert_eq!(row["lowered"], false, "{name}: {row}");
        assert_eq!(row["spliced"], false, "{name}: {row}");
        assert!(row["unsupported"].to_string().contains(tag), "{name} retains {tag}: {row}");
    }
    let outer = row(&coverage, "outer_label");
    assert_eq!(outer["lowered"], true, "{outer}");
    assert_eq!(outer["spliced"], true, "{outer}");
    assert!(outer["unsupported"].as_array().unwrap().is_empty(), "{outer}");
    let text = trust_ir::by_display_path(
        &rfs::read_to_string("negative/break_value_refusals.trust-ir.txt"),
    );
    check_storage_and_exit(body(&text, "outer_label"), 4);
}

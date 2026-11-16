//! A discarded cast/ascription still executes its assignment side effects.
//! Inspect loop state directly: a fallback to original MIR is not evidence
//! that the independently emitted Trust IR carries the right values.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

struct Block {
    label: String,
    parameters: Vec<(String, String)>,
    lines: Vec<String>,
}

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let plain = format!("fn @{name}(");
    let quoted = format!("fn @\"{name}\"(");
    text.split_once(&plain).or_else(|| text.split_once(&quoted)).unwrap().1
        .split_once("\n}\n").unwrap().0
}

fn blocks(text: &str) -> Vec<Block> {
    let mut result: Vec<Block> = Vec::new();
    for line in text.lines().map(|line| line.split(';').next().unwrap().trim()) {
        if let Some(header) = line.strip_suffix(':').filter(|header| header.starts_with("bb")) {
            let (label, arguments) = match header.split_once('(') {
                Some((label, args)) => (label, args.strip_suffix(')').unwrap()),
                None => (header, ""),
            };
            assert!(label[2..].bytes().all(|byte| byte.is_ascii_digit()));
            let parameters = if arguments.is_empty() {
                Vec::new()
            } else {
                arguments.split(',').map(|argument| {
                    let (value, ty) = argument.trim().split_once(':').unwrap();
                    (value.trim().to_owned(), ty.trim().to_owned())
                }).collect()
            };
            result.push(Block { label: label.to_owned(), parameters, lines: Vec::new() });
        } else if !line.is_empty() {
            if let Some(block) = result.last_mut() {
                block.lines.push(line.to_owned());
            }
        }
    }
    result
}

fn edges(block: &Block) -> Vec<(String, Vec<String>)> {
    let mut result = Vec::new();
    for line in &block.lines {
        if !line.starts_with("br ") && !line.starts_with("condbr ") {
            continue;
        }
        for (start, _) in line.match_indices("bb") {
            let tail = &line[start..];
            let end = 2 + tail[2..].bytes().take_while(u8::is_ascii_digit).count();
            assert!(end > 2);
            let arguments = if let Some(rest) = tail[end..].strip_prefix('(') {
                let text = rest.split_once(')').unwrap().0;
                text.split(',').filter(|arg| !arg.trim().is_empty())
                    .map(|arg| arg.trim().to_owned()).collect()
            } else {
                Vec::new()
            };
            result.push((tail[..end].to_owned(), arguments));
        }
    }
    result
}

fn increment(definitions: &BTreeMap<String, String>, blocks: &[Block], input: &str) -> String {
    let prefix = format!("add.overflow u32 {input}, ");
    let matches: Vec<_> = definitions.iter().filter_map(|(result, operation)| {
        operation.strip_prefix(&prefix).map(|right| {
            assert_eq!(definitions.get(right).map(String::as_str), Some("const u32 1"));
            (result.clone(), operation.clone())
        })
    }).collect();
    assert_eq!(matches.len(), 1, "one increment of carried value {input}");
    let (results, operation) = &matches[0];
    let outputs: Vec<_> = results.split(',').map(str::trim).collect();
    assert_eq!(outputs.len(), 2, "checked addition returns value and overflow flag");
    let select_prefix = format!("select bool {}, ", outputs[1]);
    let selections: Vec<_> = definitions.iter().filter_map(|(result, operation)| {
        operation.strip_prefix(&select_prefix).map(|values| {
            let (if_overflow, if_clear) = values.split_once(", ").unwrap();
            assert_eq!(definitions.get(if_overflow).map(String::as_str), Some("const bool false"));
            assert_eq!(definitions.get(if_clear).map(String::as_str), Some("const bool true"));
            (result.clone(), operation.clone())
        })
    }).collect();
    assert_eq!(selections.len(), 1, "negate this exact overflow flag");
    let (clear, selection) = &selections[0];
    let addition_line = format!("{results} = {operation}");
    let owners: Vec<_> = blocks.iter().filter(|block| block.lines.contains(&addition_line)).collect();
    assert_eq!(owners.len(), 1);
    let lines = &owners[0].lines;
    let addition_at = lines.iter().position(|line| line == &addition_line).unwrap();
    let select_at = lines.iter().position(|line| line == &format!("{clear} = {selection}")).unwrap();
    let assert_at = lines.iter().position(|line|
        line == &format!("assert {clear}, overflow add")).unwrap();
    assert!(addition_at < select_at && select_at < assert_at, "keep the checked increment");
    outputs[0].to_owned()
}

fn reaches(blocks: &[Block], start: &str, expected: &str, forbidden: &str) {
    let mut current = start.to_owned();
    let mut visited = Vec::new();
    while current != expected {
        assert_ne!(current, forbidden, "condition took the opposite loop path");
        assert!(!visited.contains(&current), "unexpected cycle before loop boundary");
        visited.push(current.clone());
        let block = blocks.iter().find(|block| block.label == current).unwrap();
        assert!(block.lines.last().unwrap().starts_with("br "));
        let successors = edges(block);
        assert_eq!(successors.len(), 1, "straight-line branch to loop boundary");
        current = successors[0].0.clone();
    }
}

fn check_loop(text: &str, nested: bool) {
    assert!(!text.contains("undef"));
    let blocks = blocks(text);
    let definitions: BTreeMap<String, String> = blocks.iter().flat_map(|block| &block.lines)
        .filter_map(|line| line.split_once(" = "))
        .map(|(value, instruction)| (value.to_owned(), instruction.to_owned())).collect();
    let entry = &blocks[0];
    assert!(entry.parameters.is_empty());
    let entry_edges = edges(entry);
    assert_eq!(entry_edges.len(), 1);
    let header = blocks.iter().find(|block| block.label == entry_edges[0].0).unwrap();
    assert_eq!(header.parameters.len(), 2, "both tick and sum must cross the back edge");
    assert!(header.parameters.iter().all(|(_, ty)| ty == "u32"));
    assert_eq!(entry_edges[0].1.len(), 2);
    for argument in &entry_edges[0].1 {
        assert_eq!(definitions.get(argument).map(String::as_str), Some("const u32 0"));
    }
    let tick = &header.parameters[0].0;
    let sum = &header.parameters[1].0;
    let next_tick = increment(&definitions, &blocks, tick);
    let next_sum = if nested {
        let candidates: Vec<_> = blocks.iter().filter(|block| {
            block.parameters.len() == 1 && definitions.values().any(|operation|
                operation.starts_with(&format!("add.overflow u32 {}, ", block.parameters[0].0)))
        }).collect();
        assert_eq!(candidates.len(), 1, "one inner loop carries sum");
        let inner = candidates[0];
        let inner_entries: Vec<_> = blocks.iter().flat_map(edges)
            .filter(|(target, _)| target == &inner.label).collect();
        assert_eq!(inner_entries, vec![(inner.label.clone(), vec![sum.clone()])]);
        let inner_sum = increment(&definitions, &blocks, &inner.parameters[0].0);
        let exits: Vec<_> = edges(inner).into_iter()
            .filter(|(_, args)| args.len() == 1 && args[0] == inner_sum)
            .collect();
        assert_eq!(exits.len(), 1);
        let exit = blocks.iter().find(|block| block.label == exits[0].0).unwrap();
        assert_eq!(exit.parameters.len(), 1);
        assert_eq!(exit.parameters[0].1, "u32");
        exit.parameters[0].0.clone()
    } else {
        increment(&definitions, &blocks, sum)
    };
    let back_edges: Vec<_> = blocks.iter().filter(|block| block.label != entry.label)
        .flat_map(edges).filter(|(target, _)| target == &header.label).collect();
    assert_eq!(back_edges, vec![(header.label.clone(), vec![next_tick.clone(), next_sum.clone()])]);

    let compare_prefix = format!("icmp uge u32 {next_tick}, ");
    let comparisons: Vec<_> = definitions.iter().filter_map(|(value, operation)| {
        operation.strip_prefix(&compare_prefix).map(|bound| {
            assert_eq!(definitions.get(bound).map(String::as_str), Some("const u32 3"));
            value.clone()
        })
    }).collect();
    assert_eq!(comparisons.len(), 1);
    let condition_blocks: Vec<_> = blocks.iter().filter(|block| block.lines.iter()
        .any(|line| line.starts_with(&format!("condbr {}, ", comparisons[0])))).collect();
    assert_eq!(condition_blocks.len(), 1);
    let routes = edges(condition_blocks[0]);
    assert_eq!(routes.len(), 2, "condition has true and false targets");

    let returns: Vec<_> = blocks.iter().filter_map(|block| {
        block.lines.iter().find_map(|line| line.strip_prefix("ret "))
            .map(|value| (block, value))
    }).collect();
    assert_eq!(returns.len(), 1);
    let (exit, returned) = returns[0];
    assert_eq!(exit.parameters.len(), 3, "loop result followed by both carried locals");
    assert_eq!(exit.parameters[0].0, returned);
    let exit_edges: Vec<_> = blocks.iter().flat_map(edges)
        .filter(|(target, _)| target == &exit.label).collect();
    assert_eq!(exit_edges, vec![(exit.label.clone(), vec![next_sum.clone(), next_tick, next_sum])]);
    reaches(&blocks, &routes[0].0, &exit.label, &header.label);
    reaches(&blocks, &routes[1].0, &header.label, &exit.label);
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let output = cmd(rustc_path()).args([
        "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=loop_wrappers",
        "--emit=mir", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        "-Ztrust-dump=ir:ir", "-o", "loop_wrappers.mir",
    ]).run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/loop_wrappers.coverage.json"),
    ).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let names = ["direct", "cast", "value_ascribed", "index_direct",
                 "place_ascribed", "nested_direct", "nested_cast"];
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len());
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/loop_wrappers.trust-ir.txt"));
    for name in names {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1);
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let interpreter = &row["differentials"]["interpreter"];
        assert_eq!(interpreter["verdict"], "agreed", "{name}: {row}");
        let samples = interpreter["samples"].as_u64().unwrap();
        assert!(samples > 0, "{name}: {row}");
        assert!(row["spliced"].is_boolean());
        eprintln!("loop wrapper {name}: spliced={}", row["spliced"]);
        check_loop(body(&text, name), name.starts_with("nested_"));
    }
}

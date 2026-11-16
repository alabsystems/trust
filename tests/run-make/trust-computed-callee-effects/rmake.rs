//! A computed function-item callee executes once, before its arguments.
//! These are direct-IR structure checks with verification disabled, not proof claims.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use std::collections::BTreeMap;

struct Body<'a> {
    parameters: Vec<(&'a str, &'a str)>,
    lines: Vec<&'a str>,
}

struct Arithmetic<'a> {
    at: usize,
    checked_at: usize,
    value: &'a str,
}

struct Call<'a> {
    at: usize,
    result: &'a str,
    arguments: Vec<&'a str>,
}

fn row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
        .filter(|row| row["def_path"] == name).collect();
    assert_eq!(rows.len(), 1, "one coverage row for {name}");
    rows[0]
}

fn body_text<'a>(text: &'a str, name: &str) -> &'a str {
    let plain = format!("fn @{name}(");
    let quoted = format!("fn @\"{name}\"(");
    text.split_once(&plain).or_else(|| text.split_once(&quoted)).unwrap().1
        .split_once("\n}\n").unwrap().0
}

fn body<'a>(text: &'a str, name: &str) -> Body<'a> {
    let text = body_text(text, name);
    assert!(!text.contains("undef"), "no fabricated value in {name}");
    let mut parameters = None;
    let mut lines = Vec::new();
    for line in text.lines().map(|line| line.split(" ;").next().unwrap().trim()) {
        if line.starts_with("bb") && line.ends_with(':') {
            assert!(parameters.is_none(), "straight-line fixture has one block: {name}");
            let args = if line == "bb0:" {
                ""
            } else {
                line.strip_prefix("bb0(").unwrap().strip_suffix("):").unwrap()
            };
            parameters = Some(args.split(',').filter(|arg| !arg.is_empty()).map(|arg| {
                let (value, ty) = arg.trim().split_once(':').unwrap();
                (value.trim(), ty.trim())
            }).collect());
        } else if parameters.is_some() && !line.is_empty() {
            lines.push(line);
        }
    }
    assert!(name == "borrowed_reify" || !lines.iter().any(|line|
        line.contains("alloca ") || line.starts_with("store ") || line.contains(" = load ")));
    Body { parameters: parameters.expect("entry block"), lines }
}

fn assignments<'a>(body: &Body<'a>) -> Vec<(usize, &'a str, &'a str)> {
    body.lines.iter().enumerate().filter_map(|(i, line)| {
        let (result, operation) = line.split_once(" = ")?;
        Some((i, result, operation))
    }).collect()
}

fn definition<'a>(body: &Body<'a>, value: &str) -> (usize, &'a str) {
    let found: Vec<_> = assignments(body).into_iter().filter(|(_, result, _)| *result == value).collect();
    assert_eq!(found.len(), 1, "one definition of {value}");
    (found[0].0, found[0].2)
}

fn constant<'a>(body: &Body<'a>, ty: &str, value: &str) -> &'a str {
    let operation = format!("const {ty} {value}");
    let found: Vec<_> = assignments(body).into_iter().filter(|(_, _, op)| *op == operation).collect();
    assert_eq!(found.len(), 1, "one {operation}");
    found[0].1
}

fn arithmetic<'a>(body: &Body<'a>, opcode: &str, input: &str, right: &str) -> Arithmetic<'a> {
    let prefix = format!("{opcode}.overflow u32 ");
    let found: Vec<_> = assignments(body).into_iter()
        .filter(|(_, _, op)| op.starts_with(&prefix)).collect();
    assert_eq!(found.len(), 1, "one checked {opcode}");
    let (at, outputs, operation) = found[0];
    let (left, rhs) = operation.strip_prefix(&prefix).unwrap().split_once(", ").unwrap();
    assert_eq!(left, input, "{opcode} consumes the preceding value");
    assert_eq!(definition(body, rhs).1, format!("const u32 {right}"));
    let outputs: Vec<_> = outputs.split(',').map(str::trim).collect();
    assert_eq!(outputs.len(), 2, "checked arithmetic has a value and overflow flag");
    let select_prefix = format!("select bool {}, ", outputs[1]);
    let selections: Vec<_> = assignments(body).into_iter()
        .filter(|(_, _, op)| op.starts_with(&select_prefix)).collect();
    assert_eq!(selections.len(), 1);
    let (select_at, clear, operation) = selections[0];
    let (if_overflow, if_clear) = operation.strip_prefix(&select_prefix).unwrap()
        .split_once(", ").unwrap();
    assert_eq!(definition(body, if_overflow).1, "const bool false");
    assert_eq!(definition(body, if_clear).1, "const bool true");
    let assertion = format!("assert {clear}, overflow {opcode}");
    let checks: Vec<_> = body.lines.iter().enumerate()
        .filter(|(_, line)| **line == assertion).collect();
    assert_eq!(checks.len(), 1);
    let checked_at = checks[0].0;
    assert!(at < select_at && select_at < checked_at);
    Arithmetic { at, checked_at, value: outputs[0] }
}

fn direct_calls<'a>(body: &Body<'a>, identity: u64, count: usize) -> Vec<Call<'a>> {
    let all: Vec<_> = assignments(body).into_iter().filter(|(_, _, op)| op.starts_with("call ")).collect();
    assert_eq!(all.len(), count);
    all.into_iter().map(|(at, result, operation)| {
        let args = operation.strip_prefix(&format!("call @func.{identity}(")).unwrap()
            .strip_suffix(')').unwrap();
        let arguments: Vec<_> = args.split(',').filter(|arg| !arg.is_empty()).map(str::trim).collect();
        assert_eq!(arguments.len(), 1);
        Call { at, result, arguments }
    }).collect()
}

fn indirect_call<'a>(body: &Body<'a>, text: &str, identity: u64) -> (Call<'a>, usize) {
    assert!(direct_calls(body, identity, 0).is_empty());
    let calls: Vec<_> = assignments(body).into_iter()
        .filter(|(_, _, op)| op.starts_with("call_indirect ")).collect();
    assert_eq!(calls.len(), 1);
    let (at, result, operation) = calls[0];
    let (callee, tail) = operation.strip_prefix("call_indirect ").unwrap().split_once('(').unwrap();
    let (signature, arguments) = tail.split_once(")(").unwrap();
    let argument = arguments.strip_suffix(") cc=rustcc").unwrap();
    assert!(argument.starts_with('%') && !argument.contains(','));
    assert!(text.lines().any(|line| line == format!("{signature} = (u32) -> (u32)")));
    let (pointer_at, pointer) = definition(body, callee);
    assert!(pointer.starts_with("const ") && pointer.ends_with(&format!(" fndef<func.{identity}>")));
    assert!(pointer_at < at);
    (Call { at, result, arguments: vec![argument] }, pointer_at)
}

fn check_borrowed_reify(body: &Body<'_>, text: &str, identity: u64) {
    assert!(body.parameters.is_empty());
    no_arithmetic(body);
    let slots: Vec<_> = assignments(body).into_iter()
        .filter(|(_, _, operation)| operation.starts_with("alloca ")).collect();
    assert_eq!(slots.len(), 1);
    let (slot_at, slot, operation) = slots[0];
    assert_eq!(operation, "alloca u32");
    let zero = constant(body, "u32", "0");
    let seven = constant(body, "u32", "7");
    let stores: Vec<_> = body.lines.iter().enumerate()
        .filter(|(_, line)| line.starts_with("store ")).collect();
    assert_eq!(stores.len(), 2);
    assert_eq!(*stores[0].1, format!("store u32 {zero}, ptr {slot}"));
    assert_eq!(*stores[1].1, format!("store u32 {seven}, ptr {slot}"));
    assert!(slot_at < stores[0].0 && stores[0].0 < stores[1].0);
    let loads: Vec<_> = assignments(body).into_iter()
        .filter(|(_, _, operation)| operation.starts_with("load ")).collect();
    assert_eq!(loads.len(), 1);
    let (load_at, loaded, operation) = loads[0];
    assert_eq!(operation, format!("load u32, ptr {slot}"));
    let (call, pointer_at) = indirect_call(body, text, identity);
    assert!(stores[1].0 < pointer_at && pointer_at < load_at && load_at < call.at,
        "callee write and reification precede the argument's current-value read");
    assert_eq!(call.arguments, [loaded]);
    returns(body, call.result);
}

fn no_arithmetic(body: &Body<'_>) {
    assert!(!assignments(body).iter().any(|(_, _, op)|
        op.starts_with("add.") || op.starts_with("mul.")));
}

fn returns(body: &Body<'_>, value: &str) {
    let expected = format!("ret {value}");
    assert_eq!(body.lines.last().copied(), Some(expected.as_str()));
    assert_eq!(body.lines.iter().filter(|line| line.starts_with("ret ")).count(), 1);
}

struct Block {
    label: String,
    parameters: Vec<(String, String)>,
    lines: Vec<String>,
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

// Bind the computed callee's mutation to both loop carry and the observed result.
fn check_loop(text: &str, module: &str, identity: u64, nested: bool, indirect: bool) {
    assert!(!text.contains("undef"));
    let blocks = blocks(text);
    assert!(!blocks.iter().flat_map(|block| &block.lines).any(|line|
        line.contains("alloca ") || line.starts_with("store ") || line.contains(" = load ")));
    let all_definitions: Vec<_> = blocks.iter().flat_map(|block| &block.lines)
        .filter_map(|line| line.split_once(" = ")).collect();
    let definitions: BTreeMap<String, String> = all_definitions.iter()
        .map(|(value, instruction)| (value.to_string(), instruction.to_string())).collect();
    assert_eq!(definitions.len(), all_definitions.len(), "one definition per SSA output");
    assert_eq!(definitions.values().filter(|op| op.starts_with("add")).count(), 1);
    assert!(!definitions.values().any(|op| op.starts_with("mul")));
    let entry = &blocks[0];
    assert!(entry.parameters.is_empty());
    let entry_edges = edges(entry);
    assert_eq!(entry_edges.len(), 1);
    let header = blocks.iter().find(|block| block.label == entry_edges[0].0).unwrap();
    assert_eq!(header.parameters.len(), 1, "count must cross the outer back edge");
    assert_eq!(header.parameters[0].1, "u32");
    assert_eq!(entry_edges[0].1.len(), 1);
    assert_eq!(definitions.get(&entry_edges[0].1[0]).map(String::as_str), Some("const u32 0"));
    let count = &header.parameters[0].0;
    let (next_count, effect_block, call_block) = if nested {
        let candidates: Vec<_> = blocks.iter().filter(|block| {
            block.label != header.label && block.parameters.len() == 1
                && definitions.values().any(|op|
                    op.starts_with(&format!("add.overflow u32 {}, ", block.parameters[0].0)))
        }).collect();
        assert_eq!(candidates.len(), 1, "inner loop carries the computed callee's count");
        let inner = candidates[0];
        assert_eq!(inner.parameters[0].1, "u32");
        let inner_entries: Vec<_> = blocks.iter().flat_map(edges)
            .filter(|(target, _)| target == &inner.label).collect();
        assert_eq!(inner_entries, vec![(inner.label.clone(), vec![count.clone()])]);
        let inner_count = increment(&definitions, &blocks, &inner.parameters[0].0);
        let exits: Vec<_> = edges(inner).into_iter()
            .filter(|(_, args)| args == &vec![inner_count.clone()]).collect();
        assert_eq!(exits.len(), 1, "inner break exports the incremented count");
        let exit = blocks.iter().find(|block| block.label == exits[0].0).unwrap();
        assert_eq!(exit.parameters.len(), 1);
        assert_eq!(exit.parameters[0].1, "u32");
        (exit.parameters[0].0.clone(), inner, exit)
    } else {
        (increment(&definitions, &blocks, count), header, header)
    };
    let calls: Vec<_> = blocks.iter().flat_map(|block| block.lines.iter().enumerate()
        .filter_map(move |(index, line)| line.split_once(" = ")
            .filter(|(_, op)| op.starts_with("call ") || op.starts_with("call_indirect "))
            .map(move |(result, op)| (block, index, result, op)))).collect();
    assert_eq!(calls.len(), 1, "callee and loop each emit exactly one call site");
    let (owner, call_at, _, operation) = calls[0];
    assert_eq!(owner.label, call_block.label);
    let checked_at = effect_block.lines.iter().position(|line|
        line.starts_with("assert ") && line.ends_with(", overflow add")).unwrap();
    if indirect {
        assert!(!nested);
        let body = Body {
            parameters: call_block.parameters.iter().map(|(value, ty)|
                (value.as_str(), ty.as_str())).collect(),
            lines: call_block.lines.iter().map(String::as_str).collect(),
        };
        let (call, pointer_at) = indirect_call(&body, module, identity);
        assert_eq!(call.arguments, [next_count.as_str()], "indirect call consumes updated count");
        assert_eq!(call.at, call_at);
        assert!(checked_at < pointer_at, "callee effects precede loop pointer reification");
    } else {
        assert_eq!(operation, format!("call @func.{identity}({next_count})"),
            "call consumes the updated count");
    }
    if nested {
        assert!(checked_at < effect_block.lines.len() - 1);
        assert!(effect_block.lines.last().unwrap().starts_with("br "));
    } else {
        assert!(checked_at < call_at);
    }
    let back_edges: Vec<_> = blocks.iter().filter(|block| block.label != entry.label)
        .flat_map(edges).filter(|(target, _)| target == &header.label).collect();
    assert_eq!(back_edges, vec![(header.label.clone(), vec![next_count.clone()])]);
    let compare_prefix = format!("icmp uge u32 {next_count}, ");
    let comparisons: Vec<_> = definitions.iter().filter_map(|(value, operation)| {
        operation.strip_prefix(&compare_prefix).map(|bound| {
            assert_eq!(definitions.get(bound).map(String::as_str), Some("const u32 3"));
            value.clone()
        })
    }).collect();
    assert_eq!(comparisons.len(), 1);
    let comparison_at = call_block.lines.iter().position(|line|
        line.starts_with(&format!("{} = ", comparisons[0]))).unwrap();
    assert!(call_at < comparison_at, "callee call precedes the loop exit test");
    let condition_blocks: Vec<_> = blocks.iter().filter(|block| block.lines.iter()
        .any(|line| line.starts_with(&format!("condbr {}, ", comparisons[0])))).collect();
    assert_eq!(condition_blocks.len(), 1);
    assert_eq!(condition_blocks[0].label, call_block.label);
    let routes = edges(condition_blocks[0]);
    assert_eq!(routes.len(), 2);
    let returns: Vec<_> = blocks.iter().filter_map(|block| {
        block.lines.iter().find_map(|line| line.strip_prefix("ret "))
            .map(|value| (block, value))
    }).collect();
    assert_eq!(returns.len(), 1);
    let (exit, returned) = returns[0];
    assert_eq!(exit.parameters.len(), 2, "loop result followed by the carried count");
    assert!(exit.parameters.iter().all(|(_, ty)| ty == "u32"));
    assert_eq!(exit.parameters[0].0, returned);
    let exit_edges: Vec<_> = blocks.iter().flat_map(edges)
        .filter(|(target, _)| target == &exit.label).collect();
    assert_eq!(exit_edges, vec![(exit.label.clone(), vec![next_count.clone(), next_count])]);
    reaches(&blocks, &routes[0].0, &exit.label, &header.label);
    reaches(&blocks, &routes[1].0, &header.label, &exit.label);
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
    let coverage = compile("subject.rs", "computed_callee", "positive");
    let names = ["identity", "direct", "computed", "ordered", "nested", "alias", "diverged",
                 "pointer", "pointer_inline", "loop_callee", "nested_loop_callee",
                 "reified_loop_callee", "borrowed_reify"];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    assert_eq!(coverage["totals"]["bodies"], 13);
    assert_eq!(coverage["totals"]["lowered"], 13);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["totals"]["unsupported"], 0);
    let text = trust_ir::by_display_path(&rfs::read_to_string("positive/computed_callee.trust-ir.txt"));
    let identity = row(&coverage, "identity")["func_id"].as_u64().unwrap();
    for name in names {
        let result = row(&coverage, name);
        assert_eq!(result["lowered"], true, "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
        eprintln!("computed callee {name}: spliced={} differential={}", result["spliced"], result["differentials"]);
        if name == "loop_callee" || name == "nested_loop_callee" || name == "reified_loop_callee" {
            check_loop(body_text(&text, name), &text, identity,
                name == "nested_loop_callee", name == "reified_loop_callee");
            continue;
        }
        let body = body(&text, name);
        if name == "borrowed_reify" {
            check_borrowed_reify(&body, &text, identity);
            continue;
        }
        if name != "pointer" && name != "pointer_inline" {
            assert!(!body.lines.iter().any(|line| line.contains("call_indirect ")));
        }
        let arithmetic_count = assignments(&body).iter().filter(|(_, _, op)|
            op.starts_with("add") || op.starts_with("mul")).count();
        assert_eq!(arithmetic_count, match name {
            "identity" | "diverged" => 0,
            "direct" | "computed" => 1,
            _ => 2,
        });
        if name == "identity" {
            assert_eq!(body.parameters.len(), 1);
            assert_eq!(body.parameters[0].1, "u32");
            assert!(direct_calls(&body, identity, 0).is_empty());
            no_arithmetic(&body);
            returns(&body, body.parameters[0].0);
            continue;
        }
        if name == "diverged" {
            assert!(body.parameters.is_empty());
            assert!(direct_calls(&body, identity, 0).is_empty());
            assert!(!body.lines.iter().any(|line| line.contains("call_indirect ")));
            no_arithmetic(&body);
            assert!(!assignments(&body).iter().any(|(_, _, op)| *op == "const u32 99"));
            returns(&body, constant(&body, "u32", "7"));
            continue;
        }
        let input = if name == "direct" || name == "computed" {
            assert_eq!(body.parameters.len(), 1);
            assert_eq!(body.parameters[0].1, "u32");
            body.parameters[0].0
        } else {
            assert!(body.parameters.is_empty());
            constant(&body, "u32", "0")
        };
        let added = arithmetic(&body, "add", input, "1");
        if name == "direct" || name == "computed" {
            assert!(!assignments(&body).iter().any(|(_, _, op)| op.starts_with("mul.")));
            let calls = direct_calls(&body, identity, 1);
            assert!(added.checked_at < calls[0].at);
            assert_eq!(calls[0].arguments, [added.value]);
            returns(&body, calls[0].result);
            continue;
        }
        let multiplied = arithmetic(&body, "mul", added.value, "10");
        assert!(added.checked_at < multiplied.at, "callee effect precedes argument effect");
        if name == "pointer" || name == "pointer_inline" {
            let (call, pointer_at) = indirect_call(&body, &text, identity);
            assert_eq!(call.arguments, [multiplied.value]);
            if name == "pointer" {
                assert!(pointer_at < added.at);
            } else {
                assert!(added.checked_at < pointer_at && pointer_at < multiplied.at,
                    "computed FnDef effects precede reification and argument evaluation");
            }
            assert!(multiplied.checked_at < call.at);
            returns(&body, call.result);
        } else {
            let calls = direct_calls(&body, identity, if name == "nested" { 2 } else { 1 });
            let final_call = calls.last().unwrap();
            assert!(multiplied.checked_at < final_call.at);
            assert_eq!(final_call.arguments, [multiplied.value]);
            if name == "nested" {
                assert!(added.checked_at < calls[0].at && calls[0].at < multiplied.at);
                assert_eq!(calls[0].arguments, [added.value]);
            }
            returns(&body, final_call.result);
        }
    }

    let coverage = compile("refusals.rs", "computed_callee_refusals", "negative");
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), 4);
    assert_eq!(coverage["totals"]["bodies"], 4);
    assert_eq!(coverage["totals"]["lowered"], 1);
    assert_eq!(row(&coverage, "identity")["lowered"], true);
    for name in ["conditional", "matched", "labeled"] {
        let result = row(&coverage, name);
        assert_eq!(result["lowered"], false, "{name}: {result}");
        assert_eq!(result["spliced"], false, "{name}: {result}");
        assert!(result["unsupported"].as_array().unwrap().iter()
            .any(|entry| entry[0] == "Call(computed fn-item callee)"), "{name}: {result}");
    }

    // Closure adapters are currently unspliced: these are metadata admission/refusal
    // controls, not evidence that an outer adapter body was emitted or executed.
    // The implicit return coercion in closure_effect sits inside the block, after
    // its increment; the explicit cast makes the effectful block the coercion source.
    let coverage = compile("closure_controls.rs", "closure_controls", "closure-controls");
    let names = ["closure_literal", "closure_literal::{closure#0}",
                 "closure_alias", "closure_alias::{closure#0}",
                 "closure_effect", "closure_effect::{closure#0}",
                 "closure_literal_cast", "closure_literal_cast::{closure#0}",
                 "closure_effect_cast", "closure_effect_cast::{closure#0}"];
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    assert_eq!(coverage["totals"]["bodies"], 10);
    assert_eq!(coverage["totals"]["lowered"], 9);
    assert_eq!(coverage["totals"]["spliced"], 5);
    assert_eq!(coverage["totals"]["initializer_bodies"], 0);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    for name in names {
        let result = row(&coverage, name);
        assert_eq!(result["kind"], "fn", "{name}: {result}");
        assert_eq!(result["symbolic"], false, "{name}: {result}");
        eprintln!("closure control {name}: lowered={} spliced={} differential={}",
            result["lowered"], result["spliced"], result["differentials"]);
        if name == "closure_effect_cast" {
            assert_eq!(result["lowered"], false, "{name}: {result}");
            assert_eq!(result["spliced"], false, "{name}: {result}");
            assert!(result["unsupported"].as_array().unwrap().iter()
                .any(|entry| entry[0] == "Coercion(closure→fn-ptr adapter)"),
                "{name}: {result}");
        } else {
            assert_eq!(result["lowered"], true, "{name}: {result}");
            assert!(result["unsupported"].as_array().unwrap().is_empty(), "{name}: {result}");
            if name.ends_with("::{closure#0}") {
                assert_eq!(result["spliced"], true, "closure bodies remain published: {result}");
            } else {
                assert_eq!(result["spliced"], false, "adapters remain unspliced: {result}");
                assert_eq!(result["splice_refusal"], "Splice(synthesized fn-pointer adapter)",
                    "{name}: {result}");
            }
        }
    }
}

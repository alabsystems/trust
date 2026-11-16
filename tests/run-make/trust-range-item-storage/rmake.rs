//! A borrowed range item has storage separate from the iterator counter.
//! Inspect the emitted program: LLVM execution alone cannot test the direct producer.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc, serde_json, trust_ir};

fn function<'a>(text: &'a str, name: &str) -> &'a str {
    let header = format!("fn @{name}(");
    let quoted = format!("fn @\"{name}\"(");
    let (_, tail) = text.split_once(&header).or_else(|| text.split_once(&quoted))
        .expect("emitted source function");
    tail.split_once("\n}\n").expect("complete function body").0
}

fn check_item_storage(body: &str, callee: usize) {
    let lines: Vec<_> = body.lines().map(|line| line.split(" ;").next().unwrap().trim()).collect();
    let slots: Vec<_> = lines.iter().filter_map(|line| {
        line.split_once(" = alloca u32").map(|(value, _)| value)
    }).collect();
    assert_eq!(slots.len(), 2, "one counter and one item slot: {body}");
    let (current, counter) = lines.iter().find_map(|line| {
        line.split_once(" = load u32, ptr ")
    }).expect("iterator current value loaded from its counter");
    assert!(slots.contains(&counter), "counter has its own allocation: {body}");
    let call = format!("call @func.{callee}(");
    let (call_pos, item) = lines.iter().enumerate().find_map(|(position, line)| {
        line.split_once(&call).map(|(_, rest)| {
            (position, rest.strip_suffix(')').expect("one pointer argument"))
        })
    }).expect("source helper receives the item address");
    assert!(slots.contains(&item), "item address names an allocation: {body}");
    assert_ne!(item, counter, "mutating the item must not mutate the counter: {body}");
    let copy = format!("store u32 {current}, ptr {item}");
    let copy_pos = lines.iter().position(|line| *line == copy)
        .expect("item slot initialized from the current value");
    let test_pos = lines.iter().position(|line| line.contains(&format!("icmp ult u32 {current},")))
        .expect("range exhaustion test");
    let branch_pos = lines.iter().position(|line| line.starts_with("condbr "))
        .expect("range test branches before item initialization");
    assert!(test_pos < branch_pos && branch_pos < copy_pos && copy_pos < call_pos,
        "initialize the item on the payload path before its borrow: {body}");
    assert_eq!(lines.iter().filter(|line| line.ends_with(&format!(", ptr {counter}"))
        && line.starts_with("store u32 ")).count(), 2,
        "only counter initialization and advancement store to the counter: {body}");
    let (advance_pos, advance) = lines.iter().enumerate().rev().find_map(|(position, line)| {
        line.strip_prefix("store u32 ").and_then(|rest| {
            rest.strip_suffix(&format!(", ptr {counter}")).map(|value| (position, value))
        })
    }).unwrap();
    let increment = lines.iter().find_map(|line| {
        line.strip_prefix(&format!("{advance} = add u32 {current}, "))
    }).expect("counter advances from its original current value");
    assert!(lines.contains(&format!("{increment} = const u32 1").as_str()),
        "counter advances by exactly one: {body}");
    assert!(advance_pos < call_pos, "item mutation cannot affect this advance: {body}");
    assert!(!body.contains("undef"), "item storage cannot hide a missing value: {body}");
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rustc().input("subject.rs").crate_name("range_item_storage").crate_type("lib")
        .edition("2024").arg("-Ztrust-verify=off").arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:ir").run();
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/range_item_storage.coverage.json"),
    ).expect("complete source coverage");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let rows = coverage["bodies"].as_array().expect("body inventory");
    for name in ["read", "bump", "shared_item", "mutated_item"] {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "one source body for {name}");
        assert_eq!(found[0]["lowered"], true, "{name}: {}", found[0]);
        assert_eq!(found[0]["spliced"], true, "{name}: {}", found[0]);
    }
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/range_item_storage.trust-ir.txt"));
    let names: Vec<_> = text.lines().filter_map(|line| {
        let (_, rest) = line.split_once("fn @")?;
        rest.split_once('(').map(|(name, _)| name.trim_matches('"'))
    }).collect();
    for (body, helper) in [("shared_item", "read"), ("mutated_item", "bump")] {
        let callee = names.iter().position(|name| *name == helper).expect("helper in module");
        check_item_storage(function(&text, body), callee);
    }
}

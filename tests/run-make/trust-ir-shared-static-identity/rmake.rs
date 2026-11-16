//! Trust: inspect the actual direct-THIR module, not an authored IR surrogate.
//!
//! Appending a fresh Global for every body used to give write_first and read_first
//! different allocations. A compiler exit or a check-pass test cannot detect that
//! error. Conversely, deduplicating equal initializers would incorrectly merge
//! FIRST, SECOND and IMMUTABLE. Both mistakes must fail this emitted-module test.
//! This is an identity regression, not a Rust refinement or concurrency proof.

use std::collections::BTreeSet;
use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

fn body_row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows = coverage["bodies"].as_array().expect("complete body inventory");
    let found: Vec<_> = rows.iter().filter(|row| row["def_path"].as_str() == Some(name)).collect();
    assert_eq!(found.len(), 1, "expected one coverage row for {name}: {found:?}");
    found[0]
}

/// WS5.2: `Function.name` is the link-time symbol; a body is found by its def
/// path, which the canonical text carries as `; #display-path: "..."`.
fn emitted_function<'a>(text: &'a str, name: &str) -> &'a str {
    let directive = format!("; #display-path: {name:?}\n");
    let mut found = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            let tail = &text[offset..];
            let end = tail.find("\n}\n").expect("emitted function must have a body") + 3;
            if tail[..end].contains(&directive) {
                found.push(&tail[..end]);
            }
        }
        offset += line.len();
    }
    assert_eq!(found.len(), 1, "expected one emitted body for {name}: {found:?}");
    found[0]
}

fn static_id(function: &str) -> usize {
    let mut ids = BTreeSet::new();
    for line in function.lines() {
        if let Some((_, rest)) = line.split_once("global_addr @global.") {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            assert!(digits > 0, "global address without a numeric identity: {line}");
            ids.insert(rest[..digits].parse::<usize>().expect("numeric global identity"));
        }
    }
    assert_eq!(ids.len(), 1, "expected one distinct static in actual body:\n{function}");
    *ids.first().expect("nonempty global identity set")
}

fn main() {
    let out = Path::new("shared-statics");
    rfs::create_dir(out);
    rustc()
        .input("subject.rs")
        .crate_name("shared_statics")
        .crate_type("lib")
        .edition("2024")
        .emit("trust-ir")
        .out_dir(out)
        .arg("-Ztrust-verify=off")
        .run();

    assert!(!rfs::read(out.join("shared_statics.trust-ir.bin")).is_empty());
    let text = rfs::read_to_string(out.join("shared_statics.trust-ir.txt"));
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        out.join("shared_statics.trust-ir.coverage.json"),
    ))
    .expect("valid coverage JSON");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);

    let names = [
        "write_first",
        "read_first",
        "read_first_again",
        "read_second",
        "read_immutable",
        "read_immutable_again",
        "write_then_read",
    ];
    for name in names {
        let row = body_row(&coverage, name);
        assert_eq!(row["lowered"], true, "{name} did not lower: {row}");
        assert_eq!(row["symbolic"], false, "{name} substituted a symbolic body: {row}");
        assert_eq!(row["spliced"], true, "{name} has no actual module body: {row}");
        assert_eq!(row["unsupported"].as_array().map(Vec::len), Some(0));
        assert!(row["func_id"].as_u64().is_some(), "{name} lacks a function identity");
        assert!(!emitted_function(&text, name).contains(" = undef "));
    }

    let first = static_id(emitted_function(&text, "write_first"));
    for name in ["read_first", "read_first_again"] {
        assert_eq!(static_id(emitted_function(&text, name)), first, "{name} copied FIRST");
    }
    let second = static_id(emitted_function(&text, "read_second"));
    let immutable = static_id(emitted_function(&text, "read_immutable"));
    assert_eq!(
        static_id(emitted_function(&text, "read_immutable_again")),
        immutable,
        "repeated immutable-static references lost their identity"
    );
    assert_eq!(
        BTreeSet::from([first, second, immutable]).len(),
        3,
        "distinct Rust statics must not merge because their initializers are equal"
    );
    // Display preserves Module.globals order; GlobalId is an index into that
    // exact table. Do not infer identity from a generated global's display name.
    let globals: Vec<_> = text.lines().filter(|line| line.starts_with("global ")).collect();
    for (id, mutable) in [(first, true), (second, true), (immutable, false)] {
        let declaration = globals.get(id).expect("referenced global must exist");
        assert_eq!(declaration.contains(" mut "), mutable, "{declaration}");
        assert!(declaration.ends_with(" u64 = 17"), "initializer changed: {declaration}");
    }

    assert!(emitted_function(&text, "write_first").contains("store "));
    assert!(emitted_function(&text, "read_first").contains("load "));
    let targets: Vec<u64> = emitted_function(&text, "write_then_read")
        .lines()
        .filter_map(|line| line.split_once("call @func."))
        .map(|(_, rest)| {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            rest[..digits].parse().expect("numeric direct callee identity")
        })
        .collect();
    let expected: Vec<_> = ["write_first", "read_first"]
        .into_iter()
        .map(|name| body_row(&coverage, name)["func_id"].as_u64().expect("spliced callee"))
        .collect();
    assert_eq!(targets, expected, "round trip must call the real writer then the real reader");
    let calls = &body_row(&coverage, "write_then_read")["calls"];
    assert_eq!(calls["resolved"], 2, "round trip must link both real bodies: {calls}");
    assert_eq!(calls["extern_decls"], 0);
    assert_eq!(calls["unresolved"], 0);
}

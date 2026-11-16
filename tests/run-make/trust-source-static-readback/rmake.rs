// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Inspect actual THIR StaticRef roots and rustc's cold CTFE allocations.
//!
//! The subject exercises the compiler diagnostic, not Clean's production helper.
//! The LazyLock source bodies must stay refused; the initializer graph earns no
//! proof authority, runtime-state claim, or executable-module admission.
//@ ignore-cross-compile
//@ only-apple

use std::collections::BTreeSet;
use std::mem::{align_of, size_of};
use std::path::Path;
use std::sync::{LazyLock, Once};

use run_make_support::{rfs, rustc, serde_json};
use serde_json::Value;

// The same declaration bytes supply the native-host layout check. No LazyLock
// is forced by this test, and no copy of its implementation is authored here.
#[path = "subject.rs"]
mod layout;

const CRATE: &str = "source_static_readback";
const STATIC_NAMES: [&str; 4] = ["FIRST", "SECOND", "SAME_AS_FIRST", "SELF_REF"];
const CLOSURE_STATIC_NAMES: [&str; 2] = ["CLOSURE_NAT", "CLOSURE_STRING"];
// `definition` disables trimming, not visible public reexports: this diagnostic
// spells core's FnOnce method through std. Stable DefPathHash/callee identities
// and distinct full Instance/substitution fingerprints below bind the functions.
const FN_ONCE_CALL_ONCE: &str = "std::ops::FnOnce::call_once";

fn array(value: &Value) -> &[Value] {
    value.as_array().expect("required JSON array")
}

fn number(value: &Value) -> u64 {
    value.as_u64().expect("required unsigned JSON integer")
}

fn identity(definition: &Value) -> String {
    let hash = &definition["def_path_hash"];
    let mut key = String::new();
    for field in ["stable_crate_id", "local_hash"] {
        let component = hash[field].as_str().expect("hex definition identity");
        assert_eq!(component.len(), 16, "{definition}");
        assert!(component.bytes().all(|byte| byte.is_ascii_hexdigit()), "{definition}");
        key.push_str(component);
    }
    key
}

fn fingerprint(value: &Value) {
    assert_eq!(array(value).len(), 2, "required 128-bit fingerprint");
    for component in array(value) {
        let hash = component.as_str().expect("hex fingerprint component");
        assert_eq!(hash.len(), 16);
        assert!(hash.bytes().all(|byte| byte.is_ascii_hexdigit()));
    }
}

fn source(value: &Value) {
    assert!(value["diagnostic"].as_str().expect("source location").contains("subject.rs"));
    let file_hash = value["file_hash"].as_str().expect("compiler source-file hash");
    let (algorithm, digest) = file_hash.split_once('=').expect("algorithm=hex source hash");
    let expected_length = match algorithm {
        "md5" => 32,
        "sha1" => 40,
        "sha256" | "blake3" => 64,
        algorithm => panic!("unknown compiler source-file hash algorithm: {algorithm}"),
    };
    assert_eq!(digest.len(), expected_length);
    assert!(digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
    let digest = value["snippet_digest"]
        .as_str()
        .expect("source snippet digest")
        .strip_prefix("sha256:")
        .expect("explicit source-snippet digest algorithm");
    assert_eq!(digest.len(), 64);
    assert!(digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
    assert_eq!(value["snippet_digest_domain"], "trust.thir.source-static-readback.source.v1");
}

fn unique<'a>(rows: &'a [Value], name: &str, field: &str) -> &'a Value {
    let found: Vec<_> = rows.iter().filter(|row| row[field]["def_path"] == name).collect();
    assert_eq!(found.len(), 1, "expected one {field} row for {name}: {found:?}");
    found[0]
}

fn body_row<'a>(coverage: &'a Value, name: &str) -> &'a Value {
    let found: Vec<_> = array(&coverage["bodies"])
        .iter()
        .filter(|row| row["def_path"] == name)
        .collect();
    assert_eq!(found.len(), 1, "expected one emitted coverage row for {name}: {found:?}");
    found[0]
}

fn node<'a>(capture: &'a Value, allocation: &Value) -> &'a Value {
    assert!(number(allocation) <= u64::from(u32::MAX), "allocation id is not u32");
    let found: Vec<_> = array(&capture["nodes"])
        .iter()
        .filter(|row| &row["allocation_id"] == allocation)
        .collect();
    assert_eq!(found.len(), 1, "allocation must address exactly one captured node: {allocation}");
    found[0]
}

fn static_node<'a>(capture: &'a Value, name: &str) -> &'a Value {
    let root = unique(array(&capture["statics"]), name, "definition");
    fingerprint(&root["type_fingerprint"]);
    assert!(!root["type_debug"].as_str().expect("compiler static type").is_empty());
    let result = node(capture, &root["allocation_id"]);
    assert_eq!(result["kind"], "static");
    assert_eq!(result["definition"], root["definition"]);
    identity(&result["definition"]);
    result
}

fn source_body<'a>(coverage: &'a Value, name: &str, expected_statics: &[&str]) -> &'a Value {
    let capture = &coverage["source_static_readback"];
    let body = unique(array(&capture["bodies"]), name, "owner");
    assert_eq!(body["def_index"], body_row(coverage, name)["def_index"]);
    identity(&body["owner"]);
    source(&body["source"]);
    let mut names = Vec::new();
    let mut expression_ids = BTreeSet::new();
    for usage in array(&body["uses"]) {
        assert!(expression_ids.insert(number(&usage["expr_index"])), "duplicate source use: {body}");
        let definition = &usage["static_definition"];
        identity(definition);
        let name = definition["def_path"].as_str().expect("static source path");
        names.push(name);
        assert_eq!(definition, &static_node(&body["graph"], name)["definition"]);
        source(&usage["source"]);
        assert_eq!(usage["source"]["file_hash"], body["source"]["file_hash"]);
    }
    names.sort();
    let mut expected = expected_statics.to_vec();
    expected.sort();
    assert_eq!(names, expected, "source uses must reflect actual branch/address expressions");
    body
}

fn validate_image<'a>(readback: &Value, graph: &'a Value, image: &'a Value, size: usize, alignment: usize) -> &'a [Value] {
    assert_eq!(number(&image["layout"]["size_bytes"]), size as u64);
    assert_eq!(number(&image["layout"]["align_bytes"]), alignment as u64);
    assert!(image["mutable"].is_boolean(), "allocation mutability must be disclosed");
    let bytes = array(&image["bytes"]);
    assert_eq!(bytes.len(), size, "initializer bytes must retain the complete allocation extent");
    for byte in bytes {
        assert!(byte.is_null() || number(byte) <= u64::from(u8::MAX), "not nullable u8: {byte}");
    }
    let pointer_bytes = number(&readback["target"]["pointer_size_bytes"]) as usize;
    let mut occupied = BTreeSet::new();
    for relocation in array(&image["relocations"]) {
        let offset = number(&relocation["offset_bytes"]) as usize;
        let end = offset.checked_add(pointer_bytes).expect("bounded pointer range");
        assert!(end <= bytes.len(), "pointer relocation is out of allocation bounds: {relocation}");
        for index in offset..end {
            assert!(occupied.insert(index), "overlapping relocation ranges: {image}");
            assert!(!bytes[index].is_null(), "pointer bytes are uninitialized: {image}");
        }
        let pointer = &relocation["pointer"];
        assert!(pointer["immutable"].is_boolean());
        assert!(pointer["shared_ref"].is_boolean());
        node(graph, &pointer["allocation_id"]);
        number(&pointer["offset_bytes"]);
    }
    bytes
}

fn cold_lazy_image<'a>(readback: &Value, graph: &'a Value, name: &str) -> (&'a Value, &'a Value) {
    let allocation = static_node(graph, name);
    assert_eq!(allocation["declared_mutable"], false);
    assert_eq!(allocation["freeze"], false, "LazyLock's UnsafeCell is not a frozen value");
    assert_eq!(allocation["thread_local"], false);
    assert_eq!(allocation["foreign"], false);
    let image = &allocation["initializer"];
    let bytes = validate_image(
        readback,
        graph,
        image,
        size_of::<LazyLock<layout::TypeName>>(),
        align_of::<LazyLock<layout::TypeName>>(),
    );
    let relocations = array(&image["relocations"]);
    assert_eq!(relocations.len(), 1, "cold LazyLock must retain its real initializer fn pointer");
    let relocation = &relocations[0];
    let function_offset = number(&relocation["offset_bytes"]) as usize;
    let pointer_bytes = size_of::<fn() -> layout::TypeName>();
    assert_eq!(number(&relocation["pointer"]["offset_bytes"]), 0);
    let function = node(graph, &relocation["pointer"]["allocation_id"]);
    assert_eq!(function["kind"], "function");
    identity(&function["definition"]);
    fingerprint(&function["instance_fingerprint"]);
    assert!(!function["instance_debug"].as_str().expect("compiler Instance diagnostic").is_empty());
    let callee = &function["callee_identity"];
    assert_eq!(callee["stable_crate_id"], function["definition"]["def_path_hash"]["stable_crate_id"]);
    assert!(number(&callee["def_index"]) <= u64::from(u32::MAX));
    fingerprint(&callee["substs_digest"]);

    // This is a cold union: only F is initialized, not the larger TypeName.
    // Check the mask independently of the diagnostic's header totals.
    let initialized: Vec<_> = bytes.iter().enumerate().filter(|(_, byte)| !byte.is_null()).collect();
    assert_eq!(initialized.len(), pointer_bytes + size_of::<Once>());
    assert!(bytes.iter().any(Value::is_null), "cold union's uninitialized tail was fabricated");
    let state: Vec<_> = initialized
        .iter()
        .filter(|(offset, _)| !(function_offset..function_offset + pointer_bytes).contains(offset))
        .collect();
    let state_bytes: Vec<u8> = state.iter().map(|(_, byte)| number(byte) as u8).collect();
    assert_eq!(state_bytes.len(), size_of::<Once>());
    assert_eq!(function_offset % align_of::<fn() -> layout::TypeName>(), 0);
    let state_start = state[0].0;
    assert_eq!(state_start % align_of::<Once>(), 0);
    for (ordinal, (offset, _)) in state.iter().enumerate() {
        assert_eq!(*offset, state_start + ordinal, "Once state must occupy one exact initialized interval");
    }
    let mut expected_state = vec![0; size_of::<Once>()];
    let state_index = if readback["target"]["little_endian"] == true { 0 } else { expected_state.len() - 1 };
    expected_state[state_index] = 3; // Darwin queue Once::new(): INCOMPLETE, never COMPLETE.
    assert_eq!(state_bytes, expected_state, "cold initializer must not claim a forced LazyLock");
    (image, function)
}

fn lazy_image<'a>(readback: &Value, graph: &'a Value, name: &str, expected_function: &str) -> &'a Value {
    let (image, function) = cold_lazy_image(readback, graph, name);
    assert_eq!(function["definition"]["def_path"], expected_function);
    assert!(function["instance_debug"].as_str().is_some_and(|text| text.contains(expected_function)));
    image
}

fn closure_images(coverage: &Value) {
    let readback = &coverage["source_static_readback"];
    let helper = source_body(coverage, "infer_closure_literal_type", &CLOSURE_STATIC_NAMES);
    let graph = &helper["graph"];
    assert_eq!(graph["capture_status"], "complete");
    assert_eq!(array(&graph["statics"]).len(), 2);
    assert_eq!(array(&graph["nodes"]).len(), 4, "two closure statics plus two distinct initializer Instances");
    let nat_static = static_node(graph, "CLOSURE_NAT");
    let string_static = static_node(graph, "CLOSURE_STRING");
    assert_ne!(nat_static["allocation_id"], string_static["allocation_id"]);
    assert_ne!(identity(&nat_static["definition"]), identity(&string_static["definition"]));
    let (nat_image, nat_function) = cold_lazy_image(readback, graph, "CLOSURE_NAT");
    let (string_image, string_function) = cold_lazy_image(readback, graph, "CLOSURE_STRING");
    assert_eq!(nat_image["bytes"], string_image["bytes"], "cold closure storage is not a ready TypeName");
    assert_ne!(nat_image["relocations"], string_image["relocations"]);
    assert_ne!(nat_function["allocation_id"], string_function["allocation_id"]);

    // instance.rs::fn_once_adapter_instance uses the SAME call_once DefId for
    // distinct closures. The compiler Instance/args, not its display path or
    // equal cold bytes, retain the initializer identity.
    assert_eq!(nat_function["definition"]["def_path"], FN_ONCE_CALL_ONCE);
    assert_eq!(string_function["definition"]["def_path"], FN_ONCE_CALL_ONCE);
    assert_eq!(nat_function["definition"], string_function["definition"]);
    assert_eq!(nat_function["callee_identity"]["stable_crate_id"], string_function["callee_identity"]["stable_crate_id"]);
    assert_eq!(nat_function["callee_identity"]["def_index"], string_function["callee_identity"]["def_index"]);
    assert_ne!(nat_function["instance_fingerprint"], string_function["instance_fingerprint"]);
    assert_ne!(nat_function["callee_identity"]["substs_digest"], string_function["callee_identity"]["substs_digest"]);
    assert_eq!(array(&graph["nodes"]).iter().filter(|node| node["kind"] == "function").count(), 2);

    let mut closure_owner_ids = BTreeSet::new();
    let mut closure_owner_definitions = BTreeSet::new();
    for name in ["CLOSURE_NAT::{closure#0}", "CLOSURE_STRING::{closure#0}"] {
        let emitted = body_row(coverage, name);
        assert_eq!(emitted["kind"], "fn", "closure body belongs to the producer's fn owner category");
        let captured = unique(array(&readback["bodies"]), name, "owner");
        assert_eq!(captured["def_index"], emitted["def_index"]);
        assert!(closure_owner_ids.insert(number(&captured["def_index"])));
        assert!(closure_owner_definitions.insert(identity(&captured["owner"])));
        assert!(array(&captured["uses"]).is_empty());
        assert!(captured["source"].is_null());
        assert_eq!(captured["graph"]["capture_status"], "complete");
        assert!(array(&captured["graph"]["statics"]).is_empty());
        assert!(array(&captured["graph"]["nodes"]).is_empty());
    }

    // Debug paths sanity-check the diagnostic only. Stable definitions plus
    // distinct full Instance and substitution fingerprints above are the
    // identity assertions; the text does not confer proof authority.
    for (function, static_name) in [(nat_function, "CLOSURE_NAT"), (string_function, "CLOSURE_STRING")] {
        let diagnostic = function["instance_debug"].as_str().expect("closure Instance diagnostic");
        assert!(diagnostic.contains("ClosureOnce"));
        assert!(diagnostic.contains(static_name));
    }
}

fn capture(first_class: bool, large: bool, out: &Path) -> Value {
    rfs::create_dir(out);
    let mut compiler = rustc();
    compiler
        .input("subject.rs")
        .crate_name(CRATE)
        .crate_type("lib")
        .edition("2024")
        .out_dir(out)
        .arg("-Ztrust-verify=off")
        .arg("-Cdebug-assertions=off");
    if first_class {
        compiler.emit("trust-ir");
    } else {
        compiler.emit("metadata").arg("-Ztrust-ir-lower=on");
        compiler.arg(format!("-Ztrust-dump=ir:{}", out.display()));
    }
    if large {
        compiler.arg("--cfg=readback_too_large");
    }
    compiler.run();
    let coverage_name = if first_class {
        format!("{CRATE}.trust-ir.coverage.json")
    } else {
        format!("{CRATE}.coverage.json")
    };
    assert!(!rfs::read(out.join(format!("{CRATE}.trust-ir.bin"))).is_empty());
    let coverage: Value = serde_json::from_str(&rfs::read_to_string(out.join(coverage_name)))
        .expect("actual producer coverage JSON");
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let readback = &coverage["source_static_readback"];
    assert_eq!(readback["schema"], "trust.thir.source-static-readback.v1");
    assert_eq!(readback["storage_phase"], "cold_initializer_only");
    assert_eq!(readback["proof_authority"], false);
    assert_eq!(readback["native_verification_requests"], false);
    assert_eq!(readback["producer"], "thir_static_ref");
    assert_eq!(readback["evaluator_dependency"], "rustc_ctfe");
    assert_eq!(readback["allocation_namespace"], "per_body");
    assert_eq!(readback["inventory_complete"], true);
    assert!(array(&readback["errors"]).is_empty(), "registration defects must not be ignored");
    assert_eq!(readback["limits"]["nodes"], 64);
    assert_eq!(readback["limits"]["bytes"], 65_536);
    assert_eq!(readback["limits"]["relocations"], 1024);
    assert_eq!(number(&readback["target"]["pointer_size_bytes"]), size_of::<usize>() as u64);
    assert!(!readback["target"]["triple"].as_str().expect("target triple").is_empty());
    assert!(!readback["target"]["data_layout"].as_str().expect("target data layout").is_empty());
    assert!(readback["target"]["little_endian"].is_boolean());
    let source_bodies = array(&readback["bodies"]);
    assert_eq!(number(&readback["body_count"]), source_bodies.len() as u64);
    let expected_owners: BTreeSet<_> = array(&coverage["bodies"])
        .iter()
        .map(|body| number(&body["def_index"]))
        .collect();
    let actual_owners: BTreeSet<_> = source_bodies.iter().map(|body| number(&body["def_index"])).collect();
    assert_eq!(actual_owners.len(), source_bodies.len(), "duplicate diagnostic owners");
    assert_eq!(actual_owners, expected_owners, "diagnostic must inventory every actual source owner");
    let mut completed = 0usize;
    let mut refused = 0usize;
    for body in source_bodies {
        identity(&body["owner"]);
        let graph = &body["graph"];
        match graph["capture_status"].as_str().expect("per-owner graph status") {
            "complete" => {
                completed += 1;
                assert!(array(&graph["errors"]).is_empty());
                let node_ids: BTreeSet<_> = array(&graph["nodes"]).iter().map(|item| number(&item["allocation_id"])).collect();
                assert_eq!(node_ids.len(), array(&graph["nodes"]).len(), "duplicate graph nodes");
                if array(&body["uses"]).is_empty() {
                    assert!(body["source"].is_null());
                    assert!(array(&graph["statics"]).is_empty());
                    assert!(array(&graph["nodes"]).is_empty());
                }
            }
            "refused" => {
                refused += 1;
                assert!(!array(&graph["errors"]).is_empty());
                assert!(array(&graph["statics"]).is_empty());
                assert!(array(&graph["nodes"]).is_empty());
            }
            status => panic!("unknown graph status {status}: {body}"),
        }
    }
    assert_eq!(number(&readback["complete_bodies"]), completed as u64);
    assert_eq!(number(&readback["refused_bodies"]), refused as u64);
    assert_eq!(completed + refused, source_bodies.len());
    assert_eq!(readback["capture_status"], if refused == 0 { "complete" } else { "partial" });

    // New readback must leave the executable-source refusal in force.
    for name in ["infer_literal_type", "infer_closure_literal_type"] {
        let helper = body_row(&coverage, name);
        assert_eq!(helper["lowered"], false);
        assert_eq!(helper["spliced"], false);
        assert!(helper["func_id"].is_null());
        assert!(
            array(&helper["unsupported"]).iter().any(|entry| {
                entry[0] == "StaticRef(initializer not scalar)" && number(&entry[1]) > 0
            }),
            "LazyLock's unsupported storage must not become executable merely because bytes were observed: {helper}"
        );
    }
    coverage
}

fn complete(coverage: &Value) {
    let readback = &coverage["source_static_readback"];
    assert_eq!(readback["capture_status"], "complete");
    assert!(array(&readback["errors"]).is_empty());
    assert_eq!(readback["refused_bodies"], 0);
    let helper = source_body(coverage, "infer_literal_type", &["FIRST", "SECOND"]);
    source_body(coverage, "first_address", &["FIRST"]);
    source_body(coverage, "first_address_again", &["FIRST"]);
    source_body(coverage, "equal_initializer_address", &["SAME_AS_FIRST"]);
    let pair = source_body(coverage, "equal_initializer_pair", &["FIRST", "SAME_AS_FIRST"]);
    let self_ref = source_body(coverage, "self_reference_address", &["SELF_REF"]);
    let graph = &helper["graph"];
    let pair_graph = &pair["graph"];
    let cycle_graph = &self_ref["graph"];
    let mut definitions = Vec::new();
    for (graph, names) in [(graph, &["FIRST", "SECOND"][..]), (pair_graph, &["SAME_AS_FIRST"][..]), (cycle_graph, &["SELF_REF"][..])] {
        definitions.extend(names.iter().map(|name| static_node(graph, name)["definition"].clone()));
    }
    let names: BTreeSet<_> = definitions.iter().map(|definition| definition["def_path"].as_str().expect("static path")).collect();
    assert_eq!(names, BTreeSet::from(STATIC_NAMES));
    let identities: BTreeSet<_> = definitions.iter().map(identity).collect();
    assert_eq!(identities.len(), 4, "all four source static identities must remain distinct");
    assert_eq!(array(&graph["statics"]).len(), 2);
    assert_eq!(array(&graph["nodes"]).len(), 4, "two source statics plus their two real fn pointers");
    assert_eq!(array(&pair_graph["statics"]).len(), 2);
    assert_eq!(array(&pair_graph["nodes"]).len(), 3, "two source statics share one actual initializer fn");
    assert_ne!(static_node(pair_graph, "FIRST")["allocation_id"], static_node(pair_graph, "SAME_AS_FIRST")["allocation_id"]);
    assert_ne!(static_node(graph, "FIRST")["allocation_id"], static_node(graph, "SECOND")["allocation_id"]);
    let first = lazy_image(readback, pair_graph, "FIRST", "init_nat");
    let same = lazy_image(readback, pair_graph, "SAME_AS_FIRST", "init_nat");
    let helper_first = lazy_image(readback, graph, "FIRST", "init_nat");
    let second = lazy_image(readback, graph, "SECOND", "init_string");
    assert_eq!(first, same, "equal cold images still retain separate source allocation identities");
    assert_eq!(helper_first["bytes"], second["bytes"]);
    assert_ne!(helper_first["relocations"], second["relocations"], "different initializer functions are not interchangeable");

    let cycle = static_node(cycle_graph, "SELF_REF");
    assert_eq!(array(&cycle_graph["statics"]).len(), 1);
    assert_eq!(array(&cycle_graph["nodes"]).len(), 1, "a self cycle must reuse its reserved identity");
    assert_eq!(cycle["declared_mutable"], false);
    assert_eq!(cycle["freeze"], true);
    let image = &cycle["initializer"];
    let bytes = validate_image(readback, cycle_graph, image, size_of::<layout::SelfRef>(), align_of::<layout::SelfRef>());
    assert!(bytes.iter().all(|byte| !byte.is_null()));
    let relocations = array(&image["relocations"]);
    assert_eq!(relocations.len(), 1);
    assert_eq!(relocations[0]["offset_bytes"], 0);
    assert_eq!(relocations[0]["pointer"]["allocation_id"], cycle["allocation_id"]);
    assert_eq!(relocations[0]["pointer"]["offset_bytes"], 0);
    assert_eq!(relocations[0]["pointer"]["immutable"], true);
    assert_eq!(relocations[0]["pointer"]["shared_ref"], true);
    closure_images(coverage);
}

fn main() {
    // Both maintained publication surfaces must expose the diagnostic.
    complete(&capture(false, false, Path::new("dump")));
    complete(&capture(true, false, Path::new("emit")));

    let bounded = capture(false, true, Path::new("bounded"));
    let readback = &bounded["source_static_readback"];
    assert_eq!(readback["capture_status"], "partial");
    let large = unique(array(&readback["bodies"]), "too_large_address", "owner");
    let graph = &large["graph"];
    assert_eq!(graph["capture_status"], "refused");
    assert!(array(&graph["nodes"]).is_empty(), "never publish a partial owner graph");
    assert!(array(&graph["statics"]).is_empty(), "never retain successful-looking partial roots");
    assert!(array(&graph["errors"]).iter().any(|error| {
        error == "source static readback exceeds budget of 65536 bytes"
    }), "must name the actual exceeded bound: {large}");
    let uses = array(&large["uses"]);
    assert_eq!(uses.len(), 1, "a graph refusal must preserve the actual source fact");
    assert_eq!(uses[0]["static_definition"]["def_path"], "TOO_LARGE");
    identity(&uses[0]["static_definition"]);
    source(&large["source"]);
    source(&uses[0]["source"]);
    assert_eq!(uses[0]["source"]["file_hash"], large["source"]["file_hash"]);
    let helper = source_body(&bounded, "infer_literal_type", &["FIRST", "SECOND"]);
    assert_eq!(helper["graph"]["capture_status"], "complete", "one refused owner cannot poison an unrelated complete closure");
    lazy_image(readback, &helper["graph"], "FIRST", "init_nat");
    lazy_image(readback, &helper["graph"], "SECOND", "init_string");
    closure_images(&bounded);
}

/// Execute the maintained recipe under libtest as well as compiletest.
/// The runner supplies an authenticated compiler and a fresh owned cwd; no
/// compiler or subject policy is changed by this test entry point.
#[test]
fn actual_source_static_readback_finalizer_runs() {
    assert!(cfg!(all(target_vendor = "apple", target_arch = "aarch64")));
    assert_eq!(std::env::var("HOST").as_deref(), Ok("aarch64-apple-darwin"));
    assert_eq!(std::env::var("TARGET").as_deref(), Ok("aarch64-apple-darwin"));
    let compiled_subject = include_bytes!("subject.rs");
    assert_eq!(rfs::read("subject.rs").as_slice(), compiled_subject.as_slice());
    main();
    assert_eq!(rfs::read("subject.rs").as_slice(), compiled_subject.as_slice());
}

//! Exact assembled-body selection across non-injective rustc display paths.
//!
//! Two macro expansions below create distinct nested `same` definitions under
//! one parent. rustc gives them the same `def_path_str`; since WS5.2 crate
//! assembly NAMES each by its link-time symbol (here its `export_name`) and keeps
//! the shared def path as `display_path`, so no collision rename is needed.
//! Each body calls `helper`, so its single-body `trust_ir_of` artifact has only a
//! bodyless local declaration and cannot substitute for the linked crate module.
//! Each colliding definition also has a distinct exported C symbol. Calling
//! those symbols directly makes the separately codegenerated body selection
//! observable; the ordinary `dispatch` call alone would not suffice because
//! the Trust-IR converter recursively inlines its local calls.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use std::collections::BTreeSet;

use run_make_support::{bin_name, rfs, run, rustc, serde_json};

fn main() {
    rfs::write(
        "assembled_identity.rs",
        r#"#![crate_name = "assembled_identity"]

#[inline(never)]
fn helper(x: u64) -> u64 {
    x ^ 0x55
}

macro_rules! colliding_local {
    ($salt:expr, $x:expr, $export:literal) => {{
        #[inline(never)]
        #[unsafe(export_name = $export)]
        extern "C" fn same(x: u64) -> u64 {
            crate::helper(x) ^ $salt
        }
        same($x)
    }};
}

#[inline(never)]
pub fn dispatch(selector: u64, x: u64) -> u64 {
    if selector == 0 {
        colliding_local!(0x11, x, "assembled_same_left")
    } else {
        colliding_local!(0x22, x, "assembled_same_right")
    }
}
"#,
    );
    rfs::create_dir("ir");
    rfs::create_dir("out");

    let compiled = rustc()
        .input("assembled_identity.rs")
        .crate_name("assembled_identity")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .arg("-Ztrust-dump=ir:ir")
        .out_dir("out")
        .run();
    compiled
        .assert_stderr_contains("trust-cg trust-ir frontend: 4/4 reachable function(s) completed");
    let stderr = compiled.stderr_utf8();
    for forbidden in [
        "fell back to the per-instance artifact",
        "refusing display-name selection",
        "assembled Trust-IR handoff has no body",
        "non-local callee",
    ] {
        assert!(!stderr.contains(forbidden), "unexpected `{forbidden}`:\n{stderr}");
    }

    let coverage: serde_json::Value =
        serde_json::from_str(&rfs::read_to_string("ir/assembled_identity.coverage.json"))
            .expect("coverage sidecar must be valid JSON");
    let same_rows: Vec<_> = coverage["bodies"]
        .as_array()
        .expect("body inventory")
        .iter()
        .filter(|row| {
            row["kind"] == "fn"
                && row["def_path"]
                    .as_str()
                    .is_some_and(|path| path.rsplit("::").next() == Some("same"))
        })
        .collect();
    assert_eq!(
        same_rows.len(),
        2,
        "the fixture must really create two same-display-path definitions: {same_rows:?}"
    );
    assert_eq!(same_rows[0]["def_path"], same_rows[1]["def_path"]);
    let mut ids = BTreeSet::new();
    for row in &same_rows {
        assert_eq!(row["lowered"], true, "colliding body was not lowered: {row}");
        assert_eq!(row["spliced"], true, "colliding body was not spliced: {row}");
        assert_eq!(
            row["calls"]["resolved"], 1,
            "the per-body fallback poison (the helper call) disappeared: {row}"
        );
        ids.insert(row["func_id"].as_u64().expect("spliced body FuncId"));
    }
    assert_eq!(ids.len(), 2, "distinct definitions must map to distinct FuncIds");

    let text = rfs::read_to_string("ir/assembled_identity.trust-ir.txt");
    // WS5.2: each colliding definition is NAMED by its link-time symbol — its
    // `export_name`, exactly what `nm` shows for the native object — and both
    // carry the ONE shared def path as display path (display paths are not
    // identity). The retired `!trust_definition::…` collision name is gone.
    // The shared def path is the coverage rows' own `def_path` (rustc's
    // `def_path_str`, which spells a local item without the crate name).
    let shared = same_rows[0]["def_path"].as_str().expect("the rows' shared def path");
    for symbol in ["assembled_same_left", "assembled_same_right"] {
        let header = format!("fn @{symbol}(");
        assert_eq!(text.matches(&header).count(), 1, "{symbol} must name exactly one row:\n{text}");
        let body = text.split_once(&header).unwrap().1.split_once("\n}\n").unwrap().0;
        assert!(
            body.contains(&format!("; #display-path: {shared:?}")),
            "{symbol} must display the shared def path `{shared}`:\n{body}"
        );
    }
    assert!(!text.contains("!trust_definition::"), "the collision rename is retired:\n{text}");

    rfs::write(
        "driver.rs",
        r#"extern crate assembled_identity;

unsafe extern "C" {
    fn assembled_same_left(x: u64) -> u64;
    fn assembled_same_right(x: u64) -> u64;
}

fn main() {
    let values = unsafe {
        (
            assembled_same_left(0x123),
            assembled_same_right(0x123),
        )
    };
    println!("{} {} {} {}", values.0, values.1,
        assembled_identity::dispatch(0, 0x123),
        assembled_identity::dispatch(1, 0x123));
}
"#,
    );
    rustc()
        .input("driver.rs")
        .edition("2024")
        .arg("-Cpanic=abort")
        // Trust: `driver` is the OBSERVER, not the subject — this test asserts the
        // codegen backend's exact body SELECTION through the printed results, never
        // a verdict about `driver` itself, so it is built verify-off like the
        // sibling observers. Measured 2026-09-13 on the 7ef82153b7 driver: under the
        // default strict policy `driver::main` fails closed HONESTLY — two
        // `hardened_ffi_boundary` unknowns for the unmodeled extern-C calls, and the
        // `println!` std path refused by name ("native TrustIr bundle … refused
        // Assert-bearing member `std::sync::reentrant_lock::ReentrantLock<…>`") — and
        // its native bundle VALIDATES. An earlier driver (d8997ace61-era) emitted an
        // INVALID native bundle for this `main` (use-before-def in an orphaned block,
        // `insert_field` index out of range, a bitcast without layout evidence); that
        // was the BRIDGE's bundle, not the direct producer's module, and d2769909e7
        // fixed both root causes in `crates/trust-ir-bridge/src/lower.rs`.
        .arg("-Ztrust-verify=off")
        .extern_("assembled_identity", "out/libassembled_identity.rlib")
        .library_search_path("out")
        .output(bin_name("driver"))
        .run();
    let ran = run("driver");
    assert_eq!(
        ran.stdout_utf8().trim(),
        format!(
            "{} {} {} {}",
            0x123_u64 ^ 0x55 ^ 0x11,
            0x123_u64 ^ 0x55 ^ 0x22,
            0x123_u64 ^ 0x55 ^ 0x11,
            0x123_u64 ^ 0x55 ^ 0x22,
        ),
        "exact assembled identities were swapped or collapsed"
    );
}

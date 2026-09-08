//! Exact assembled-body selection across non-injective rustc display paths.
//!
//! Two macro expansions below create distinct nested `same` definitions under
//! one parent. rustc gives them the same `def_path_str`; crate assembly therefore
//! gives both a `!trust_definition::...::<DefinitionIdentity>` operational name.
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
    let renamed: Vec<_> = text
        .lines()
        .filter(|line| {
            line.contains("fn @!trust_definition::") && line.contains("::dispatch::same::")
        })
        .collect();
    assert_eq!(
        renamed.len(),
        2,
        "both non-injective display paths must be collision-renamed:\n{text}"
    );

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

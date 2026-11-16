//! The crate assembler's per-body storage-value-traffic refusal (STORAGE-VALUE-TRAFFIC-1,
//! `BodyRecord::storage_value_traffic`), end to end over the shapes that carry storage by value.
//!
//! Since `060a4cd7ff` the producer spells `MaybeUninit<T>` and non-Drop unions as addressable
//! storage (`Ty::Storage`), and the trust-ir validator refuses any module that carries such
//! storage BY VALUE. Without a per-body refusal one such body failed the WHOLE crate module's
//! validation, so nothing of the crate was published. Pinned here, over the real producer:
//!   * the crate module validates and the coverage artifact is published;
//!   * every body that carries `W`/`MaybeUninit` by value — in its own signature, a block
//!     parameter, a typed instruction, or a declaration its callee ledger would mint — and lowered
//!     is left out BY NAME, `Splice(storage value traffic)`;
//!   * `mk` (a withheld-layout row by value, which R2 refuses without the flag) and `new_uninit`
//!     (a bare storage return, which the signature-type check refuses without it) are named by
//!     the flag, which `splice_refusal` checks before both;
//!   * the by-reference controls and the `const` thread-local's value bodies splice, and `W` keeps
//!     its storage field and full layout;
//!   * every lowered body the module leaves out names its refusal, and no other row names one.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

const TRAFFIC: &str = "Splice(storage value traffic)";

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    let out = cmd(rustc_path())
        .args([
            "own.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=own",
            "-Copt-level=3",
            "-Ccodegen-units=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:own-ir",
            "--out-dir",
            "out",
        ])
        .run();
    let stderr = out.stderr_utf8();
    for line in stderr.lines() {
        assert!(
            !line.contains("final Trust-IR module validation failed")
                && !line.contains("semantic finalization failed"),
            "the crate module must validate:\n{line}"
        );
    }

    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("own-ir/own.coverage.json"))
            .expect("published coverage must be valid JSON");
    let rows = report["bodies"].as_array().expect("complete body inventory");
    let row = |path: &str| {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == path).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate row {path}: {rows:?}");
        matching[0]
    };

    // Own signature / block parameter (`get`, `pass`), a by-value argument to a local callee
    // (`forwards`), typed instruction roots (`copy_out`, `opt`, `tag`), storage-typed call results
    // (`binds`, `std_caller`), the static initializer (`ONCE`) and the lazy thread-local's value
    // bodies; `mk` and `new_uninit` are pre-emption cases (R2 and the signature-type check would
    // name them without the flag).
    let lazy_vals: Vec<String> = rows
        .iter()
        .filter_map(|r| r["def_path"].as_str())
        .filter(|p| p.starts_with("LAZY::") && p.ends_with("::__RUST_STD_INTERNAL_VAL"))
        .map(str::to_string)
        .collect();
    assert_eq!(lazy_vals.len(), 2, "the lazy thread-local's value bodies: {lazy_vals:?}");
    let mut refused: Vec<&str> = vec![
        "get", "pass", "forwards", "copy_out", "opt", "tag", "binds", "std_caller", "mk",
        "new_uninit", "ONCE",
    ];
    refused.extend(lazy_vals.iter().map(String::as_str));
    for path in refused {
        let body = row(path);
        assert_eq!(body["lowered"], true, "{path} must lower for the splice to judge it: {body}");
        assert_eq!(body["spliced"], false, "{path} carries storage by value: {body}");
        assert_eq!(body["splice_refusal"], TRAFFIC, "{path}: {body}");
        assert!(body["func_id"].is_null(), "{body}");
    }
    let mut controls = vec!["ctl", "ctl_caller"];
    let const_vals: Vec<String> = rows
        .iter()
        .filter_map(|r| r["def_path"].as_str())
        .filter(|p| p.starts_with("CONSTED::") && p.ends_with("::__RUST_STD_INTERNAL_VAL"))
        .map(str::to_string)
        .collect();
    assert_eq!(const_vals.len(), 2, "the const thread-local's value bodies: {const_vals:?}");
    controls.extend(const_vals.iter().map(String::as_str));
    for path in controls {
        let body = row(path);
        assert_eq!(body["spliced"], true, "the control splices: {body}");
        assert!(body["splice_refusal"].is_null(), "{body}");
    }

    for r in rows {
        let dropped = r["lowered"] == true && r["spliced"] == false;
        let named = r["splice_refusal"].as_str().is_some_and(|m| m.starts_with("Splice("));
        assert_eq!(dropped, named, "every drop is named and nothing else is: {r}");
    }

    let text = trust_ir::by_display_path(&rfs::read_to_string("own-ir/own.trust-ir.txt"));
    let w = text
        .lines()
        .find(|l| l.starts_with("struct @W ") || l.starts_with("struct @\"W\" "))
        .unwrap_or_else(|| panic!("the controls' `W` row is in the module:\n{text}"));
    assert!(w.contains("storage<8, 8>"), "W keeps its storage field as geometry: {w}");
    assert!(w.contains("size=16"), "W keeps its full layout: {w}");
    for (path, defined) in [("get", false), ("pass", false), ("mk", false), ("ctl", true)] {
        // A bare identifier is spelled unquoted (`trust_ir::by_display_path`).
        let header = format!("fn @{path}(");
        assert_eq!(text.matches(&header).count(), usize::from(defined), "{path}");
    }
}

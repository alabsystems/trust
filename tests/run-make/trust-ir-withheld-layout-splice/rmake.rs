//! A thread-local whose cell holds a DECLINED `Option` — a tuple payload (`(u64, u64)`) or a fn
//! pointer payload — lowers `Option` to its `Ty::Bool` flag lane, and the producer WITHHOLDS the
//! layout of every struct row over that flag (`UnsafeCell<Option<..>>` is `repr(transparent)`, so
//! its 1-byte model cannot carry rustc's bytes; `RefCell`/`Cell` over it names an unsized row).
//! The generated `__rust_std_internal_init_fn` returns that cell by value. R2, the crate
//! assembler's identity-spelling refusal, read every layout-less signature row as an identity
//! spelling, so the init body was dropped from the crate module with nothing in the artifact
//! saying so (measured 2026-09-27 on origin/main `5ab8dcccfc`: `lowered: true, spliced: false`).
//!
//! Pinned here, over the real producer (ratification review 2026-09-28, which withdrew the
//! 2026-09-27 exemption that spliced these bodies on the producer's withheld-layout ledger):
//!   * the init bodies of `PAIR` and `HOOK` are REFUSED by R2 and say so by name — their signature
//!     returns a cell row whose layout the producer withheld (a 1-byte model of rustc's bytes),
//!     which the assembled module cannot carry as a callable definition, witnessed or not;
//!     `PLAIN`, a first-class `Option`, is the control that splices;
//!   * every lowered body the module leaves out NAMES its refusal (`splice_refusal`), and no
//!     other row names one. The value bodies (`__RUST_STD_INTERNAL_VAL`) are one such: their
//!     `LazyStorage` carries `MaybeUninit`, which 060a4cd7ff spells as no-value `Storage`
//!     geometry instead of a union placeholder lane. Returning it by value is storage value
//!     traffic, a separate, deliberate refusal — pinned by name so the day it closes this test
//!     says so. It must stay a per-body refusal: left to final validation it failed the whole
//!     crate module (`InvalidStorageUse`), so no coverage artifact was written at all.

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    cmd(rustc_path())
        .args([
            "cells.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=cells",
            "-Copt-level=3",
            "-Ccodegen-units=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:cells-ir",
            "--out-dir",
            "out",
        ])
        .run();

    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("cells-ir/cells.coverage.json"))
            .expect("published coverage must be valid JSON");
    assert_eq!(report["schema"], "trust.thir-lower.crate-module.coverage.v2");
    let rows = report["bodies"].as_array().expect("complete body inventory");
    let row = |path: &str| {
        let matching: Vec<_> = rows.iter().filter(|r| r["def_path"] == path).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate row {path}");
        matching[0]
    };

    for key in ["PAIR", "HOOK", "PLAIN"] {
        let init = row(&format!("{key}::__rust_std_internal_init_fn"));
        assert_eq!(init["lowered"], true, "{init}");
        if key == "PLAIN" {
            assert_eq!(init["spliced"], true, "the control init body is in the module: {init}");
            assert!(init["splice_refusal"].is_null(), "{init}");
            assert!(init["func_id"].is_u64(), "{init}");
        } else {
            assert_eq!(init["spliced"], false, "a withheld-layout signature must not splice: {init}");
            assert_eq!(
                init["splice_refusal"], "Splice(signature reaches a layout-less struct)",
                "{init}"
            );
            assert!(init["func_id"].is_null(), "{init}");
        }

        let value = row(&format!("{key}::{{constant#0}}::{{closure#0}}::__RUST_STD_INTERNAL_VAL"));
        assert_eq!(value["lowered"], true, "{value}");
        assert_eq!(value["spliced"], false, "{value}");
        // Trust: 060a4cd7ff respelled `MaybeUninit` as `Ty::Storage`; the body is refused by
        // the per-body storage-value gate, not by the union placeholder lane.
        assert_eq!(value["splice_refusal"], "Splice(storage value traffic)", "{value}");
    }

    // The invariant the artifact now carries: a lowered body the module leaves out names why,
    // and no other row names anything.
    for r in rows {
        let dropped = r["lowered"] == true && r["spliced"] == false;
        let named = r["splice_refusal"].as_str().is_some_and(|m| m.starts_with("Splice("));
        assert_eq!(dropped, named, "every drop is named and nothing else is: {r}");
        assert!(named || r["splice_refusal"].is_null(), "{r}");
    }

    // The module carries the control's definition and neither refused one.
    // Headers by def path (WS5.2 names them by link symbol; `trust_ir::by_display_path`).
    let text = trust_ir::by_display_path(&rfs::read_to_string("cells-ir/cells.trust-ir.txt"));
    for (key, defined) in [("PAIR", false), ("HOOK", false), ("PLAIN", true)] {
        let header = format!("fn @\"{key}::__rust_std_internal_init_fn\"(");
        assert_eq!(text.matches(&header).count(), usize::from(defined), "{key}: init function");
    }
    // Where the producer's cell rows reach the module at all, they still carry no layout claim.
    for cell in [
        "std::cell::RefCell<std::option::Option<(u64, u64)>>",
        "std::cell::Cell<std::option::Option<fn(u32) -> u32>>",
    ] {
        if let Some(line) = text.lines().find(|l| l.starts_with(&format!("struct @\"{cell}\" "))) {
            assert!(!line.contains(" size="), "the layout stays withheld: {line}");
        }
    }
}

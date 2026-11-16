//! Trust (2026-10-02, KNOWN_HAZARDS "a field store through a `DerefMut` chain runs the
//! `deref_mut` call BEFORE the right-hand side", CLOSED): the direct producer lowers an
//! assignment's right-hand side BEFORE the place's pointer, Rust's order.
//!
//! `o.n = c(fd)` evaluates `c(fd)` (here `close(fd)`) first, then the place
//! (`<Outer as DerefMut>::deref_mut`, here `close(-1)`). The producer used to lower the
//! place's pointer first and splice `set_n` tag-free as `call deref_mut; call c; ...`.
//! This pins the order in the dumped trust-ir: in `set_n`, the call to `c` comes before
//! the call to `deref_mut`, and the body still lowers and splices.

//@ ignore-cross-compile

use run_make_support::{rfs, rustc, serde_json, trust_ir};

fn main() {
    rustc()
        .input("dm.rs")
        .crate_name("dm")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:ir")
        .emit("metadata")
        .run();
    let coverage: serde_json::Value =
        serde_json::from_str(&rfs::read_to_string("ir/dm.coverage.json")).expect("coverage json");
    let set_n = coverage["bodies"]
        .as_array()
        .expect("bodies")
        .iter()
        .find(|b| b["def_path"] == "set_n")
        .expect("coverage row for set_n")
        .clone();
    assert_eq!(set_n["lowered"], true, "set_n must lower: {set_n}");
    assert_eq!(set_n["spliced"], true, "set_n must splice: {set_n}");

    // Headers by def path (WS5.2 names them by link symbol; `trust_ir::by_display_path`).
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/dm.trust-ir.txt"));
    // The callee FuncIds, by their definition headers' order in the module.
    let func_id = |name: &str| {
        text.lines()
            .filter(|line| line.contains("fn @"))
            .position(|line| line.contains(name))
            .unwrap_or_else(|| panic!("no definition for {name}:\n{text}"))
    };
    let deref_mut = format!("call @func.{}(", func_id("as std::ops::DerefMut>::deref_mut"));
    let c = format!("call @func.{}(", func_id("fn @c("));
    let body: String = text
        .lines()
        .skip_while(|line| !line.contains("fn @set_n("))
        .take_while(|line| *line != "}")
        .collect::<Vec<_>>()
        .join("\n");
    let at = |needle: &str| {
        body.find(needle).unwrap_or_else(|| panic!("set_n has no `{needle}`:\n{body}"))
    };
    assert!(
        at(&c) < at(&deref_mut),
        "the right-hand side's call must precede the place's deref_mut:\n{body}"
    );
}

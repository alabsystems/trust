//! Trust (2026-09-12, IR-5): a CRATE-ROOT Clean island must emit a Module that
//! passes the producer boundary.
//!
//! Measured on the sealed pack toolchain `trust/8590` (rev `f558ea288`,
//! 2026-09-12 — no part of this fix), on exactly `top_level.rs` below:
//!
//! ```text
//! error: trust-ir-lower semantic finalization failed: final Trust-IR module
//!        validation failed [DuplicateFunctionName]: name="ctrl_min"
//!        ids=[FuncId(1), FuncId(2)]
//! ```
//!
//! exit 1 — while the identical crate with the island wrapped in `mod m`
//! compiled and linked. The cause is not the island: assemble pass 2 names the
//! `local-unlowered` declaration by the def's canonical `def_path` and the Clean
//! emitter names the appended definition by `plan.name()`, and at the crate root
//! those are the same string. `Module::function_by_name` and codegen's
//! known-fn-pointer resolution are first-match, so the producer boundary
//! (`crate_module::final_module_validation_errors`) refuses the whole module.
//!
//! The first fix (2026-09-12) renamed the orphan declaration
//! `ctrl_min::<shadowed-by-clean-origin:FuncId(N)>` — a name that is no link-time
//! symbol at all. WS5.2 (F-087/F-092) removes the orphan instead: every row is
//! NAMED by its link-time symbol, the Rust declaration of `ctrl_min` and its
//! Clean definition therefore carry ONE symbol, and the definition takes the
//! declaration's row. There is nothing left to retire.
//!
//! Pins:
//!  * the crate compiles and emits (the refusal above is gone);
//!  * the link row links the one edge IN PLACE (`decl_func_id == target_func_id`),
//!    refuses nothing, and retires nothing (`retired_declaration: null`);
//!  * exactly one row displays `ctrl_min`, it is the Clean definition, it is
//!    named by the Rust item's v0 symbol, and no `<shadowed-by-…>` name exists;
//!  * CONTROL: the same crate under `-Ztrust-verify=off` records no Clean-origin
//!    rows at all.
//!
//! The one-row rule's refusal half (a refused edge can no longer stay on a
//! separately named declaration, so it refuses the batch) and the pre-placement
//! `DuplicateFunctionName` control are unit-pinned in
//! `crates/trust-thir-lower/src/clean_origin_join.rs`
//! (`an_arity_refused_edge_refuses_the_batch_because_no_declaration_can_stay`,
//! `without_the_ledger_one_symbol_would_name_two_rows_and_is_refused`).

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn main() {
    let on_dir = Path::new("emit-on");
    rfs::create_dir(&on_dir);
    rustc()
        .input("top_level.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&on_dir)
        .arg("-Ztrust-verify=on")
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override. A run-make recipe is a new policy boundary.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();

    let coverage = rfs::read_to_string(on_dir.join("top_level.trust-ir.coverage.json"));
    let coverage_json: serde_json::Value =
        serde_json::from_str(&coverage).expect("coverage sidecar must be valid JSON");
    let link = coverage_json["clean_origin"]["linked"]
        .as_array()
        .expect("clean_origin.linked array")
        .iter()
        .find(|row| row["def_path"] == "ctrl_min")
        .cloned()
        .expect("the crate-root ctrl_min link row");
    assert_eq!(link["edges_repointed"], 1, "{link}");
    assert_eq!(
        link["refusals"].as_array().map(Vec::len),
        Some(0),
        "the one-row link must refuse nothing: {link}"
    );
    assert_eq!(link["decl_func_id"], link["target_func_id"], "one symbol, one row: {link}");
    assert!(link["retired_declaration"].is_null(), "nothing is retired any more: {link}");

    let text = rfs::read_to_string(on_dir.join("top_level.trust-ir.txt"));
    let directive = "; #display-path: \"ctrl_min\"\n";
    assert_eq!(text.matches(directive).count(), 1, "exactly one `ctrl_min` row:\n{text}");
    let header = text[..text.find(directive).unwrap()]
        .lines()
        .rev()
        .find(|line| line.contains("fn @"))
        .expect("the ctrl_min row's header");
    assert!(
        header.trim_start().starts_with("rustcc fn @_R") && header.contains("8ctrl_min"),
        "the Clean definition must be named by `ctrl_min`'s v0 link-time symbol: {header}"
    );
    assert!(!text.contains("<shadowed-by-"), "no synthetic symbol is minted:\n{text}");
    assert!(text.contains("ctrl"), "the Rust caller's row is missing from the one Module:\n{text}");

    // ── CONTROL: verification off records nothing to retire ──────────────────
    let off_dir = Path::new("emit-off");
    rfs::create_dir(&off_dir);
    rustc()
        .input("top_level.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&off_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let coverage_off = rfs::read_to_string(off_dir.join("top_level.trust-ir.coverage.json"));
    assert!(
        coverage_off.contains("\"recorded\": false"),
        "verification-off must disclose the absent recording:\n{coverage_off}"
    );
    assert!(
        !coverage_off.contains("retired_declaration"),
        "verification-off retires nothing — there is no appended definition:\n{coverage_off}"
    );
}

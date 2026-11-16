//! Trust (WS5.5, STAGED): the zero-authority contract-carry shadow, measured on
//! the REAL producer for the two-language fixtures p01 (`requires` /
//! `ensures` / `decreases`) and p02 (a `while` loop's `invariant` and
//! `decreases`), plus the original width-conversion `shift_mask` body.
//!
//! Behind `TRUST_CONTRACT_CARRY_SHADOW=<dir>` the finalizer seam installs the
//! staged contract carry on a CLONE of the published module and writes
//! `<crate>.contract-carry.shadow.json`. This test pins, per fixture:
//!
//! * the carry: typed summaries with `Param` / `ResultSlot` / header-`Value`
//!   bindings at `BitVec(64)`, and one `Pending` contract-kind row per
//!   authored clause, loop rows sited at their header;
//! * the clone validates under `validate_module`,
//!   `validate_module_with_authority` and `validate_linked_module`, the
//!   staged contract-bound rung admits it, and the LIVE tier
//!   (`obligation-bearing-pending-v2`) REFUSES it — zero rows born live;
//! * the reference interpreter runs `program` to the fixture's native value;
//! * the published `.trust-ir.bin` is BYTE-IDENTICAL with and without the
//!   env var: the shadow changes no artifact.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use run_make_support::serde_json::Value;
use run_make_support::{rfs, rustc, serde_json, source_root};

const SHADOW_ENV: &str = "TRUST_CONTRACT_CARRY_SHADOW";

fn fixture(row: &str, file: &str) -> PathBuf {
    source_root().join("tests/two-language-programs").join(row).join(file)
}

/// Compile `source` as a library to `--emit=trust-ir`, with the shadow on
/// (`Some(dir)`) or off. Returns the artifact directory.
fn emit(source: &Path, crate_name: &str, tag: &str, shadow: Option<&Path>) -> PathBuf {
    let out = PathBuf::from(format!("{crate_name}-{tag}"));
    rfs::create_dir(&out);
    let mut cmd = rustc();
    cmd.input(source)
        .crate_name(crate_name)
        .crate_type("lib")
        .cfg("parta_lib")
        .emit("trust-ir")
        .out_dir(&out)
        .arg("-Ztrust-verify=off");
    match shadow {
        Some(dir) => {
            cmd.env(SHADOW_ENV, dir);
        }
        None => {
            cmd.env_remove(SHADOW_ENV);
        }
    }
    cmd.run();
    out
}

fn shadow_json(dir: &Path, crate_name: &str) -> Value {
    let path = dir.join(format!("{crate_name}.contract-carry.shadow.json"));
    let text = rfs::read_to_string(&path);
    serde_json::from_str(&text)
        .unwrap_or_else(|error| panic!("{} is not JSON ({error}):\n{text}", path.display()))
}

fn strings(value: &Value) -> Vec<String> {
    value.as_array().expect("an array").iter().map(|v| v.to_string()).collect()
}

/// The staged clone judgements shared by every fixture.
fn assert_clone_judged(json: &Value, crate_name: &str) {
    let dump = || serde_json::to_string_pretty(json).unwrap();
    assert_eq!(json["schema"], "trust.contract-carry.shadow/v1", "{}", dump());
    assert_eq!(json["crate"], crate_name);
    assert_eq!(json["published"], true, "{}", dump());
    assert_eq!(json["staged_marker"], "contract-bound-v3");
    assert_eq!(
        json["live_marker"], "obligation-bearing-pending-v2",
        "the capability flip is the owner's signed act (DG-60)"
    );
    for key in [
        "install_errors",
        "validate_module",
        "validate_module_with_authority",
        "validate_linked_module",
        "staged_rung_errors",
        "text_losses",
    ] {
        assert!(strings(&json[key]).is_empty(), "{key} must be empty: {}", dump());
    }
    assert_eq!(json["live_tier_refuses"], true, "ZERO rows born live: {}", dump());
    assert_eq!(json["binary_round_trip"], true, "{}", dump());
    for resolution in json["resolution"].as_array().unwrap() {
        assert!(resolution.get("function").is_some(), "unresolved body: {resolution}");
    }
}

/// Also run the zero-argument program in the existing two-language fixtures.
fn assert_judged(json: &Value, crate_name: &str, program_value: &str) {
    assert_clone_judged(json, crate_name);
    let dump = || serde_json::to_string_pretty(json).unwrap();
    let program = json["interpreted"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["display_path"] == "program")
        .unwrap_or_else(|| panic!("program was not interpreted: {}", dump()));
    assert_eq!(program["value"]["raw"], program_value, "{}", dump());
}

fn summary<'a>(json: &'a Value, name: &str) -> &'a Value {
    json["summaries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["display_path"] == name)
        .unwrap_or_else(|| panic!("no summary for {name}: {json}"))
}

fn bindings(clause: &Value) -> Vec<String> {
    clause["bindings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| format!("{}:{}:{}", b["name"].as_str().unwrap(), b["sort"].as_str().unwrap(), b["place"]))
        .collect()
}

fn assert_artifact_unchanged(crate_name: &str, with: &Path, without: &Path) {
    let file = format!("{crate_name}.trust-ir.bin");
    let a = rfs::read(with.join(&file));
    let b = rfs::read(without.join(&file));
    assert!(!a.is_empty());
    assert!(a == b, "the shadow changed the published {file}");
    for dir in [with, without] {
        let coverage: Value = serde_json::from_str(&rfs::read_to_string(
            dir.join(format!("{crate_name}.trust-ir.coverage.json")),
        )).unwrap();
        assert_eq!(coverage["direct_obligation_capability"], "obligation-bearing-pending-v2");
        assert_eq!(coverage["proof_authority"], false);
        assert_eq!(coverage["native_verification_requests"], false);
    }
}

/// Isolate the actual production body without copying its implementation.
/// Only the existing macro's two exact clauses are re-spelled in native grammar.
fn shift_mask_subject() -> PathBuf {
    const DECLARATION: &str = "pub fn shift_mask(target_width: u32) -> u32\n\
clauses [ensures result <= 127 ensures result <= target_width]\n";
    let source = rfs::read_to_string(source_root().join("crates/trust-widthconv/src/lib.rs"));
    assert_eq!(source.matches(DECLARATION).count(), 1, "the original clause pair changed");
    let remainder = source.split_once(DECLARATION).unwrap().1;
    let body = remainder.split_once("\n}\n}").expect("function then macro close").0;
    assert!(body.starts_with("{\n"));
    let path = PathBuf::from("shift_mask.rs");
    rfs::write(&path, format!(
        "pub fn shift_mask(target_width: u32) -> u32\n\
    ensures result <= 127\n\
    ensures result <= target_width\n{body}\n}}\n",
    ));
    path
}

fn assert_native_refused(json: &Value) {
    let native = &json["native_wp"];
    assert_eq!(native["status"], "refused", "{native}");
    assert_eq!(native["authority"], "NONE", "{native}");
    assert!(!native["reason"].as_str().unwrap().is_empty());
    assert!(native.get("bundle").is_none(), "a refusal emitted a native bundle: {native}");
}

/// Inspect actual emitted questions; solving/replay belongs to the portable WP tests.
fn assert_shift_mask_questions(json: &Value) {
    assert_clone_judged(json, "trust_widthconv");
    assert_eq!(json["outcome"]["rows_installed"], 2, "{json}");
    assert_eq!(json["outcome"]["clauses_typed"], 2, "{json}");
    assert_eq!(json["outcome"]["clauses_opaque"], 0, "{json}");
    let staged = summary(json, "shift_mask");
    assert_eq!(staged["proved"], false);
    assert_eq!(staged["backed_by"], Value::Null);
    assert!(staged["requires"].as_array().unwrap().is_empty());
    assert!(staged["decreases"].as_array().unwrap().is_empty());
    assert_eq!(staged["ensures"].as_array().unwrap().len(), 2);

    let native = &json["native_wp"];
    assert_eq!(native["status"], "questions", "{native}");
    assert_eq!(native["authority"], "NONE");
    assert!(!native["non_applying_checks"].as_array().unwrap().is_empty());
    let public = &native["public"];
    let rows = public["obligations"].as_array().unwrap();
    let contracts = public["contracts"].as_array().unwrap();
    assert_eq!(rows.len(), 2, "the authored question denominator changed: {native}");
    assert_eq!(contracts.len(), 2);
    let public_ids: BTreeSet<_> = rows.iter()
        .map(|row| row["obligation_id"].as_str().unwrap()).collect();
    assert_eq!(public_ids.len(), 2);
    // Compare actual predicates with the retained original compiler questions,
    // independent of this new diagnostic producer's IDs and source spans.
    let original: Value = serde_json::from_str(&rfs::read_to_string(source_root().join(
        "crates/trust-bmc/testdata/widthconv-shift-mask/public.json",
    ))).unwrap();
    for (index, row) in rows.iter().enumerate() {
        assert_eq!(row["kind"], "Postcondition");
        assert!(row.get("summary_facts").is_none_or(|facts| facts.as_array().unwrap().is_empty()));
        let contract = contracts.iter().find(|contract| {
            contract["contract_id"] == row["contract_id"]
        }).unwrap();
        let original_id = format!("trust-contract:trust_widthconv::shift_mask:ensures:{index}");
        let expected = original["contracts"].as_array().unwrap().iter()
            .find(|contract| contract["contract_id"] == original_id).unwrap();
        assert_eq!(contract["kind"], "Ensures");
        assert_eq!(contract["predicate"], expected["predicate"], "original clause {index} changed");
    }

    let bundle = &native["bundle"];
    // NativeBundleProducer::TRust has the ratified JSON spelling "Trust".
    assert_eq!(bundle["producer"], "Trust");
    assert_eq!(bundle["input"], "TrustIrModule");
    assert_eq!(bundle["provenance"]["source_digest"], Value::Null);
    assert_ne!(native["pristine_module_digest"], bundle["trust_ir_module_digest"]);
    assert!(bundle.get("evidence_bundles").is_none_or(|rows| rows.as_array().unwrap().is_empty()));
    let module = &bundle["module"];
    assert!(module["proof_certificates"].as_array().unwrap().is_empty());
    let functions = module["functions"].as_array().unwrap();
    assert_eq!(functions.len(), 1);
    assert_eq!(functions[0]["producer"], "Trust");
    assert_eq!(functions[0]["summary"]["proved"], false);
    assert_eq!(functions[0]["summary"]["backed_by"], Value::Null);
    let proofs = module["proof_obligations"].as_array().unwrap();
    assert_eq!(proofs.len(), 2);
    let proof_ids: BTreeSet<_> = proofs.iter().map(|proof| {
        assert_eq!(proof["kind"], "Postcondition");
        assert_eq!(proof["status"], "Pending");
        let public_id = proof["source"]["public"]["obligation_id"].as_str().unwrap();
        assert!(public_ids.contains(public_id));
        proof["id"].as_u64().unwrap()
    }).collect();
    assert_eq!(proof_ids.len(), 2);
    let requests = bundle["requests"].as_array().unwrap();
    assert_eq!(requests.len(), 4, "two primary and two alternative questions: {native}");
    assert_eq!(requests.iter().filter(|request| request.get("TrustMc").is_some()).count(), 2);
    let wp: Vec<_> = requests.iter().filter_map(|request| request.get("TrustWp")).collect();
    assert_eq!(wp.len(), 2, "both authored clauses need a WP request");
    let requested_ids: BTreeSet<_> = wp.into_iter().map(|request| {
        assert_eq!(request["mode"], "WeakestPrecondition");
        assert_eq!(request["function"], functions[0]["id"]);
        assert_eq!(request["obligations"].as_array().unwrap().len(), 1);
        assert!(request["provenance"]["replay"]["invocation"].as_str().unwrap()
            .contains("SHADOW LANE (lineage-unanchored)"));
        request["obligations"][0].as_u64().unwrap()
    }).collect();
    assert_eq!(requested_ids, proof_ids, "missing or duplicated authored WP question");
}

fn main() {
    let shadow_dir = PathBuf::from("shadow");
    rfs::create_dir(&shadow_dir);

    // ---- p01: requires / ensures / decreases --------------------------------
    let p01 = fixture("ir-ta01_rust_contracts", "p01_rust_contracts.rs");
    let with = emit(&p01, "p01", "shadow", Some(&shadow_dir));
    let without = emit(&p01, "p01", "plain", None);
    assert_artifact_unchanged("p01", &with, &without);
    let json = shadow_json(&shadow_dir, "p01");
    assert_judged(&json, "p01", "49");
    assert_native_refused(&json);

    let clamp = summary(&json, "clamp_add");
    assert_eq!(clamp["proved"], false);
    assert_eq!(clamp["backed_by"], Value::Null);
    assert_eq!(strings(&clamp["params"]), vec!["\"x\"", "\"y\""]);
    let requires = clamp["requires"].as_array().unwrap();
    assert_eq!(requires.len(), 2, "{clamp}");
    for clause in requires {
        assert_eq!(clause["schema"], "trust.contract-clause@1", "{clause}");
    }
    assert_eq!(bindings(&requires[0]), vec!["x:BitVec(64):{\"param\":0}"]);
    assert_eq!(bindings(&requires[1]), vec!["y:BitVec(64):{\"param\":1}"]);
    assert_eq!(requires[0]["smtlib"], "(bvule x (_ bv1000 64))", "{clamp}");
    let ensures = &clamp["ensures"][0];
    assert_eq!(ensures["schema"], "trust.contract-clause@1", "{clamp}");
    assert_eq!(
        bindings(ensures),
        vec![
            "_0:BitVec(64):{\"result\":0}",
            "x:BitVec(64):{\"param\":0}",
            "y:BitVec(64):{\"param\":1}",
        ]
    );
    let countdown = summary(&json, "countdown");
    assert_eq!(bindings(&countdown["decreases"][0]), vec!["n:BitVec(64):{\"param\":0}"]);

    let rows = json["rows"].as_array().unwrap();
    let kinds: Vec<&str> = rows.iter().map(|r| r["kind"].as_str().unwrap()).collect();
    assert_eq!(kinds, vec!["Precondition", "Precondition", "Postcondition", "Termination"]);
    for row in rows {
        assert_eq!(row["status"], "pending", "{row}");
        assert_eq!(row["site"], Value::Null, "a function clause is unsited: {row}");
        assert_ne!(row["formula"], Value::Null, "{row}");
    }

    // ---- p02: a while loop's invariant and decreases --------------------------
    let p02 = fixture("ir-ta02_rust_loop_invariant", "p02_rust_loop_invariant.rs");
    let with = emit(&p02, "p02", "shadow", Some(&shadow_dir));
    let without = emit(&p02, "p02", "plain", None);
    assert_artifact_unchanged("p02", &with, &without);
    let json = shadow_json(&shadow_dir, "p02");
    assert_judged(&json, "p02", "45");
    assert_native_refused(&json);

    let sum = summary(&json, "sum_below");
    assert_eq!(bindings(&sum["requires"][0]), vec!["n:BitVec(64):{\"param\":0}"]);
    let rows = json["rows"].as_array().unwrap();
    let kinds: Vec<&str> = rows.iter().map(|r| r["kind"].as_str().unwrap()).collect();
    assert_eq!(kinds, vec!["Precondition", "LoopInvariant", "Termination"], "{json}");
    let invariant = &rows[1];
    let site = &invariant["site"];
    assert_ne!(*site, Value::Null, "a loop row is sited: {invariant}");
    assert_eq!(site["inst"], 0);
    assert_eq!(site["function"], invariant["function"]);
    assert_eq!(rows[2]["site"], *site, "both loop rows sit at the same header");
    let formula = &invariant["formula"];
    assert_eq!(formula["schema"], "trust.contract-clause@1", "{invariant}");
    let invariant_bindings = bindings(formula);
    assert_eq!(invariant_bindings.len(), 2, "{invariant}");
    assert!(invariant_bindings[0].starts_with("i:BitVec(64):{\"value\":"), "{invariant}");
    assert!(invariant_bindings[1].starts_with("n:BitVec(64):{\"value\":"), "{invariant}");
    assert_eq!(formula["smtlib"], "(bvule i n)", "{invariant}");

    // ---- actual isolated U32 source: diagnostic native WP questions ----------
    let source = shift_mask_subject();
    let with = emit(&source, "trust_widthconv", "shadow", Some(&shadow_dir));
    let without = emit(&source, "trust_widthconv", "plain", None);
    assert_artifact_unchanged("trust_widthconv", &with, &without);
    assert_shift_mask_questions(&shadow_json(&shadow_dir, "trust_widthconv"));

}

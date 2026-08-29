//! Trust: the STOCK-SURVIVING loop-clause transport must MEAN the same thing
//! as the native clause position, and the evidence must be the obligations.
//!
//! `#[cfg_attr(trust_verify, trust::loop_invariant(P))]` on a `while`/`loop`
//! expression is the only spelling of a loop clause a crate that must ALSO
//! build on stock rustc can write. Measured on stock rustc 1.97.1 (8bab26f4f,
//! ay's pinned channel): with the cfg unset that file compiles clean and emits
//! metadata, while both the native grammar and a direct
//! `#[trust::loop_invariant(..)]` are hard errors there.
//!
//! Exit status is not evidence. A transported clause that parsed and was then
//! dropped compiles clean and is CREDITED as verified — the silent acceptance
//! the two-language design forbids, and the failure mode this codebase has
//! shipped before (`#[trust::invariant]` was silently erased; a `decreases`
//! passthrough erased a FALSE measure and the function was credited). So this
//! test reads the typed obligation stream and asserts KINDS, COUNTS and
//! OUTCOMES.
//!
//! What it pins:
//!   * the attribute surface and the native surface, given the same authored
//!     facts about the same loop, produce an IDENTICAL (kind, outcome)
//!     multiset — on `loop` AND on `while`. One desugaring, one meaning,
//!     observationally rather than by inspection. A dropped clause fails this,
//!     because the native side proves three loop obligations the empty ledger
//!     does not have.
//!   * a FALSE transported invariant is still asked at both program points and
//!     is not proved at entry. Refusals stay refusals across the transport.
//!   * a bogus transported measure yields an unproved termination obligation.
//!
//! The misplacement and malformed-payload refusals are UI tests:
//! `tests/ui/trust/loop_clause_attr_*.rs`.

use std::collections::BTreeMap;
use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rustc_path, serde_json};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

/// The (typed obligation kind -> outcome) multiset for one compilation.
type Ledger = BTreeMap<String, BTreeMap<String, usize>>;

fn trustc() -> PathBuf {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    if trustc.exists() { trustc } else { rustc }
}

/// Compile `source` through the verifier in advisory mode and return the typed
/// obligation ledger. Advisory keeps a refusal from aborting the compile, so
/// the negative fixtures still emit their rows and can be inspected.
fn ledger(source: &str) -> Ledger {
    let report = cmd(trustc())
        .env_remove("TRUST_NO_VERIFY")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-level=2")
        .arg("-Ztrust-verify-output=both")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("-Awarnings")
        .arg(source)
        .run()
        .stderr_utf8();

    let mut ledger = Ledger::new();
    let mut saw_function_result = false;
    for line in report.lines() {
        let Some(payload) = line.strip_prefix("TRUST_JSON:") else { continue };
        let value: serde_json::Value = match serde_json::from_str(payload) {
            Ok(value) => value,
            Err(_) => continue,
        };
        if value["type"] != "function_result" {
            continue;
        }
        saw_function_result = true;
        for result in value["results"].as_array().expect("typed obligation array") {
            let kind = match &result["typed_kind"] {
                serde_json::Value::String(name) => name.clone(),
                serde_json::Value::Object(map) => {
                    map.keys().next().expect("typed_kind object has a variant key").clone()
                }
                other => panic!("unexpected typed_kind shape in {source}: {other}"),
            };
            let outcome = result["outcome"].as_str().expect("every row has an outcome").to_string();
            *ledger.entry(kind).or_default().entry(outcome).or_default() += 1;
        }
    }
    assert!(
        saw_function_result,
        "{source} emitted no typed function result at all -- the verifier did not run, so nothing \
         below would be evidence:\n{report}"
    );
    ledger
}

fn count(ledger: &Ledger, kind: &str, outcome: &str) -> usize {
    ledger.get(kind).and_then(|by_outcome| by_outcome.get(outcome)).copied().unwrap_or(0)
}

fn total(ledger: &Ledger, kind: &str) -> usize {
    ledger.get(kind).map(|by_outcome| by_outcome.values().sum()).unwrap_or(0)
}

/// The reference surface must actually be discharging the loop facts;
/// otherwise a parity assertion is an agreement between two empties. This is
/// the guard that makes a DROPPED transported clause fail this test rather
/// than pass it.
fn assert_reference_is_live(name: &str, ledger: &Ledger) {
    for kind in ["LoopInvariantInitiation", "LoopInvariantConsecution", "NonTermination"] {
        assert_eq!(
            count(ledger, kind, "proved"),
            1,
            "the {name} reference did not prove {kind}, so parity against it would be vacuous: \
             {ledger:?}"
        );
    }
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let native_loop = ledger("surface_native_loop.rs");
    let attr_loop = ledger("surface_attr_loop.rs");
    assert_reference_is_live("native `loop`", &native_loop);
    assert_eq!(
        native_loop, attr_loop,
        "the native and attribute surfaces disagreed on the same authored facts on `loop`.\n \
         native: {native_loop:?}\n attr:   {attr_loop:?}"
    );

    let native_while = ledger("surface_native_while.rs");
    let attr_while = ledger("surface_attr_while.rs");
    assert_reference_is_live("native `while`", &native_while);
    assert_eq!(
        native_while, attr_while,
        "the native and attribute surfaces disagreed on the same authored facts on `while`.\n \
        native: {native_while:?}\n attr:   {attr_while:?}"
    );

    // The verifier's exact positive owner set is free functions and
    // associated functions. The free-function rows above cover the former;
    // this fixture makes the latter observable in the obligation stream.
    // Keeping this positive guard beside the unsupported-owner UI test stops
    // a fail-closed repair from accidentally becoming "refuse everything".
    let attr_assoc = ledger("surface_attr_assoc.rs");
    assert_reference_is_live("attribute clause in an associated function", &attr_assoc);
    assert_eq!(
        attr_loop, attr_assoc,
        "the same transported loop contract changed meaning in an associated function.\n \
         free fn: {attr_loop:?}\n assoc fn: {attr_assoc:?}"
    );

    // Negative: a FALSE transported invariant must still be ASKED and must not
    // be proved at entry. Both halves matter -- a dropped clause also reports
    // zero proved rows, so it is the obligation COUNT that separates the two.
    //
    // `loop_invariant(n == 0)` on a countdown from `limit` is false ON ENTRY
    // and vacuously preserved thereafter, so the exact expected shape is
    // initiation refused and consecution proved. That asymmetry is the point:
    // the transported clause is being evaluated at two distinct program
    // points, not waved through as one lump.
    let false_ledger = ledger("surface_attr_false.rs");
    assert_eq!(
        total(&false_ledger, "LoopInvariantInitiation"),
        1,
        "a false transported invariant produced no initiation obligation: {false_ledger:?}"
    );
    assert_eq!(
        count(&false_ledger, "LoopInvariantInitiation", "proved"),
        0,
        "a false transported invariant was PROVED at entry: {false_ledger:?}"
    );
    assert_eq!(
        total(&false_ledger, "LoopInvariantConsecution"),
        1,
        "a false transported invariant produced no consecution obligation: {false_ledger:?}"
    );

    // Negative: a bogus transported measure must produce a termination
    // obligation that is not proved.
    let bogus_ledger = ledger("surface_attr_bogus_measure.rs");
    assert_eq!(
        total(&bogus_ledger, "NonTermination"),
        1,
        "a bogus transported measure produced no termination obligation: {bogus_ledger:?}"
    );
    assert_eq!(
        count(&bogus_ledger, "NonTermination", "proved"),
        0,
        "a bogus transported measure was PROVED to terminate: {bogus_ledger:?}"
    );
}

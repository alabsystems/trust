//! Trust: the E4/E5 clause positions on `while` and `loop` must produce THE
//! SAME OBLIGATIONS, not merely the same exit code.
//!
//! Exit status is not evidence here. A clause that parsed and was then dropped
//! would compile clean and be credited as verified -- that is the silent
//! acceptance the two-language design forbids, and it is exactly what an
//! `invariant` on `loop` did before this change (it was a parse error, which
//! at least failed closed; the danger now is the opposite direction). So this
//! test reads the typed obligation stream and asserts the KINDS, the count,
//! and the outcomes.
//!
//! What it pins:
//!   * `while` and `loop`, given the same authored facts about the same loop,
//!     produce an identical (kind, outcome) multiset. One parser entry, one
//!     lowering, one meaning -- observationally, not by inspection.
//!   * a false `loop` invariant produces the obligations and fails to prove
//!     them, and a bogus `loop` measure produces a termination obligation that
//!     is not proved. Refusals stay refusals.
//!
//! `for` is covered by `tests/ui/trust/loop_clause_for_refused.rs`: it has no
//! clause position, and the parser says why.

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
            // `typed_kind` is either a bare variant name or a single-key
            // object carrying the variant payload; identity is the variant.
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

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let while_ledger = ledger("surface_while.rs");
    let loop_ledger = ledger("surface_loop.rs");

    // The reference surface must actually be discharging the loop facts;
    // otherwise the equality below would be an agreement between two empties.
    assert_eq!(
        count(&while_ledger, "LoopInvariantInitiation", "proved"),
        1,
        "the `while` reference did not prove initiation: {while_ledger:?}"
    );
    assert_eq!(
        count(&while_ledger, "LoopInvariantConsecution", "proved"),
        1,
        "the `while` reference did not prove consecution: {while_ledger:?}"
    );
    assert_eq!(
        count(&while_ledger, "NonTermination", "proved"),
        1,
        "the `while` reference did not prove termination: {while_ledger:?}"
    );

    assert_eq!(
        while_ledger, loop_ledger,
        "`while` and `loop` disagreed on the same authored facts.\n while: {while_ledger:?}\n \
         loop:  {loop_ledger:?}"
    );

    // Negative: a false `loop` invariant must still be ASKED and must not be
    // proved. Both halves matter -- a dropped clause would also report zero
    // proved rows, so the obligation count is what separates the two.
    //
    // `invariant n == 0` on `loop { if n == 0 { break } n -= 1 }` is false ON
    // ENTRY (`n` starts at `limit`) and vacuously preserved thereafter, so the
    // exact expected shape is initiation refused and consecution proved. That
    // asymmetry is the point: the clause is being evaluated at two distinct
    // program points, not waved through as one lump.
    let false_ledger = ledger("surface_loop_false.rs");
    assert_eq!(
        total(&false_ledger, "LoopInvariantInitiation"),
        1,
        "a false `loop` invariant produced no initiation obligation: {false_ledger:?}"
    );
    assert_eq!(
        count(&false_ledger, "LoopInvariantInitiation", "proved"),
        0,
        "a false `loop` invariant was PROVED at entry: {false_ledger:?}"
    );
    assert_eq!(
        total(&false_ledger, "LoopInvariantConsecution"),
        1,
        "a false `loop` invariant produced no consecution obligation: {false_ledger:?}"
    );

    // Negative: a bogus measure must produce a termination obligation that is
    // not proved.
    let bogus_ledger = ledger("surface_loop_bogus_measure.rs");
    assert_eq!(
        total(&bogus_ledger, "NonTermination"),
        1,
        "a bogus `loop` measure produced no termination obligation: {bogus_ledger:?}"
    );
    assert_eq!(
        count(&bogus_ledger, "NonTermination", "proved"),
        0,
        "a bogus `loop` measure was PROVED to terminate: {bogus_ledger:?}"
    );
}

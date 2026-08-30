//! STEP 1 of the direct-lane proof-authority plan: every INSTRUCTION-scoped
//! proof obligation the native lane mints must name the instruction it is about.
//!
//! Before this test, every row in the native bundle shipped `site: None`. That
//! is not a cosmetic gap. A `ProofObligation` with no `ObligationSite` says
//! "something in this function must be proved" without saying what, so a
//! consumer that wants to attach a solver result to a specific check has to
//! re-derive the binding from the description string. `trust-mc` is about to
//! become that consumer, and a re-derived binding is exactly the kind of
//! coincidence that holds until it silently does not.
//!
//! The binding is deliberately hard to establish, which is why this is measured
//! rather than assumed. Spans are NOT unique per instruction: in the fixture
//! below the span of `a / b` covers ELEVEN trust_ir instructions, TWO of them
//! asserts (the divisor check and the signed `MIN / -1` overflow check). So the
//! mint resolves on three discriminators together — span, `Inst::Assert`, and
//! the assert's own `ProofAnnotation` — and when they still do not pick out
//! exactly one instruction it emits `None` rather than guessing. A wrong site is
//! worse than an absent one: it binds a verifier to the wrong solver condition
//! while looking correct in review.
//!
//! What this test pins is the CONSEQUENCE of that rule, both halves of it:
//!   * the four arithmetic rows resolve to a site, and to four DISTINCT sites;
//!   * the function-scoped CHC admission row does NOT, because no single
//!     instruction is what it is about.
//! A change that made the mint guess would turn the second assertion red, and a
//! change that dropped the binding would turn the first red. Freezing a
//! checked-in bundle would catch neither, so the fixture is compiled here.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

/// Set by compiletest's `--trust-vanilla` replay, which runs the stock rustc.
/// That build has no verifier, so it mints no obligations and there is
/// nothing here to assert -- the same opt-out `//@ needs-trust-verify` gives
/// the ui tests, spelled the way run-make has to spell it.
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const CRATE_NAME: &str = "obligation_site_probe";
const DUMP_DIRECTORY: &str = "native-bundle";

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    rfs::write(
        "probe.rs",
        "#![allow(dead_code)]\n\
         pub fn f(a: i32, b: i32) -> i32 {\n\
         \x20   let s = a + b;\n\
         \x20   let d = a / b;\n\
         \x20   s * d\n\
         }\n",
    );

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    cmd(trustc)
        .args([
            "--edition=2021",
            "--crate-type=lib",
            &format!("--crate-name={CRATE_NAME}"),
            "-Ztrust-verify=on",
            "-Ztrust-ir-lower=on",
            &format!("-Ztrust-dump=native-bundle:{DUMP_DIRECTORY}"),
            "probe.rs",
        ])
        // `run_unchecked`, not `run`: this fixture does NOT verify -- `a + b`
        // overflows at `a = i32::MAX, b = 1`, so the fail-closed verifier
        // correctly rejects it and rustc exits nonzero. That is a verdict about
        // the PROGRAM. Whether an obligation names the instruction it is about
        // is a property of the bundle, independent of whether the obligation is
        // later discharged, and a fixture with no failing check would mint
        // nothing to bind.
        .run_unchecked();

    let bundle = rfs::read_dir(DUMP_DIRECTORY)
        .filter_map(|entry| {
            let path = entry.expect("read native-bundle directory entry").path();
            let name = path.file_name()?.to_string_lossy().into_owned();
            (name.starts_with("trust-native-bundle-") && name.ends_with(".json")).then_some(path)
        })
        .next()
        .expect("-Ztrust-dump=native-bundle: wrote no bundle");

    let json: serde_json::Value =
        serde_json::from_slice(&rfs::read(&bundle)).expect("the bundle must be valid JSON");
    let rows = json["module"]["proof_obligations"]
        .as_array()
        .expect("the bundle module must carry a proof_obligations array");

    // Read off the descriptions rather than hardcoding indices: if the lowering
    // changes shape this re-derives instead of asserting against a stale map.
    let (instruction_scoped, function_scoped): (Vec<_>, Vec<_>) = rows.iter().partition(|row| {
        let description = row["description"].as_str().unwrap_or_default();
        description.contains("arithmetic overflow")
            || description.contains("division by zero")
            || description.contains("remainder by zero")
    });

    assert_eq!(
        instruction_scoped.len(),
        4,
        "fixture drift: the arithmetic body should mint 4 instruction-scoped \
         obligations (add overflow, div-by-zero, signed MIN/-1, mul overflow), got {}",
        rows.len()
    );

    let mut sites = Vec::new();
    for row in &instruction_scoped {
        let description = row["description"].as_str().unwrap_or_default();
        let site = row.get("site").filter(|site| !site.is_null()).unwrap_or_else(|| {
            panic!(
                "obligation `{description}` shipped site: None -- the mint could not bind it \
                 to an instruction, so a consumer cannot tell WHICH check it is about"
            )
        });
        sites.push(site.to_string());
    }

    // Distinctness is the half that catches a mint which "resolves" by picking
    // the first assert it sees: four rows would each carry a site and every one
    // of them would be the same wrong instruction.
    let mut distinct = sites.clone();
    distinct.sort();
    distinct.dedup();
    assert_eq!(
        distinct.len(),
        sites.len(),
        "two obligations bound to the SAME instruction; the mint is guessing rather than \
         resolving: {sites:?}"
    );

    for row in &function_scoped {
        let description = row["description"].as_str().unwrap_or_default();
        assert!(
            row.get("site").is_none_or(serde_json::Value::is_null),
            "function-scoped obligation `{description}` was bound to a single instruction, \
             but no one instruction is what it is about -- the mint is over-claiming"
        );
    }
}

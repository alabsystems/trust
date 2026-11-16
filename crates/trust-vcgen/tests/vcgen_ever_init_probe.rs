//! MEASUREMENT HARNESS (not a gate): run VC generation on one extracted
//! `VerifiableFunction` and print what it cost, so peak RSS and CPU can be read
//! off `/usr/bin/time -l` around THIS process alone.
//!
//! The input is the compiler's own extraction of the `ever-init-many-locals`
//! shape (`tests/ui/borrowck/ever-init-many-locals.rs` with N locals), dumped by
//! `trustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-no-r1
//! -Ztrust-dump=mir-only:<dir>`. Point `TRUST_VCGEN_PROBE_JSON` at the dumped
//! `many_locals` JSON and run
//!
//! ```text
//! /usr/bin/time -l <this test binary> --ignored --exact probe_generate_vcs_on_json
//! ```
//!
//! It is `#[ignore]`d because it has no input of its own and asserts nothing
//! about cost: wall time and RSS are machine properties, so the linearity GATE
//! lives in `src/generate/version_ssa_scaling_tests.rs` as deterministic work
//! counters.
use trust_types::VerifiableFunction;

#[test]
#[ignore = "measurement harness: needs TRUST_VCGEN_PROBE_JSON; run under /usr/bin/time -l"]
fn probe_generate_vcs_on_json() {
    let Ok(path) = std::env::var("TRUST_VCGEN_PROBE_JSON") else {
        eprintln!("TRUST_VCGEN_PROBE_JSON unset; nothing to measure");
        return;
    };
    let text = std::fs::read_to_string(&path).expect("read the dumped VerifiableFunction");
    let func: VerifiableFunction =
        serde_json::from_str(&text).expect("parse the dumped VerifiableFunction");
    drop(text);
    trust_vcgen::reset_analysis_memo_stats();
    let start = std::time::Instant::now();
    let vcs = trust_vcgen::generate_vcs(&func);
    let elapsed = start.elapsed();
    let bytes: usize = vcs.iter().map(|vc| format!("{:?}", vc.formula).len()).sum();
    println!(
        "PROBE fn={} blocks={} locals={} vcs={} vc_formula_bytes={bytes} gen_ms={} stats={:?}",
        func.name,
        func.body.blocks.len(),
        func.body.locals.len(),
        vcs.len(),
        elapsed.as_millis(),
        trust_vcgen::analysis_memo_stats(),
    );
}

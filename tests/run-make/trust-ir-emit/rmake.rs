//! Trust: `--emit=trust-ir` is a first-class analysis-phase artifact lane —
//! it must write the crate-level trust-ir binary Module at the requested
//! output path, with the canonical-text and coverage.json companions
//! alongside (extension swap on the `.bin`), WITHOUT the `-Z trust-ir-lower`
//! dev flag or the `-Z trust-dump=ir` dev flag, and without running codegen or
//! metadata emission (no `.rmeta`, no object artifacts).
//!
//! The coverage companion is the only published record of what the direct
//! producer could not lower, so this test also pins its HONESTY: the
//! capability/authority header must still read `structural-parity-only-v1` /
//! `proof_authority: false`, and a body that failed to lower must carry the
//! leaf-demand histogram that explains why. An empty histogram on a failed body
//! is indistinguishable, to every downstream consumer, from a body that
//! demanded nothing — so "the artifact exists and parses" is deliberately not
//! enough to pass here.
use std::path::Path;

use run_make_support::{rfs, rustc};

/// The text of `"<key>": [ … ]` inside a single coverage row up to the first
/// `]`, or `None` when the row carries no such key. Only emptiness is asserted
/// on the result, so stopping at a nested array's close is fine and keeps this
/// from being a second JSON parser.
fn array_field<'a>(row: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\": [");
    let start = row.find(&needle)? + needle.len();
    let end = start + row[start..].find(']')?;
    Some(row[start..end].trim())
}

/// The coverage row for `def_path`, as raw JSON text. The crate-module coverage
/// writer emits exactly one body per line.
fn body_row<'a>(coverage: &'a str, def_path: &str) -> &'a str {
    let needle = format!("\"def_path\": \"{def_path}\"");
    let start = coverage.find(&needle).unwrap_or_else(|| {
        panic!("coverage.json carries no body row for `{def_path}`:\n{coverage}")
    });
    let rest = &coverage[start..];
    rest.split('\n').next().unwrap_or(rest)
}

fn main() {
    let out_dir = Path::new("emit");
    rfs::create_dir(&out_dir);

    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&out_dir)
        .arg("-Ztrust-verify=off")
        .run();

    // The artifact triple, named from the crate name.
    assert!(out_dir.join("foo.trust-ir.bin").is_file(), "missing trust-ir binary artifact");
    assert!(out_dir.join("foo.trust-ir.txt").is_file(), "missing canonical-text companion");
    assert!(
        out_dir.join("foo.trust-ir.coverage.json").is_file(),
        "missing coverage.json companion"
    );

    // Analysis-only lane: no metadata, no codegen outputs.
    assert!(!out_dir.join("libfoo.rmeta").exists(), "trust-ir emit must not write metadata");
    assert!(!out_dir.join("foo.o").exists(), "trust-ir emit must not run codegen");

    // The binary artifact is non-empty and the coverage companion carries a
    // versioned schema tag. Matched on the stable prefix: a schema revision is a
    // deliberate, reviewable change to the fields asserted below, and pinning
    // the digit alone turns every revision into an unexplained failure that
    // reads as unrelated to whatever it actually broke.
    assert!(rfs::read(out_dir.join("foo.trust-ir.bin")).len() > 0);
    let cov = rfs::read_to_string(out_dir.join("foo.trust-ir.coverage.json"));
    assert!(
        cov.contains("\"schema\": \"trust.thir-lower.crate-module.coverage.v"),
        "coverage.json missing schema tag"
    );

    // The direct producer has no proof and no native-request authority. A
    // published artifact that says otherwise is a soundness event, not a golden
    // to re-bless.
    assert!(
        cov.contains("\"direct_obligation_capability\": \"structural-parity-only-v1\""),
        "coverage.json must publish the direct producer's declared capability"
    );
    assert!(
        cov.contains("\"proof_authority\": false"),
        "the direct THIR producer must never publish proof authority"
    );
    assert!(
        cov.contains("\"native_verification_requests\": false"),
        "the direct THIR producer must never publish native verification requests"
    );

    // `add` is inside the lowerable fragment: no unsupported shapes, hence no
    // leaf demand to explain.
    let add = body_row(&cov, "add");
    assert_eq!(array_field(add, "unsupported"), Some(""), "`add` must lower cleanly: {add}");
    assert_eq!(array_field(add, "collect_primary"), Some(""));

    // `evens` is outside it (an RPIT return type and a closure in value
    // position). Its first-fail inventory and its collect-all leaf demand must
    // BOTH be published: the first-fail prefix attributes a whole subtree to one
    // masking tag, which is the entire reason the second histogram exists.
    let evens = body_row(&cov, "evens");
    assert_ne!(
        array_field(evens, "unsupported"),
        Some(""),
        "`evens` must record unsupported shapes: {evens}"
    );
    let primary = array_field(evens, "collect_primary")
        .expect("coverage row must carry a collect_primary field");
    assert!(
        !primary.is_empty(),
        "`evens` failed to lower but published an EMPTY collect_primary histogram — the \
         collect-all measurement pass never ran for a pure `--emit=trust-ir` invocation, so the \
         artifact reports a failed body as demanding no leaf shapes: {evens}"
    );
}

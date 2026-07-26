use std::ffi::OsString;

use super::rustdoc_bootstrap_no_verify_applies;
use super::shared_helpers::{canonicalize_trust_no_verify, finalize_trust_no_verify};

fn args(values: &[&str]) -> Vec<OsString> {
    values.iter().map(OsString::from).collect()
}

#[test]
fn no_verify_covers_real_rustdoc_compiles_when_requested() {
    let compile = args(&["src/lib.rs", "--crate-name", "fixture"]);

    assert!(rustdoc_bootstrap_no_verify_applies(true, true, &compile, Some("fixture"),));
    assert!(!rustdoc_bootstrap_no_verify_applies(false, true, &compile, Some("fixture"),));
}

#[test]
fn no_verify_covers_direct_rustdoc_without_crate_name() {
    let compile = args(&["src/lib.rs"]);
    assert!(rustdoc_bootstrap_no_verify_applies(true, true, &compile, None,));
}

#[test]
fn no_verify_skips_rustdoc_probes_and_unsupported_drivers() {
    let probe = args(&["-", "--crate-name", "___", "--print=file-names"]);
    assert!(!rustdoc_bootstrap_no_verify_applies(true, true, &probe, Some("___"),));

    let compile = args(&["src/lib.rs", "--crate-name", "fixture"]);
    assert!(!rustdoc_bootstrap_no_verify_applies(true, false, &compile, Some("fixture"),));
}

#[test]
fn untargeted_rustdoc_compile_gets_one_canonical_no_verify_switch() {
    let mut rustdoc_args = args(&[
        "src/lib.rs",
        "--crate-name",
        "fixture",
        "-Ztrust_verify=on",
        "-Z",
        "trust-verify=on",
    ]);
    let applies = rustdoc_bootstrap_no_verify_applies(true, true, &rustdoc_args, Some("fixture"));
    finalize_trust_no_verify(&mut rustdoc_args, true, applies);

    assert_eq!(
        rustdoc_args,
        args(&["src/lib.rs", "--crate-name", "fixture", "-Ztrust-verify=off",])
    );
}

#[test]
fn no_verify_is_canonical_and_precedes_positional_tail() {
    let mut rustdoc_args = args(&[
        "src/lib.rs",
        "-Z",
        "trust_verify=on",
        "-Ztrust-verify=on",
        "--",
        "-Ztrust-verify=on",
    ]);
    canonicalize_trust_no_verify(&mut rustdoc_args);

    assert_eq!(
        rustdoc_args,
        args(&["src/lib.rs", "-Ztrust-verify=off", "--", "-Ztrust-verify=on",]),
    );
}

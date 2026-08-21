use std::ffi::OsString;

use super::shared_helpers::{
    canonicalize_trust_no_verify, finalize_trust_no_verify, trust_bootstrap_no_verify_applies,
};

fn args(values: &[&str]) -> Vec<OsString> {
    values.iter().map(OsString::from).collect()
}

/// Exactly rustdoc's call site. rustdoc resolves ONE driver, so the same
/// capability answer covers both the targeted and the untargeted arm of the
/// shared predicate — which is what makes the rustc shim's policy usable here
/// verbatim instead of copied.
fn rustdoc_applies(
    requested: bool,
    supports: bool,
    args: &[OsString],
    crate_name: Option<&str>,
) -> bool {
    let untargeted =
        trust_bootstrap_no_verify_applies(false, requested, supports, supports, args, crate_name);
    let targeted =
        trust_bootstrap_no_verify_applies(true, requested, supports, supports, args, crate_name);
    // rustdoc's own former copy of this predicate did not take `has_target` at
    // all. Pinning the two arms equal here is what keeps sharing the rustc
    // shim's policy a refactor rather than a behaviour change.
    assert_eq!(untargeted, targeted, "rustdoc has one driver; --target must not change the answer");
    untargeted
}

#[test]
fn no_verify_covers_real_rustdoc_compiles_when_requested() {
    let compile = args(&["src/lib.rs", "--crate-name", "fixture"]);

    assert!(rustdoc_applies(true, true, &compile, Some("fixture")));
    assert!(!rustdoc_applies(false, true, &compile, Some("fixture")));
}

#[test]
fn no_verify_covers_direct_rustdoc_without_crate_name() {
    let compile = args(&["src/lib.rs"]);
    assert!(rustdoc_applies(true, true, &compile, None));
}

#[test]
fn no_verify_skips_rustdoc_probes_and_unsupported_drivers() {
    let probe = args(&["-", "--crate-name", "___", "--print=file-names"]);
    assert!(!rustdoc_applies(true, true, &probe, Some("___")));

    let compile = args(&["src/lib.rs", "--crate-name", "fixture"]);
    assert!(!rustdoc_applies(true, false, &compile, Some("fixture")));
}

/// ONE POLICY, ONE IMPLEMENTATION. rustdoc used to keep a second copy of the
/// no-verify predicate that did not take `has_target` where the rustc version
/// did; the two had already diverged once historically. Both shims now call the
/// same function, so the only way to diverge again is to pass different
/// arguments — which is exactly what this enumerates.
#[test]
fn the_shared_no_verify_policy_is_the_rustdoc_policy() {
    let compile = args(&["src/lib.rs", "--crate-name", "fixture"]);
    let probe = args(&["-", "--crate-name", "___", "--print=file-names"]);
    let empty: Vec<OsString> = Vec::new();

    for argv in [&compile, &probe, &empty] {
        for requested in [false, true] {
            for supports in [false, true] {
                // The rustdoc answer, taken through the shared predicate.
                let shared = rustdoc_applies(requested, supports, argv, Some("fixture"));
                // The policy rustdoc's private copy encoded, spelled out.
                let is_real_compile = !argv.is_empty()
                    && !argv
                        .iter()
                        .any(|arg| arg.to_str().is_some_and(|arg| arg.starts_with("--print")));
                assert_eq!(
                    shared,
                    requested && supports && is_real_compile,
                    "requested={requested} supports={supports} argv={argv:?}"
                );
            }
        }
    }
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
    let applies = rustdoc_applies(true, true, &rustdoc_args, Some("fixture"));
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

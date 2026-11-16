use std::ffi::OsString;

use shim_utils::{
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

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): a `/bin/sh` launch whose custody
/// environment is decided here, not by the runner.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn custody_launch(script: &str, set: &[(&str, &str)]) -> std::process::Command {
    let mut cmd = std::process::Command::new("/bin/sh");
    cmd.args(["-c", script]);
    for name in super::GNU_ADVERTISEMENTS.into_iter().chain(super::STRICT_CUSTODY_MARKERS) {
        cmd.env_remove(name);
    }
    for (name, value) in set {
        cmd.env(name, value);
    }
    cmd
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): only a strict launch that inherited
/// nothing and was advertised nothing is lent, and a doctest run only when the
/// shim can hold it to one thread.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn rustdoc_is_lent_an_execution_only_when_owed_one() {
    use super::{Lending, lending_owed};
    let doc = args(&["src/lib.rs", "--crate-name", "fixture"]);
    let doctest = args(&["--test", "src/lib.rs", "--test-args", "--quiet"]);
    let strict = custody_launch("", &[("BUILD_SLOT_CPU_PROTOCOL", "1")]);
    assert_eq!(
        lending_owed(false, false, &strict, &doc),
        Lending::Lend { one_doctest_at_a_time: false }
    );
    assert_eq!(
        lending_owed(false, false, &strict, &doctest),
        Lending::Lend { one_doctest_at_a_time: true }
    );
    for marker in super::STRICT_CUSTODY_MARKERS {
        let strict = custody_launch("", &[(marker, "1")]);
        assert_ne!(lending_owed(false, false, &strict, &doc), Lending::Forward, "{marker}");
    }
    // An inherited scheduler, any inbound advertisement, an advertisement the
    // command itself carries, no strict marker, or a chosen doctest thread
    // count: forwarded, so the real rustdoc judges its own custody.
    assert_eq!(lending_owed(true, false, &strict, &doctest), Lending::Forward);
    assert_eq!(lending_owed(false, true, &strict, &doctest), Lending::Forward);
    for name in super::GNU_ADVERTISEMENTS {
        let advertised = custody_launch("", &[("BUILD_SLOT_CPU_PROTOCOL", "1"), (name, "-k")]);
        assert_eq!(lending_owed(false, false, &advertised, &doctest), Lending::Forward, "{name}");
    }
    assert_eq!(lending_owed(false, false, &custody_launch("", &[]), &doctest), Lending::Forward);
    for chosen in [
        args(&["--test", "src/lib.rs", "--test-args", "--test-threads=4"]),
        args(&["--test", "src/lib.rs", "--test-args=--quiet --test-threads 2"]),
        args(&["--test", "src/lib.rs", "--test-args", "--test-threads", "--test-args", "1"]),
        args(&["--test", "src/lib.rs", "--test-args=--test-threads=1 --test-threads=3"]),
    ] {
        assert_eq!(lending_owed(false, false, &strict, &chosen), Lending::Forward, "{chosen:?}");
    }
    for one in [
        args(&["--test", "src/lib.rs", "--test-args", "--test-threads=1"]),
        args(&["--test", "src/lib.rs", "--test-args=--quiet --test-threads=1"]),
    ] {
        assert_eq!(
            lending_owed(false, false, &strict, &one),
            Lending::Lend { one_doctest_at_a_time: true },
            "{one:?}"
        );
    }
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): every GNU option the launched process
/// receives names a descriptor open in it, and the handoff locator is present.
#[cfg(any(target_os = "linux", target_os = "macos"))]
const LENT_POOL_OPEN: &str = r#"
for value in "${CARGO_MAKEFLAGS-}" "${MAKEFLAGS-}" "${MFLAGS-}"; do
  case "$value" in *--jobserver-auth=*) ;; *) echo "no GNU auth in: [$value]" >&2; exit 3 ;; esac
  auth=${value##*--jobserver-auth=}
  auth=${auth%% *}
  if [ ! -e "/dev/fd/${auth%%,*}" ] || [ ! -e "/dev/fd/${auth##*,}" ]; then exit 4; fi
done
[ -n "${CARGO_JOBSERVER_HANDOFF-}" ] || exit 5
echo "lent-open threads=${RUST_TEST_THREADS-unset}"
"#;

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): a loan is an open pool with the
/// handoff that holds no token, read on its owner (a pool built with one token
/// is the reading's positive control), and a doctest loan holds the harness to
/// one thread.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn a_loan_is_an_open_empty_pool_with_the_handoff() {
    use super::{Lending, lend};
    for (one, threads) in [(false, "unset"), (true, "1")] {
        let mut cmd = custody_launch(LENT_POOL_OPEN, &[("BUILD_SLOT_CPU_PROTOCOL", "1")]);
        cmd.env_remove("RUST_TEST_THREADS");
        let lent = lend(Lending::Lend { one_doctest_at_a_time: one }, &mut cmd)
            .expect("an owed run is lent");
        assert_eq!(lent.client().available().unwrap(), 0);
        let output = cmd.output().unwrap();
        drop(cmd);
        drop(lent);
        let expected = format!("lent-open threads={threads}");
        assert!(
            output.status.success() && String::from_utf8_lossy(&output.stdout).contains(&expected),
            "{expected}: {output:?}"
        );
    }
    let control = jobserver_utils::Jobserver::new(1).unwrap();
    assert_eq!(control.client().available().unwrap(), 1);
}

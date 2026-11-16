//! Trust (CUSTODY-PROTOCOL1-LAUNCH-1): `lent_output` lends a launched compiler
//! the test's own execution only when it is owed one, a strict custody context
//! with no GNU advertisement at all. The loan is an owned pool that holds no
//! token and is open in the launched process, with the descendant handoff its
//! own children recover through, and two lent launches never overlap, whatever
//! libtest's thread count. Every other launch is forwarded unchanged.
#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::process::{Command, Output};

use trust_integration_tests::trust_rustc::{lend_execution, lent_output, owed_a_lent_execution};

/// Every GNU-related variable that `lent_output` judges or sets.
const GNU: [&str; 4] = ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF"];
/// Every strict custody marker the compiler reads, less the handoff.
const STRICT: [&str; 6] = [
    "BUILD_SLOT_CPU_PROTOCOL",
    "TRUST_CPU_HANDOFF",
    "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
];

/// A `/bin/sh` launch whose environment is decided here, not by the runner:
/// every GNU variable and strict marker removed, then `set` applied.
fn launch(script: &str, set: &[(&str, &str)]) -> Command {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", script]);
    for name in GNU.into_iter().chain(STRICT) {
        command.env_remove(name);
    }
    for (name, value) in set {
        command.env(name, value);
    }
    command
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// Every GNU option the launched process receives names a descriptor open in
/// it, and the handoff locator is present.
const LENT_POOL_OPEN: &str = r#"
for value in "${CARGO_MAKEFLAGS-}" "${MAKEFLAGS-}" "${MFLAGS-}"; do
  case "$value" in *--jobserver-auth=*) ;; *) echo "no GNU auth in: [$value]" >&2; exit 3 ;; esac
  auth=${value##*--jobserver-auth=}
  auth=${auth%% *}
  if [ ! -e "/dev/fd/${auth%%,*}" ] || [ ! -e "/dev/fd/${auth##*,}" ]; then
    echo "advertised $auth is not open in the launched process" >&2
    exit 4
  fi
done
[ -n "${CARGO_JOBSERVER_HANDOFF-}" ] || { echo "no descendant handoff" >&2; exit 5; }
echo "lent-pool-open"
"#;

/// The GNU variables the launched process received, verbatim.
const REPORT_GNU: &str = r#"
echo "C=[${CARGO_MAKEFLAGS-unset}] M=[${MAKEFLAGS-unset}] F=[${MFLAGS-unset}] H=[${CARGO_JOBSERVER_HANDOFF-unset}]"
"#;

#[test]
fn a_strict_launch_with_no_advertisement_borrows_an_open_pool() {
    for marker in STRICT {
        let mut command = launch(LENT_POOL_OPEN, &[(marker, "1")]);
        assert!(owed_a_lent_execution(&command), "{marker}");
        let output = lent_output(&mut command).unwrap();
        assert!(
            output.status.success() && stdout(&output).contains("lent-pool-open"),
            "{marker}: {output:?}"
        );
    }
}

/// The loan holds no token, read on its owner; the same reading of a pool
/// built with one token is the positive control.
#[test]
fn the_loan_holds_no_token() {
    let mut command = launch(LENT_POOL_OPEN, &[("BUILD_SLOT_CPU_PROTOCOL", "1")]);
    let loan = lend_execution(&mut command).unwrap();
    assert_eq!(loan.owner().client().available().unwrap(), 0);
    let output = command.output().unwrap();
    assert!(output.status.success() && stdout(&output).contains("lent-pool-open"), "{output:?}");
    drop(loan);
    let control = jobserver_utils::Jobserver::new(1).unwrap();
    assert_eq!(control.client().available().unwrap(), 1);
}

#[test]
fn an_advertisement_of_any_kind_is_forwarded_unchanged() {
    // Valid-looking, dangling, malformed and auth-free advertisements, and a
    // handoff with no make flags: the compiler's own capture judges each.
    let cases: [&[(&str, &str)]; 5] = [
        &[("CARGO_MAKEFLAGS", "-j --jobserver-auth=999998,999999")],
        &[("MAKEFLAGS", "--jobserver-auth=-2,-2")],
        &[("MFLAGS", "-k")],
        &[("CARGO_JOBSERVER_HANDOFF", "/no/such/ancestor")],
        &[("MAKEFLAGS", "--jobserver-fds=999998,999999"), ("CARGO_JOBSERVER_HANDOFF", "x")],
    ];
    for set in cases {
        let mut strict = set.to_vec();
        strict.push(("BUILD_SLOT_CPU_PROTOCOL", "1"));
        let mut command = launch(REPORT_GNU, &strict);
        assert!(!owed_a_lent_execution(&command), "{set:?}");
        let reported = stdout(&lent_output(&mut command).unwrap());
        for name in GNU {
            let expected = set.iter().find(|(key, _)| *key == name).map_or("unset", |(_, v)| v);
            let key = match name {
                "CARGO_MAKEFLAGS" => "C",
                "MAKEFLAGS" => "M",
                "MFLAGS" => "F",
                _ => "H",
            };
            assert!(reported.contains(&format!("{key}=[{expected}]")), "{set:?}: {reported}");
        }
    }
}

#[test]
fn a_launch_outside_a_strict_context_is_not_lent() {
    let mut command = launch(REPORT_GNU, &[]);
    assert!(!owed_a_lent_execution(&command));
    let reported = stdout(&lent_output(&mut command).unwrap());
    assert!(reported.contains("C=[unset] M=[unset] F=[unset] H=[unset]"), "{reported}");
}

#[test]
fn lent_launches_run_one_at_a_time() {
    let dir = tempfile::tempdir().unwrap();
    // `mkdir` is atomic: a second launch that overlapped the first finds the
    // directory still held and fails.
    let held = dir.path().join("held");
    let script = format!(
        "mkdir '{0}' || exit 9; sleep 0.2; rmdir '{0}' || exit 10; echo one-at-a-time",
        held.display()
    );
    let threads: Vec<_> = (0..4)
        .map(|_| {
            let script = script.clone();
            std::thread::spawn(move || {
                let mut command = launch(&script, &[("BUILD_SLOT_CPU_PROTOCOL", "1")]);
                assert!(owed_a_lent_execution(&command));
                lent_output(&mut command).unwrap()
            })
        })
        .collect();
    for thread in threads {
        let output = thread.join().unwrap();
        assert!(output.status.success() && stdout(&output).contains("one-at-a-time"), "{output:?}");
    }
}

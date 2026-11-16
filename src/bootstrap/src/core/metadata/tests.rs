use std::ffi::OsStr;
use std::path::Path;

use super::workspace_metadata_command;

// Trust: inspect the actual startup request, not a policy-only predicate.
#[test]
fn workspace_metadata_is_frozen_before_request_execution() {
    for manifest in ["Cargo.toml", "library/Cargo.toml"] {
        let mut command = workspace_metadata_command(Path::new("targo"), Path::new(manifest));
        command.mark_as_executed();
        assert_eq!(command.get_program(), OsStr::new("targo"));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            [
                "metadata",
                "--frozen",
                "--format-version",
                "1",
                "--no-deps",
                "--manifest-path",
                manifest
            ]
            .map(OsStr::new),
        );
    }
}

/// Trust (BOOTSTRAP-JOBSERVER-CUSTODY-1): every GNU option the probe receives
/// names a descriptor open in it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
const ADVERTISED_DESCRIPTORS_OPEN: &str = r#"#!/bin/sh
for value in "${CARGO_MAKEFLAGS-}" "${MAKEFLAGS-}" "${MFLAGS-}"; do
  case "$value" in *--jobserver-auth=*) ;; *) echo "no GNU auth in: [$value]" >&2; exit 3 ;; esac
  auth=${value##*--jobserver-auth=}
  auth=${auth%% *}
  if [ ! -e "/dev/fd/${auth%%,*}" ] || [ ! -e "/dev/fd/${auth##*,}" ]; then
    echo "advertised $auth is not open in the probe" >&2
    exit 4
  fi
done
echo "workspace-metadata probe: open"
"#;

/// Trust (BOOTSTRAP-JOBSERVER-CUSTODY-1): the route the tool-graph tests take.
/// A parent lends its pool through `metadata_scheduler::output`, and the
/// re-entered unit binary captures that numeric pipe at genuine entry, so its
/// process environment advertises descriptors Trust std hands no ordinary
/// child. The Session's `cargo metadata` request must borrow the captured pool
/// instead of inheriting that advertisement.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn workspace_metadata_borrows_the_captured_scheduler() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    const NAME: &str = "core::metadata::tests::workspace_metadata_borrows_the_captured_scheduler";
    const ROLE: &str = "TRUST_BOOTSTRAP_WORKSPACE_METADATA_ROLE";
    if !trust_resource_controller::client::explicit_inheritance_supported() {
        // Stock std hands an ordinary child the inherited numbers themselves,
        // and the scheduler refuses an original transport it cannot forward.
        return;
    }
    let role = std::env::var_os(ROLE);
    if role.as_deref() == Some(OsStr::new("child")) {
        let dir = tempfile::tempdir().unwrap();
        let probe = dir.path().join("cargo");
        std::fs::write(&probe, ADVERTISED_DESCRIPTORS_OPEN).unwrap();
        std::fs::set_permissions(&probe, std::fs::Permissions::from_mode(0o755)).unwrap();
        // Control: an ordinary spawn inherits the captured advertisement
        // without its descriptors, which the probe reports as exit 4.
        let ordinary = Command::new(&probe).output().unwrap();
        assert_eq!(ordinary.status.code(), Some(4), "control: {ordinary:?}");
        let mut metadata =
            super::workspace_metadata_command(&probe, Path::new("Cargo.toml")).allow_failure();
        let output = metadata.run_capture(crate::utils::exec::ExecutionContext::new(0, false));
        assert!(
            output.is_success() && output.stdout().contains("workspace-metadata probe: open"),
            "the workspace metadata request lost the captured pool: {:?} {:?} {:?}",
            output.status(),
            output.stdout_if_present(),
            output.stderr_if_present()
        );
        println!("workspace-metadata child: ok");
        return;
    }
    if role.is_none() {
        // The enclosing build may lend a named FIFO. This control specifically
        // exercises descriptor loss, so construct an isolated EMPTY numeric
        // pool instead of interpreting a FIFO pathname as descriptor numbers.
        // No native admission or scheduling credits enter this synthetic owner.
        let mut owner =
            crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()));
        let output =
            owner.args(["--exact", NAME, "--nocapture"]).env(ROLE, "owner").output().unwrap();
        assert!(
            output.status.success()
                && String::from_utf8_lossy(&output.stdout).contains("workspace-metadata child: ok"),
            "{output:?}"
        );
        return;
    }
    assert_eq!(role.as_deref(), Some(OsStr::new("owner")));
    crate::utils::metadata_scheduler::install_test_original(
        jobserver_utils::Jobserver::new(0).unwrap(),
    )
    .unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap());
    child.args(["--exact", NAME, "--nocapture"]).env(ROLE, "child");
    let output = crate::utils::metadata_scheduler::output(&mut child, true, true).unwrap();
    // Success alone is not a pass: a filter that selects nothing also exits 0.
    assert!(
        output.status.success()
            && String::from_utf8_lossy(&output.stdout).contains("workspace-metadata child: ok"),
        "{output:?}\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    println!("workspace-metadata child: ok");
}

//! Test fixtures that are owner-only whatever the process umask.
//!
//! `tempfile::tempdir`, `fs::create_dir` and `fs::write` ask for 0777 or 0666
//! less the umask: never group or other writable under the usual 022, but group
//! writable under 002, a Linux login default (user private groups). The
//! namespace checks of this crate and of trust-build-cpu refuse a group-writable
//! directory or file: most refuse `mode & 0o022`, and trust-build-cpu's CPU pool
//! directories and files (`unix::check_private`) and this crate's fixed handoff
//! packet refuse any group or other bit (`mode & 0o077`). That refusal is
//! correct, so a fixture states its mode instead of inheriting the runner's
//! umask (TBT-WORKER-EPOCH-LINUX-1). These mirror the std calls they replace.
//! A fixture for a file the legacy launcher makes 0644 uses `crate::launcher_file`.

use std::fs;
use std::io::Write as _;
use std::os::unix::fs::{DirBuilderExt as _, OpenOptionsExt as _, PermissionsExt as _};
use std::path::Path;

/// A temporary root created 0700.
pub(crate) fn tempdir() -> tempfile::TempDir {
    tempfile::Builder::new().permissions(fs::Permissions::from_mode(0o700)).tempdir().unwrap()
}

/// Creates the directory `path`, whose parent exists, 0700.
pub(crate) fn create_dir(path: &Path) {
    fs::DirBuilder::new().mode(0o700).create(path).unwrap();
}

/// Creates `path` and each missing ancestor 0700.
#[cfg(feature = "machine-admission")] // Only admission::status's fixture, under that feature.
pub(crate) fn create_dir_all(path: &Path) {
    fs::DirBuilder::new().recursive(true).mode(0o700).create(path).unwrap();
}

/// Writes `bytes` to `path`, truncating it, or creating it 0600.
pub(crate) fn write(path: &Path, bytes: &[u8]) {
    fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(path)
        .unwrap()
        .write_all(bytes)
        .unwrap();
}

/// Runs `body` alone in a fresh process of this test binary
/// (`trust_output_lock::tests::isolated_case`) whose umask is 002, so a fixture
/// is checked under the mask that makes a std-created directory 0775. `test`
/// is the calling test's full path.
pub(crate) fn under_umask_002(test: &str, body: impl FnOnce()) {
    crate::trust_output_lock::tests::isolated_case(test, || {
        // SAFETY: umask(2) only replaces this process's file creation mask, and
        // this process runs this one test and nothing else.
        unsafe { libc::umask(0o002) };
        let probe = tempdir();
        let plain = probe.path().join("std-create-dir");
        fs::create_dir(&plain).unwrap();
        assert_eq!(
            fs::symlink_metadata(&plain).unwrap().permissions().mode() & 0o777,
            0o775,
            "a std-created directory is group writable under the child's umask"
        );
        drop(probe);
        body();
    });
}

/// Runs each of `tests`, existing tests named by full path, alone in its own
/// process of this test binary, from inside the umask-002 process of the
/// calling test `test` (`under_umask_002`), so each inherits that umask. This
/// is for tests that isolate themselves through `isolated_case`: it requires
/// the calling thread to bear the test's own name, so another test cannot
/// call one directly.
#[cfg(feature = "machine-admission")] // Only admission::resources::adoption's tests.
pub(crate) fn existing_tests_under_umask_002(test: &str, tests: &[&str]) {
    under_umask_002(test, || {
        for &name in tests {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", name, "--test-threads=1"])
                .stdin(std::process::Stdio::null())
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let report = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
            assert!(output.status.success(), "{name}, under umask 002, failed:\n{report}");
            assert!(
                stdout.contains("test result: ok. 1 passed;"),
                "{name} did not run alone:\n{report}"
            );
        }
    });
}

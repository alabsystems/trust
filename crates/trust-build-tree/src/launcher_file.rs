//! Test fixtures for the files the legacy launcher, scripts/build-slot, makes in
//! its namespace: `slot-N`, `admission.lock`, a worktree lease and the CPU fence.
//! It opens each with `os.open(path, flags, 0o644)`, so each is 0644 less its
//! umask: 0644 under the usual 022 and under 002, readable by group and other
//! but writable by neither. The namespace checks accept such a file because they
//! refuse only `mode & 0o022`, and a test must keep seeing that the real
//! launcher's files are accepted, so a fixture for one is exactly 0644 whatever
//! the runner's umask. The launcher makes its queue tickets, registry locks and
//! adoption records 0600; fixtures for those use `crate::owner_only`.
//!
//! git makes `<git-dir>`, the worktree lease's parent, 0777 less the umask, and
//! an older launcher made its namespace with `os.makedirs(DIR, exist_ok=True)`,
//! the same: 0755 under the usual umask 022 and 0775 under 002. The current
//! launcher makes each missing component of its namespace 0700 whatever the
//! umask and never changes an existing directory, so a namespace an older one
//! made is still 0755 or 0775. The namespace checks admit 0755 and refuse a
//! group-writable directory by name, so a fixture for `<git-dir>` or for such a
//! namespace is exactly 0755 whatever the runner's umask.

use std::fs;
use std::io::Write as _;
use std::os::unix::fs::{DirBuilderExt as _, OpenOptionsExt as _, PermissionsExt as _};
use std::path::Path;

/// Creates the directory `path`, whose parent exists, with mode exactly 0755.
/// It is made 0700 and then given 0755 (chmod), which no umask reduces.
pub(crate) fn create_dir(path: &Path) {
    fs::DirBuilder::new().mode(0o700).create(path).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(fs::symlink_metadata(path).unwrap().permissions().mode() & 0o7777, 0o755);
}

/// Writes `bytes` to `path`, truncating it or creating it, with mode exactly
/// 0644. The mode is set on the open file (fchmod), which no umask reduces.
pub(crate) fn write(path: &Path, bytes: &[u8]) {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(path)
        .unwrap();
    file.set_permissions(fs::Permissions::from_mode(0o644)).unwrap();
    assert_eq!(file.metadata().unwrap().permissions().mode() & 0o7777, 0o644);
    file.write_all(bytes).unwrap();
}

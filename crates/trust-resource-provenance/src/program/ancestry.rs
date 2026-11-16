// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The held-directory walk, and a preflight that names where it refuses.
//!
//! Every held input reaches a directory by opening `/` and then each component
//! no-follow beneath the previous description, applying `owned()` to each one.
//! [`check_directory_ancestry`] runs that SAME walk, so a long producer (such as
//! Bootstrap before it builds a compiler whose sysroot it later holds) can refuse
//! a location at its start instead of an hour in. It returns no description: a
//! pass is no custody, snapshot or admission, and does not say that a later
//! capture succeeds (the tree can change, and directories created later are not
//! observed).

use super::*;

/// The first directory, from `/` down, that the held-input rule refuses.
#[derive(Debug)]
pub struct DirectoryRefusal {
    /// The refused directory: `/` or a prefix of the walked path (the whole
    /// path when its syntax is refused).
    pub directory: PathBuf,
    /// Owner of the refused directory's opened description. `None` when the
    /// component itself could not be opened.
    pub uid: Option<u32>,
    /// Full `st_mode` of that description, under the same condition.
    pub mode: Option<u32>,
    /// The error the held capture itself returns for this directory.
    pub error: io::Error,
}

/// Open `path` the way every held capture does and refuse at the first
/// directory `owned()` refuses. `directory()` is this walk minus the report.
pub(super) fn walk(path: &Path, deadline: Instant) -> Result<File, DirectoryRefusal> {
    let refusal = |depth: usize, file: Option<&File>, error: io::Error| {
        let meta = file.and_then(|file| file.metadata().ok());
        DirectoryRefusal {
            directory: path.components().take(depth + 1).collect(),
            uid: meta.as_ref().map(|meta| meta.uid()),
            mode: meta.as_ref().map(|meta| meta.mode()),
            error,
        }
    };
    canonical(path).map_err(|error| DirectoryRefusal {
        directory: path.to_owned(),
        uid: None,
        mode: None,
        error,
    })?;
    time(deadline).map_err(|error| refusal(0, None, error))?;
    let mut dir =
        openat(libc::AT_FDCWD, OsStr::new("/"), true).map_err(|error| refusal(0, None, error))?;
    owned(&dir, true, false).map_err(|error| refusal(0, Some(&dir), error))?;
    for (depth, part) in path.components().enumerate() {
        if let Component::Normal(name) = part {
            time(deadline).map_err(|error| refusal(depth, None, error))?;
            dir =
                openat(dir.as_raw_fd(), name, true).map_err(|error| refusal(depth, None, error))?;
            owned(&dir, true, false).map_err(|error| refusal(depth, Some(&dir), error))?;
        }
    }
    Ok(dir)
}

/// Apply the held-directory rule to `/` and every directory down to and
/// including `path`, which must be canonical absolute syntax naming an existing
/// directory. Preflight only: see the module documentation.
pub fn check_directory_ancestry(path: &Path, deadline: Instant) -> Result<(), DirectoryRefusal> {
    walk(path, deadline).map(drop)
}

#[cfg(test)]
mod tests;

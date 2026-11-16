// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Mutable directory identity/parent custody only. This is neither complete
//! namespace contents, writer exclusion, a source/SDK root nor write authority.
//! The actual resource owner separately selects permissions and retains the
//! SAME description through the real operation, including failed retirement.

use super::*;
use std::os::fd::{AsFd as _, BorrowedFd};
use std::sync::atomic::{AtomicBool, Ordering};

pub struct HeldDirectoryInput {
    path: PathBuf,
    directories: BTreeMap<PathBuf, HeldDirectory>,
    invalid: AtomicBool,
}
impl HeldDirectoryInput {
    /// Negative physical ancestry DATA from this actual original directory.
    /// Consumers may veto an ancestor alias; these identities grant no access.
    pub fn original_tree_identities(&self, deadline: Instant) -> io::Result<Vec<(u64, u64)>> {
        self.validate(deadline)?;
        Ok(self
            .directories
            .values()
            .map(|held| (held.before.dev(), held.before.ino()))
            .collect())
    }
    /// Actual retained identity DATA. It grants no write or resource rights.
    pub fn original_identity(&self, deadline: Instant) -> io::Result<(u64, u64)> {
        self.validate(deadline)?;
        let held = self
            .directories
            .get(&self.path)
            .ok_or_else(|| refused("original directory absent"))?;
        Ok((held.before.dev(), held.before.ino()))
    }
    /// Conservative native capture demand only. Reserve before opening and
    /// retain the actual held population until its descriptors close.
    pub fn capture_descriptor_bound() -> usize {
        MAX_COMPONENTS + 3
    }
    pub fn descriptor_count(&self) -> usize {
        self.directories.len()
    }
    pub fn path(&self) -> &Path {
        &self.path
    }
    /// Capture actual no-follow originals. The caller must admit descriptor
    /// capacity first; this method neither raises limits nor grants resources.
    pub fn open(path: &Path, deadline: Instant) -> io::Result<Self> {
        canonical(path)?;
        time(deadline)?;
        let mut directories = BTreeMap::new();
        for ancestor in path.ancestors().collect::<Vec<_>>().into_iter().rev() {
            let file = directory(ancestor, deadline)?;
            let before = owned(&file, true, false)?;
            directories.insert(
                ancestor.into(),
                HeldDirectory {
                    file,
                    before,
                    selected: false,
                },
            );
        }
        let result = Self {
            path: path.into(),
            directories,
            invalid: AtomicBool::new(false),
        };
        result.validate(deadline)?;
        Ok(result)
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original directory input has an earlier failed bookend",
            ));
        }
        let result = (|| {
            time(deadline)?;
            for (path, held) in &self.directories {
                let named = directory(path, deadline)?;
                for file in [&held.file, &named] {
                    if !same_directory(&held.before, &owned(file, true, false)?, false) {
                        return Err(refused(
                            "original directory input or ancestor was substituted",
                        ));
                    }
                }
            }
            time(deadline)
        })();
        // A retained identity is not the capture operation's permission.
        // Current timeout withholds THIS call; structural drift stays sticky.
        if result.as_ref().is_err_and(|error|error.kind()!=io::ErrorKind::TimedOut) {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original directory input failed a concurrent bookend",
            ));
        }
        result
    }
    /// Actual original directory description, not an authority reconstructed
    /// from its pathname. Admission and operation permissions remain separate.
    pub fn descriptor(&self, deadline: Instant) -> io::Result<BorrowedFd<'_>> {
        self.validate(deadline)?;
        Ok(self
            .directories
            .get(&self.path)
            .ok_or_else(|| refused("original directory absent"))?
            .file
            .as_fd())
    }
}

#[cfg(test)]
mod tests;

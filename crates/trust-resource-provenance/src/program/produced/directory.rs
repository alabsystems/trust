// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Mutable directory originals below the SAME actual output-root description.
//! Contents, writer exclusion, output eligibility and execution admission are
//! separate. No pathname, saved namespace or digest constructs this owner.
use std::os::fd::{AsFd as _, BorrowedFd};
use std::sync::atomic::{AtomicBool, Ordering};

use super::*;

pub struct HeldRootDirectory {
    output: Arc<OutputBacking>,
    directories: BTreeMap<PathBuf, HeldDirectory>,
    selected: PathBuf,
    invalid: AtomicBool,
}
impl HeldRootDirectory {
    pub fn require_disjoint_trees(
        &self,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<()> {
        self.validate(deadline)?;
        super::publication::require_disjoint_trees(
            self.descriptor(deadline)?.as_raw_fd(),
            exclusions,
            deadline,
        )?;
        self.validate(deadline)
    }
    /// Identity relation between two live originals, never a write grant.
    pub fn belongs_to_root(&self, root: &HeldOutputRoot) -> bool {
        Arc::ptr_eq(&self.output, &root.backing)
    }
    /// Conservative preparation demand only; reserve before mkdir/open.
    pub fn capture_descriptor_bound() -> usize {
        MAX_COMPONENTS + 3
    }
    /// Newly held descriptions only. The original output backing is shared.
    pub fn descriptor_count(&self) -> usize {
        self.directories.len()
    }
    pub fn path(&self) -> &Path {
        &self.selected
    }
    pub fn output_root(&self) -> &Path {
        &self.output.path
    }
    fn parent(&self, path: &Path) -> io::Result<i32> {
        let parent = path
            .parent()
            .ok_or_else(|| refused("selected directory parent absent"))?;
        if parent == self.output.path {
            Ok(self.output.file.as_raw_fd())
        } else {
            Ok(self
                .directories
                .get(parent)
                .ok_or_else(|| refused("unheld output directory ancestor"))?
                .file
                .as_raw_fd())
        }
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original output directory has an earlier failed bookend",
            ));
        }
        // This is current identity custody, not the earlier operation's grant.
        // Each caller still supplies its current admitted deadline. A timeout
        // returns Err for THAT operation; structural drift remains sticky.
        let result = (|| {
            self.output.validate(deadline)?;
            for (path, held) in &self.directories {
                time(deadline)?;
                let current = openat(
                    self.parent(path)?,
                    path.file_name()
                        .ok_or_else(|| refused("selected directory name absent"))?,
                    true,
                )?;
                for original in [&held.file, &current] {
                    if !same_directory(&held.before, &owned(original, true, false)?, false) {
                        return Err(refused(
                            "original selected output directory or parent changed",
                        ));
                    }
                }
            }
            self.output.validate(deadline)?;
            time(deadline)
        })();
        if result
            .as_ref()
            .is_err_and(|error| error.kind() != io::ErrorKind::TimedOut)
        {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original output directory failed a concurrent bookend",
            ));
        }
        result
    }
    /// Borrow one actual original; this grants no writes or resource authority.
    pub fn descriptor(&self, deadline: Instant) -> io::Result<BorrowedFd<'_>> {
        self.validate(deadline)?;
        Ok(self
            .directories
            .get(&self.selected)
            .ok_or_else(|| refused("original selected output directory absent"))?
            .file
            .as_fd())
    }
}
fn mkdir(parent: i32, name: &OsStr) -> io::Result<()> {
    let name = std::ffi::CString::new(name.as_bytes())
        .map_err(|_| refused("output directory name contains NUL"))?;
    // SAFETY: actual original directory FD, one bounded no-slash component and
    // a live NUL-terminated name. Never resolve a projected absolute pathname.
    if unsafe { libc::mkdirat(parent, name.as_ptr(), 0o700) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}
impl HeldOutputRoot {
    /// Capture an existing mutable child namespace through original root FDs.
    /// Native capacity must be admitted before this call. The caller retains
    /// the original root/admission and independently selects any write policy.
    pub fn directory(&self, path: &Path, deadline: Instant) -> io::Result<HeldRootDirectory> {
        self.root_directory(path, false, &PublicationExclusions::default(), deadline)
    }
    /// Retain a transferred original selected directory, independently bound
    /// to the SAME held root and no-follow ancestor chain. This supplies no
    /// writer/producer/resource authority. Admit receive/capture capacity first.
    pub fn directory_from_original(
        &self,
        path: &Path,
        original: File,
        deadline: Instant,
    ) -> io::Result<HeldRootDirectory> {
        let mut held =
            self.root_directory(path, false, &PublicationExclusions::default(), deadline)?;
        // SAFETY: observe access flags on the actual held incoming original.
        let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) };
        // SAFETY: read descriptor flags from the same owned incoming original.
        let descriptor_flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFD) };
        let named = held
            .directories
            .get_mut(path)
            .ok_or_else(|| refused("received selected directory missing"))?;
        if flags < 0
            || descriptor_flags < 0
            || descriptor_flags & libc::FD_CLOEXEC == 0
            || flags & libc::O_ACCMODE != libc::O_RDONLY
            || !same_directory(&named.before, &owned(&original, true, false)?, false)
        {
            return Err(refused(
                "received directory differs from its held-root name or read-only access",
            ));
        }
        named.file = original;
        held.validate(deadline)?;
        Ok(held)
    }
    /// Parent-only preparation: create a NEW final namespace using mkdirat
    /// below the SAME original root. Existing intermediate directories are
    /// opened no-follow; an existing final directory always refuses. Partial
    /// failure leaves created namespace/evidence intact and grants no owner.
    /// Capacity must precede every mkdir/open, including bounded scratch.
    pub fn prepare_directory(
        &self,
        path: &Path,
        deadline: Instant,
    ) -> io::Result<HeldRootDirectory> {
        self.root_directory(path, true, &PublicationExclusions::default(), deadline)
    }
    pub fn prepare_directory_excluding(
        &self,
        path: &Path,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<HeldRootDirectory> {
        self.root_directory(path, true, exclusions, deadline)
    }
    fn root_directory(
        &self,
        path: &Path,
        create: bool,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<HeldRootDirectory> {
        self.validate(deadline)?;
        canonical(path)?;
        let relative = path
            .strip_prefix(self.path())
            .map_err(|_| refused("selected output directory escapes its original root"))?;
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|part| !matches!(part, Component::Normal(_)))
        {
            return Err(refused(
                "selected output directory is not a canonical child",
            ));
        }
        let mut directories = BTreeMap::<PathBuf, HeldDirectory>::new();
        let mut current = self.path().to_owned();
        for component in relative.components() {
            time(deadline)?;
            let Component::Normal(name) = component else {
                return Err(refused("noncanonical output directory"));
            };
            let parent = if current == self.path() {
                self.backing.file.as_raw_fd()
            } else {
                directories
                    .get(&current)
                    .ok_or_else(|| refused("unheld output directory ancestor"))?
                    .file
                    .as_raw_fd()
            };
            current.push(name);
            let file = if create && current == path {
                super::publication::require_disjoint_trees(parent, exclusions, deadline)?;
                exclusions.check_directory(parent)?;
                mkdir(parent, name)?;
                openat(parent, name, true)?
            } else {
                match openat(parent, name, true) {
                    Ok(file) => file,
                    Err(error) if create && error.kind() == io::ErrorKind::NotFound => {
                        // EEXIST after the failed lookup is a race/refusal,
                        // never permission to reuse somebody else's capture.
                        super::publication::require_disjoint_trees(parent, exclusions, deadline)?;
                        exclusions.check_directory(parent)?;
                        mkdir(parent, name)?;
                        openat(parent, name, true)?
                    }
                    Err(error) => return Err(error),
                }
            };
            let before = owned(&file, true, false)?;
            directories.insert(
                current.clone(),
                HeldDirectory {
                    file,
                    before,
                    selected: false,
                },
            );
        }
        let result = HeldRootDirectory {
            output: Arc::clone(&self.backing),
            directories,
            selected: path.to_owned(),
            invalid: AtomicBool::new(false),
        };
        result.validate(deadline)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests;

// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original selected output DATA, not compiler-success or dependency authority.
//! The caller selects the real Unit OutputFile and positively closes its actual
//! producer before capture. Root membership, bytes and hashes establish none of
//! those prerequisites. Consumers must separately exclude writers and retain
//! this SAME owner through their actual retirement, including failed outcomes.

use super::*;
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use sha2::Digest as _;
use sha2::Sha256;
use std::os::fd::{AsFd as _, BorrowedFd};
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use std::os::unix::fs::FileExt as _;
use std::sync::atomic::{AtomicBool, Ordering};

const MAX_BYTES: u64 = 8 * 1024 * 1024 * 1024;

/// Read-only original file and descriptor-relative parent custody below the
/// SAME held output root. No public constructor accepts saved observations,
/// status, digest or a replacement root. Zero bytes are valid DATA only: this
/// neither validates Rust metadata nor turns an empty executable into a program.
pub struct HeldRootFile {
    pub(super) output: Arc<OutputBacking>,
    pub(super) parents: BTreeMap<PathBuf, HeldDirectory>,
    pub(super) input: HeldFile,
    pub(super) invalid: AtomicBool,
}
impl HeldRootFile {
    /// Conservative owned metadata demand only. Shared original output-root
    /// custody is not recounted. This performs no IO or admission transition.
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.input.observation.path.capacity())?
            .checked_add(self.input.observation.sha256.capacity())?;
        for path in self.parents.keys() {
            // The linked alloc B-tree uses eleven slots per node (B=6).
            // Charge a whole node per filled entry, including the sparsest
            // one-entry root, rather than pretending unused slots are free.
            bytes = bytes
                .checked_add(
                    std::mem::size_of::<(PathBuf, HeldDirectory)>()
                        .checked_mul(11)?
                        .checked_add(128)?,
                )?
                .checked_add(path.capacity())?;
        }
        Some(bytes)
    }
    /// Identity relation between two live originals, never path authority.
    pub fn belongs_to_root(&self, root: &HeldOutputRoot) -> bool {
        Arc::ptr_eq(&self.output, &root.backing)
    }
    /// Demand bound, never a capacity grant. Admit it before opening any
    /// capture descriptions: at most one per canonical component, one file and
    /// bounded validation scratch. The caller can account the smaller actual
    /// held population after successful capture, without releasing originals.
    pub fn capture_descriptor_bound() -> usize {
        MAX_COMPONENTS + 3
    }
    pub fn descriptor_count(&self) -> usize {
        self.parents.len() + 1
    }
    pub fn observation(&self) -> &FileObservation {
        &self.input.observation
    }
    pub fn output_root(&self) -> &Path {
        &self.output.path
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original selected output has an earlier failed bookend",
            ));
        }
        // This is current identity custody, not the earlier operation's grant.
        // Each caller still supplies its current admitted deadline. A timeout
        // returns Err for THAT operation; structural drift remains sticky.
        let result = self.validate_inner(deadline);
        if result
            .as_ref()
            .is_err_and(|error| error.kind() != io::ErrorKind::TimedOut)
        {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused(
                "original selected output failed a concurrent bookend",
            ));
        }
        result
    }
    fn validate_inner(&self, deadline: Instant) -> io::Result<()> {
        self.output.validate(deadline)?;
        for (path, held) in &self.parents {
            time(deadline)?;
            let named = openat(
                self.parent(path)?,
                path.file_name()
                    .ok_or_else(|| refused("output parent has no name"))?,
                true,
            )?;
            // Output directories remain mutable namespaces. Bind original
            // identities/modes, not unrelated new outputs or their timestamps.
            for file in [&held.file, &named] {
                if !same_directory(&held.before, &owned(file, true, false)?, false) {
                    return Err(refused("selected output parent was substituted"));
                }
            }
        }
        let path = &self.input.observation.path;
        let named = openat(
            self.parent(path)?,
            path.file_name()
                .ok_or_else(|| refused("selected output has no name"))?,
            false,
        )?;
        for file in [&self.input.file, &named] {
            if stamp(&owned(file, false, false)?) != stamp(&self.input.before) {
                return Err(refused("original selected output bytes or backing changed"));
            }
        }
        self.output.validate(deadline)?;
        time(deadline)
    }
    fn parent(&self, path: &Path) -> io::Result<i32> {
        let parent = path
            .parent()
            .ok_or_else(|| refused("selected output parent absent"))?;
        if parent == self.output.path {
            Ok(self.output.file.as_raw_fd())
        } else {
            Ok(self
                .parents
                .get(parent)
                .ok_or_else(|| refused("unheld output ancestor"))?
                .file
                .as_raw_fd())
        }
    }
    /// Borrow the actual retained original after a fresh bookend. The caller
    /// must admit any copies before making them and retain this owner through
    /// use; an FD transfer supplies no producer, CPU, SDK or proof authority.
    pub fn descriptor(&self, deadline: Instant) -> io::Result<BorrowedFd<'_>> {
        self.validate(deadline)?;
        Ok(self.input.file.as_fd())
    }
}
impl HeldOutputRoot {
    /// Capture the caller's actual selected Unit output after its real producer
    /// has retired. This only owns current original data. The parent graph must
    /// bind the typed Unit/output selection and actual producer independently;
    /// no status/manifest/path can authorize later execution or dependency use.
    /// Native descriptor admission MUST precede this call and outlive its result.
    pub fn file(&self, path: &Path, deadline: Instant) -> io::Result<HeldRootFile> {
        self.file_inner(path, None, deadline)
    }
    /// Receive the SAME actual read-only original across a native descriptor
    /// transfer. The held root and no-follow traversal independently bind its
    /// current name/backing; saved observations never reconstruct this owner.
    /// Native capacity must cover the incoming FD before receive and this
    /// capture envelope before opening any additional description.
    pub fn file_from_original(
        &self,
        path: &Path,
        original: File,
        deadline: Instant,
    ) -> io::Result<HeldRootFile> {
        self.file_inner(path, Some(original), deadline)
    }
    fn file_inner(
        &self,
        path: &Path,
        original: Option<File>,
        deadline: Instant,
    ) -> io::Result<HeldRootFile> {
        self.validate(deadline)?;
        canonical(path)?;
        let relative = path
            .strip_prefix(self.path())
            .map_err(|_| refused("selected output escapes its original root"))?;
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|part| !matches!(part, Component::Normal(_)))
        {
            return Err(refused("selected output is not a canonical child file"));
        }
        let mut parents = BTreeMap::<PathBuf, HeldDirectory>::new();
        let mut current = self.path().to_owned();
        let parent_path = path
            .parent()
            .ok_or_else(|| refused("selected output has no parent"))?;
        for component in relative.parent().into_iter().flat_map(Path::components) {
            time(deadline)?;
            let Component::Normal(name) = component else {
                return Err(refused("noncanonical output parent"));
            };
            let parent = if current == self.path() {
                self.backing.file.as_raw_fd()
            } else {
                parents
                    .get(&current)
                    .ok_or_else(|| refused("unheld output parent"))?
                    .file
                    .as_raw_fd()
            };
            let file = openat(parent, name, true)?;
            let before = owned(&file, true, false)?;
            current.push(name);
            parents.insert(
                current.clone(),
                HeldDirectory {
                    file,
                    before,
                    selected: false,
                },
            );
        }
        if current != parent_path {
            return Err(refused(
                "selected output traversal did not reach its original parent",
            ));
        }
        let parent = if current == self.path() {
            &self.backing.file
        } else {
            &parents
                .get(&current)
                .ok_or_else(|| refused("unheld output parent"))?
                .file
        };
        if super::super::target_sysroot::directory_entry(parent, path.file_name().unwrap())? {
            return Err(refused("selected output data is a directory"));
        }
        let named = openat(parent.as_raw_fd(), path.file_name().unwrap(), false)?;
        let file = if let Some(file) = original {
            // SAFETY: read access flags only on this held original FD.
            let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
            // SAFETY: descriptor flags are observed on the same owned original.
            let descriptor_flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
            if flags < 0
                || descriptor_flags < 0
                || descriptor_flags & libc::FD_CLOEXEC == 0
                || flags & libc::O_ACCMODE != libc::O_RDONLY
                || stamp(&owned(&file, false, false)?) != stamp(&owned(&named, false, false)?)
            {
                return Err(refused(
                    "received output original differs from its held-root name or read-only access",
                ));
            }
            file
        } else {
            named
        };
        let before = owned(&file, false, false)?;
        if before.len() > MAX_BYTES {
            return Err(refused(
                "selected output data exceeds the native byte bound",
            ));
        }
        let mut hash = Sha256::new();
        let mut offset = 0u64;
        let mut buffer = [0u8; 65536];
        while offset < before.len() {
            time(deadline)?;
            let wanted = (before.len() - offset).min(buffer.len() as u64) as usize;
            let count = file.read_at(&mut buffer[..wanted], offset)?;
            if count == 0 {
                return Err(refused("selected output shortened during capture"));
            }
            hash.update(&buffer[..count]);
            offset += count as u64;
        }
        if file.read_at(&mut buffer[..1], offset)? != 0
            || stamp(&file.metadata()?) != stamp(&before)
        {
            return Err(refused("selected output changed during capture"));
        }
        let observation = FileObservation {
            path: path.to_owned(),
            sha256: crate::schema::hex(&hash.finalize()),
            bytes: before.len(),
            device: before.dev(),
            inode: before.ino(),
        };
        let result = HeldRootFile {
            output: Arc::clone(&self.backing),
            parents,
            input: HeldFile {
                file,
                before,
                observation,
            },
            invalid: AtomicBool::new(false),
        };
        result.validate(deadline)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests;

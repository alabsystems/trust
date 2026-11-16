// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Consuming, nonbuffering physical file offers under the SAME selected root.
//! No filename, size or descriptor supplies committed membership, an archive
//! role, source writer exclusion, Seed, SDK, dispatch or native closure.
use std::os::fd::AsFd as _;

use super::*;

const MAX_OFFER_BYTES: u64 = 32 * 1024 * 1024 * 1024;

/// Retains the SAME complete read-set and its actual readonly leaf. This is
/// not Clone and has no path/row/descriptor constructor. A native recipient
/// must keep this whole offer beside any explicit close-only FD copies until
/// actual settlement. Borrowing the file cannot transfer its source meaning.
#[must_use = "retain the complete original offer through all actual file users"]
pub struct HeldSourceFileOffer {
    reads: HeldSourceReadSet,
    path: PathBuf,
    file: File,
    stamp: Stamp,
    flags: i32,
    local_flags: i32,
}

/// A failed consuming capture keeps its SAME quarantined read-set and any
/// pending file. The caller can retain the refusal beside its semantic owner;
/// no failure reconstructs a fresh reader or releases native obligations.
#[must_use = "retain failed originals beside their actual operation owner"]
pub struct RefusedSourceFileOffer {
    error: io::Error,
    reads: HeldSourceReadSet,
    pending: Option<File>,
}
impl RefusedSourceFileOffer {
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    pub fn original_deadline(&self) -> Instant {
        self.reads.original_deadline()
    }
    /// Conservative retained population DATA, never descriptor admission.
    pub fn descriptor_population(&self) -> usize {
        self.reads.selected_population() + usize::from(self.pending.is_some())
    }
}

fn flags(file: &File) -> io::Result<(i32, i32)> {
    // Observe only the retained original; never mutate flags or its cursor.
    let status = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
    if status < 0 || local < 0 {
        return Err(io::Error::last_os_error());
    }
    if status & libc::O_ACCMODE != libc::O_RDONLY || local & libc::FD_CLOEXEC == 0 {
        return Err(invalid("selected file offer is not readonly and close-on-exec"));
    }
    Ok((status, local))
}

impl HeldSourceReadSet {
    /// Conservative total held population plus two validation scratch FDs.
    /// Existing parents may be counted twice. This grants no resource capacity.
    pub fn file_offer_descriptor_bound(&self, relative: &Path) -> io::Result<usize> {
        selected_path(relative)?;
        self.selected_population()
            .checked_add(relative.components().count())
            .and_then(|total| total.checked_add(2))
            .filter(|total| *total <= MAX_DESCRIPTORS + 2)
            .ok_or_else(|| invalid("selected file offer descriptor demand exceeds bound"))
    }
    /// Capture a readonly file without allocating or reading its payload.
    /// Consumes this SAME physical read-set, retaining every earlier leaf,
    /// listing, root and ancestor. `maximum_bytes` only narrows the32GiB hard
    /// bound; reserve descriptor capacity before calling. Source/semantic
    /// owners remain the caller's separate responsibility.
    ///
    /// # Errors
    /// Any existing bookend, relative syntax, bound, nofollow open, protection,
    /// identity, creator or original endpoint failure permanently quarantines
    /// and returns the same read-set plus any pending actual file.
    pub fn into_readonly_file_offer(
        mut self,
        original_root: BorrowedFd<'_>,
        relative: &Path,
        maximum_bytes: u64,
    ) -> Result<HeldSourceFileOffer, RefusedSourceFileOffer> {
        let mut pending = None;
        let captured = (|| {
            selected_path(relative)?;
            self.check_current(original_root)?;
            if maximum_bytes == 0 || maximum_bytes > MAX_OFFER_BYTES {
                return Err(invalid("selected file offer exceeds its finite profile"));
            }
            self.room(1)?;
            let parent = self.parent(original_root, relative, 1)?;
            pending = Some(open(parent, relative.file_name().unwrap(), false)?);
            let file = pending.as_ref().expect("same pending actual file");
            let stamp = protected(file, false)?;
            if stamp.size > maximum_bytes {
                return Err(invalid("selected file offer exceeds its requested byte bound"));
            }
            let (flags, local_flags) = flags(file)?;
            self.check_current(original_root)?;
            Ok((stamp, flags, local_flags))
        })();
        let (stamp, flags, local_flags) = match captured {
            Ok(captured) => captured,
            Err(error) => {
                self.revoked.store(true, Ordering::Release);
                return Err(RefusedSourceFileOffer { error, reads: self, pending });
            }
        };
        let offer = HeldSourceFileOffer {
            reads: self,
            path: relative.to_path_buf(),
            file: pending.take().expect("same actual file"),
            stamp,
            flags,
            local_flags,
        };
        if let Err(error) = offer.check_current() {
            let HeldSourceFileOffer { reads, file, .. } = offer;
            return Err(RefusedSourceFileOffer { error, reads, pending: Some(file) });
        }
        Ok(offer)
    }
}

impl HeldSourceFileOffer {
    pub fn original_deadline(&self) -> Instant {
        self.reads.original_deadline()
    }

    /// Immutable DATA from the accepted traversal; currentness still requires
    /// its original guards. No caller can substitute a different path.
    pub fn relative(&self) -> &Path {
        &self.path
    }

    /// Conservative held population DATA, excluding two validation scratch FDs.
    pub fn descriptor_population(&self) -> usize {
        self.reads.selected_population() + 1
    }

    /// Bounded original size DATA only; this authenticates no archive/hash.
    pub fn bytes(&self) -> io::Result<u64> {
        self.check_current()?;
        Ok(self.stamp.size)
    }

    /// Borrow only the SAME actual readonly file while this complete offer
    /// stays alive. Use positional reads and close-only native copies; retain
    /// this owner with those copies. No OwnedFd/source-owner conversion exists.
    pub fn descriptor(&self) -> io::Result<BorrowedFd<'_>> {
        self.check_current()?;
        Ok(self.file.as_fd())
    }

    /// Recheck the SAME creator/end, all earlier physical inputs, protected
    /// ancestors, original leaf and its current name. Restoring bytes/names
    /// after a failure never revives the consumed read-set or this offer.
    pub fn check_current(&self) -> io::Result<()> {
        let current = (|| {
            self.reads.check_current(self.reads.root.as_fd())?;
            let parent = self.path.parent().unwrap();
            let parent = if parent.as_os_str().is_empty() {
                self.reads.root.as_fd()
            } else {
                self.reads.directories[parent].file.as_fd()
            };
            let named = open(parent, self.path.file_name().unwrap(), false)?;
            if protected(&self.file, false)? != self.stamp
                || protected(&named, false)? != self.stamp
                || flags(&self.file)? != (self.flags, self.local_flags)
            {
                return Err(invalid("selected readonly file offer changed"));
            }
            // This validation copy is not an original owner. Closing it here
            // keeps the final whole-read-set bookend within the advertised
            // two scratch FDs (root copy plus a named ancestor).
            drop(named);
            self.reads.check_current(self.reads.root.as_fd())
        })();
        if current.is_err() {
            self.reads.revoked.store(true, Ordering::Release);
        }
        current
    }
}

#[cfg(test)]
mod tests;

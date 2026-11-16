//! Selected source custody from the SAME actual retained Manager root.
//! A borrowed directory is an input, never launch or release authority.

use std::fs::{File, Metadata};
use std::io;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd};
use std::os::unix::fs::FileExt;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use super::{Inner, ProtectedWorkScope, ScopeDispatch, ScopeIdentity};
use crate::trust_repo_lock::management::{HOLDER, RECORD_LIMIT};

/// Non-Clone source owner minted only from the actual original scope. It
/// retains the SAME Manager directory, without reopening or cloning its File.
/// No path, descriptor, observation or deserializer constructs this owner.
pub struct OriginalSourceRoot {
    inner: Arc<Inner>,
}

impl OriginalSourceRoot {
    /// The SAME protected scope's original endpoint DATA. Readers may only
    /// restrict it; a clock observation creates no work or release authority.
    pub fn deadline(&self) -> Instant {
        self.inner.deadline
    }

    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }

    pub fn path(&self) -> &Path {
        &self.inner.original.original.manager.root.physical
    }

    pub fn check_current(&self) -> io::Result<()> {
        let result = (|| {
            // Reject an already changed source namespace before entering the
            // Manager's original holder transaction. Never select a new root.
            self.inner.original.original.manager.root.check_current().map_err(io::Error::other)?;
            ScopeDispatch { inner: Arc::clone(&self.inner) }.check_current()
        })();
        result.inspect_err(|error| self.inner.fail(error.to_string()))
    }

    /// Borrow only the original readonly directory. The enclosing graph must
    /// retain this owner and recheck after actual reads; this grants no work,
    /// namespace mutation, Manager release or foreign closure capability.
    pub fn directory(&self) -> io::Result<BorrowedFd<'_>> {
        self.check_current()?;
        Ok(self.inner.original.original.manager.root.file.as_fd())
    }

    /// Observe the SAME original directory description without reopening or cloning it.
    /// A graph may retain this clock as an additional input restriction, never as authority.
    pub fn metadata(&self) -> io::Result<std::fs::Metadata> {
        self.check_current()?;
        let observed = self.inner.original.original.manager.root.file.metadata()?;
        self.check_current()?;
        Ok(observed)
    }

    /// Retain close-only copies of the four actual original descriptions.
    /// No path is opened here, and neither the copies nor their observations
    /// confer Manager, release, execution or foreign-scope authority.
    pub fn close_only_offer(&self) -> io::Result<OriginalSourceOffer> {
        self.check_current()?;
        let result = (|| {
            let original = &self.inner.original;
            let files = [
                original.original.manager.root.file.try_clone()?,
                original.original.held.directory.try_clone()?,
                original.original.held.file.try_clone()?,
                original.held.file.try_clone()?,
            ];
            let metadata = description_metadata(&files)?;
            let data = SourceOfferData {
                metadata,
                original_record: record_bytes(&files[2])?,
                withheld_record: record_bytes(&files[3])?,
            };
            let offer = OriginalSourceOffer { inner: Arc::clone(&self.inner), files, data };
            offer.check_current()?;
            Ok(offer)
        })();
        // A failed duplication/read cannot skip the actual final bookend.
        self.check_current()?;
        result
    }
}

/// Non-Clone, non-serializable retention of the SAME original protected scope
/// and four readonly open descriptions. Drop only closes these duplicates.
/// There is deliberately no constructor from paths, descriptors or DATA.
pub struct OriginalSourceOffer {
    inner: Arc<Inner>,
    files: [File; 4],
    data: SourceOfferData,
}

/// Observations only, never source ownership. Record bytes may contain private
/// tokens, so this type deliberately implements neither Debug nor serialization.
pub struct SourceOfferData {
    metadata: [Metadata; 4],
    original_record: Vec<u8>,
    withheld_record: Vec<u8>,
}

impl SourceOfferData {
    /// Fixed order: Manager root, original holder, acquired info, WITHHELD info.
    pub fn description_metadata(&self) -> &[Metadata; 4] {
        &self.metadata
    }

    pub fn holder_leaf(&self) -> &'static str {
        HOLDER
    }

    pub fn original_record(&self) -> &[u8] {
        &self.original_record
    }

    pub fn withheld_record(&self) -> &[u8] {
        &self.withheld_record
    }
}

impl OriginalSourceOffer {
    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }

    /// The actual original deadline, never a caller-supplied extension.
    pub fn deadline(&self) -> Instant {
        self.inner.deadline
    }

    pub fn check_current(&self) -> io::Result<()> {
        let source = OriginalSourceRoot { inner: Arc::clone(&self.inner) };
        source.check_current()?;
        let result = (|| {
            let metadata = description_metadata(&self.files)?;
            let originals = &self.inner.original;
            let actual = [
                originals.original.manager.root.file.metadata()?,
                originals.original.held.directory.metadata()?,
                originals.original.held.file.metadata()?,
                originals.held.file.metadata()?,
            ];
            for (offered, original) in metadata.iter().zip(&actual) {
                if !crate::trust_repo_lock::same_inode(offered, Some(original)) {
                    return Err(io::Error::other("source offer description is not the original"));
                }
            }
            if record_bytes(&self.files[2])? != self.data.original_record
                || record_bytes(&self.files[3])? != self.data.withheld_record
            {
                return Err(io::Error::other("source offer record changed"));
            }
            Ok(())
        })();
        source.check_current()?;
        result.inspect_err(|error| self.inner.fail(error.to_string()))
    }

    /// Borrow only close-only readonly descriptions while retaining the actual
    /// offer. The callback cannot replace ownership with an FD/path/hash claim.
    /// Successful, failed and unwinding callbacks receive the same final
    /// bookend. Unwind permanently withholds further work in the original scope.
    pub fn with_descriptions<T>(
        &self,
        action: impl FnOnce([BorrowedFd<'_>; 4], &SourceOfferData) -> io::Result<T>,
    ) -> io::Result<T> {
        self.check_current()?;
        let result = catch_unwind(AssertUnwindSafe(|| {
            action(self.files.each_ref().map(AsFd::as_fd), &self.data)
        }));
        let current = self.check_current();
        match result {
            Ok(result) => {
                current?;
                result
            }
            Err(payload) => {
                self.inner.fail("original source offer callback panicked");
                resume_unwind(payload)
            }
        }
    }
}

fn description_metadata(files: &[File; 4]) -> io::Result<[Metadata; 4]> {
    for file in files {
        // F_GETFL observes flags only; no F_SETFL, seek, unlock or reopen.
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::O_ACCMODE != libc::O_RDONLY {
            return Err(io::Error::other("source offer requires readonly original descriptions"));
        }
    }
    let observed =
        [files[0].metadata()?, files[1].metadata()?, files[2].metadata()?, files[3].metadata()?];
    if !observed[0].is_dir()
        || !observed[1].is_dir()
        || !observed[2].is_file()
        || !observed[3].is_file()
    {
        return Err(io::Error::other("source offer original description types changed"));
    }
    Ok(observed)
}

fn record_bytes(file: &File) -> io::Result<Vec<u8>> {
    let len = file.metadata()?.len();
    if len == 0 || len > RECORD_LIMIT {
        return Err(io::Error::other("source offer record exceeds its bounded format"));
    }
    let mut bytes = vec![0; len as usize];
    // Positional reads preserve the original shared OFD's cursor.
    file.read_exact_at(&mut bytes, 0)?;
    if file.metadata()?.len() != len {
        return Err(io::Error::other("source offer record length changed"));
    }
    Ok(bytes)
}

impl ProtectedWorkScope {
    /// Bind a configured source to the real original Manager root before work.
    /// The path checks equality only; it cannot choose a different source owner.
    pub fn original_source(&self, expected: &Path) -> io::Result<OriginalSourceRoot> {
        self.dispatcher().check_current()?;
        self.bind_original_source(expected)
    }

    fn bind_original_source(&self, expected: &Path) -> io::Result<OriginalSourceRoot> {
        self.inner
            .original
            .original
            .manager
            .root
            .check_expected_kind(expected)
            .map_err(|error| self.source_check_error(error))?;
        let original = OriginalSourceRoot { inner: Arc::clone(&self.inner) };
        original.check_current()?;
        Ok(original)
    }

    fn source_check_error(&self, error: crate::trust_repo_lock::ExpectedRootError) -> io::Error {
        use crate::trust_repo_lock::ExpectedRootError;
        match error {
            ExpectedRootError::Current(error) => {
                self.inner.fail(error.clone());
                io::Error::other(error)
            }
            ExpectedRootError::Selection(error) => io::Error::other(error),
        }
    }

    pub fn same_original_directory(&self, opened: &File) -> io::Result<bool> {
        self.check_current()?;
        let original = self.inner.original.original.manager.root.file.metadata()?;
        let offered = opened.metadata()?;
        let same = original.is_dir()
            && offered.is_dir()
            && crate::trust_repo_lock::same_inode(&original, Some(&offered));
        self.check_current()?;
        Ok(same)
    }
}

#[cfg(test)]
mod tests;

#[cfg(feature = "resident-inputs")]
mod retirement;
#[cfg(feature = "resident-inputs")]
pub use retirement::{RefusedInputRetirement, RetiredResidentInputs};

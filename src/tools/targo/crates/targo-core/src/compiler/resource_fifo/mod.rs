//! Private local worker FIFO; its owner retains the namespace through workers.

use std::ffi::CString;
use std::io;
use std::os::fd::{AsFd, BorrowedFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

use anyhow::bail;
use jobserver_utils::Jobserver;

pub(crate) struct PrivateFifo {
    _directory: tempfile::TempDir,
    pub(super) jobserver: Jobserver,
    witnesses: [OwnedFd; 2],
    backing: trust_resource_controller::FileIdentity,
    supplementary: usize,
    escrowed: AtomicBool,
}

/// SAME original GNU tokens and descriptions, never a replacement pool. Once
/// offered to the host, only its positive phase retirement permits their
/// return. Unknown Drop aborts before any Acquired guard can release a byte.
pub(crate) struct ForeignGnuEscrow {
    fifo: Arc<PrivateFifo>,
    tokens: Vec<jobserver::Acquired>,
    offered: bool,
}

impl PrivateFifo {
    pub(crate) fn ceiling(&self) -> u32 {
        self.supplementary as u32 + 1
    }
    pub(super) fn new(ceiling: u32) -> anyhow::Result<Self> {
        Self::in_directory(
            ceiling,
            tempfile::Builder::new().prefix("targo-cpu-").tempdir()?,
        )
    }

    /// Initial-pair roots cannot expose supplementary credits before genuine
    /// replacement funding. Construct and capture the SAME private server in
    /// one operation, before any caller can export it or start workers. These
    /// inert guards are not executable capacity; unknown Drop must not restore
    /// them to a still-partially-funded root.
    pub(crate) fn new_captive(ceiling: u32) -> anyhow::Result<(Arc<Self>, ForeignGnuEscrow)> {
        let fifo = Arc::new(Self::new(ceiling)?);
        let mut escrow = fifo
            .try_escrow()?
            .ok_or_else(|| anyhow::anyhow!("new original GNU credits could not be captured"))?;
        escrow.offered();
        Ok((fifo, escrow))
    }

    fn in_directory(ceiling: u32, directory: tempfile::TempDir) -> anyhow::Result<Self> {
        Self::open(ceiling, directory, true)
    }

    /// Empty transport for supplementary credits backed individually by
    /// actual inherited Acquired guards. This creates no scheduling credits.
    pub(super) fn unseeded(ceiling: u32) -> anyhow::Result<Self> {
        Self::open(
            ceiling,
            tempfile::Builder::new().prefix("targo-gnu-").tempdir()?,
            false,
        )
    }

    fn open(ceiling: u32, directory: tempfile::TempDir, seed: bool) -> anyhow::Result<Self> {
        if ceiling == 0 {
            bail!("native CPU local ceiling is zero");
        }
        let path = directory.path().join("credits");
        let name = CString::new(path.as_os_str().as_bytes())?;
        // SAFETY: this NUL-terminated path is inside our newly created private
        // directory. Only this owner creates and removes its FIFO namespace.
        if unsafe { libc::mkfifo(name.as_ptr(), 0o600) } != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        let jobserver = Jobserver::from_fifo(&path)?;
        // The executing root already owns the implicit token; expose only
        // the extras; the implicit credit is never minted again.
        if seed {
            for _ in 1..ceiling {
                jobserver.client().release_raw()?;
            }
        }
        // Borrow custody from the actual native client, not its advertised
        // pathname or configured numeric descriptor strings. Named FIFOs do
        // not have Jobserver::pipe_descriptors().
        let jobserver::TransportWitnesses::NamedFifo {
            path: observed,
            read,
            write,
        } = jobserver.client().transport_witnesses()?
        else {
            bail!("original private GNU transport is not its named FIFO");
        };
        if observed != path {
            bail!("original private GNU FIFO locator changed");
        }
        let read_meta = std::fs::File::from(read.try_clone()?).metadata()?;
        let write_meta = std::fs::File::from(write.try_clone()?).metadata()?;
        let selected = std::fs::symlink_metadata(&path)?;
        if !read_meta.file_type().is_fifo()
            || !write_meta.file_type().is_fifo()
            || !selected.file_type().is_fifo()
            || (read_meta.dev(), read_meta.ino()) != (write_meta.dev(), write_meta.ino())
            || (read_meta.dev(), read_meta.ino()) != (selected.dev(), selected.ino())
        {
            bail!("original private GNU FIFO witnesses changed");
        }
        Ok(Self {
            _directory: directory,
            jobserver,
            witnesses: [read, write],
            backing: trust_resource_controller::FileIdentity {
                device: read_meta.dev(),
                inode: read_meta.ino(),
            },
            supplementary: ceiling as usize - 1,
            escrowed: AtomicBool::new(false),
        })
    }

    #[cfg(test)]
    pub(crate) fn fixture(ceiling: u32) -> Arc<Self> {
        Arc::new(Self::new(ceiling).unwrap())
    }

    #[cfg(test)]
    pub(crate) fn fixture_in(ceiling: u32, parent: &std::path::Path) -> Arc<Self> {
        Arc::new(Self::in_directory(ceiling, tempfile::tempdir_in(parent).unwrap()).unwrap())
    }

    #[cfg(test)]
    pub(crate) fn fixture_path(&self) -> std::path::PathBuf {
        self._directory.path().join("credits")
    }

    #[cfg(test)]
    pub(crate) fn available(&self) -> usize {
        self.jobserver.client().available().unwrap()
    }

    /// Call only with root dispatch parked and current workers/loans joined.
    /// The actual token acquisition remains the check: an idle queue or a
    /// token count cannot manufacture a missing guard. Pending returns None
    /// and returns any partial acquisition to the SAME original FIFO.
    pub(crate) fn try_escrow(self: &Arc<Self>) -> io::Result<Option<ForeignGnuEscrow>> {
        if self
            .escrowed
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Ok(None);
        }
        let mut escrow = ForeignGnuEscrow {
            fifo: self.clone(),
            tokens: Vec::new(),
            offered: false,
        };
        for _ in 0..self.supplementary {
            let Some(token) = self.jobserver.client().try_acquire()? else {
                return Ok(None);
            };
            escrow.tokens.push(token);
        }
        if self.jobserver.client().available()? != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "original GNU pool contains unbound supplementary tokens",
            ));
        }
        Ok(Some(escrow))
    }
}

impl ForeignGnuEscrow {
    /// Park current dispatch and join/exclude its workers before calling.
    /// Capture only credits previously returned by THIS escrow, retaining
    /// the same Acquired guards. A missing token leaves custody unchanged.
    pub(crate) fn try_recapture_backed(&mut self, count: usize) -> io::Result<bool> {
        if !self.offered || self.tokens.len().checked_add(count) != Some(self.fifo.supplementary) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "current GNU backing differs",
            ));
        }
        let mut returned = Vec::new();
        returned
            .try_reserve_exact(count)
            .map_err(io::Error::other)?;
        for _ in 0..count {
            let Some(token) = self.fifo.jobserver.client().try_acquire()? else {
                return Ok(false);
            };
            returned.push(token);
        }
        if self.fifo.jobserver.client().available()? != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unbound current GNU credits",
            ));
        }
        self.tokens
            .try_reserve_exact(returned.len())
            .map_err(io::Error::other)?;
        self.tokens.extend(returned);
        Ok(true)
    }

    /// Only after original Host positively acknowledges final Drained and
    /// all current worker/loan owners retired. Permanently consume credits;
    /// they must never return to a partially funded or completed GNU server.
    pub(crate) fn retire_drained(mut self) -> io::Result<()> {
        if !self.offered || self.tokens.len() != self.fifo.supplementary {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "GNU drain is incomplete",
            ));
        }
        for token in self.tokens.drain(..) {
            token.drop_without_releasing();
        }
        self.offered = false;
        Ok(())
    }
    /// Return only SAME Acquired guards after the native owner installed that
    /// many actual funded replacements. Unfunded guards remain escrowed; Drop
    /// of an offered partial phase still aborts instead of returning them.
    pub(crate) fn return_backed(&mut self, count: usize) -> io::Result<()> {
        if !self.offered || count > self.tokens.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "original GNU backing differs",
            ));
        }
        for _ in 0..count {
            drop(self.tokens.pop());
        }
        Ok(())
    }
    pub(super) fn belongs_to(&self, original: &Arc<PrivateFifo>) -> bool {
        !self.offered && Arc::ptr_eq(&self.fifo, original)
    }
    pub(crate) fn captive_original(&self, original: &Arc<PrivateFifo>) -> bool {
        self.offered
            && Arc::ptr_eq(&self.fifo, original)
            && self.tokens.len() == self.fifo.supplementary
    }
    pub(crate) fn ceiling(&self) -> usize {
        self.fifo.supplementary + 1
    }
    pub(crate) fn backing(&self) -> trust_resource_controller::FileIdentity {
        self.fifo.backing
    }

    pub(crate) fn descriptors(&self) -> [BorrowedFd<'_>; 2] {
        [
            self.fifo.witnesses[0].as_fd(),
            self.fifo.witnesses[1].as_fd(),
        ]
    }

    /// Must precede delivery, not merely successful Ready. A lost reply may
    /// have left a real foreign member running under the original owner.
    pub(crate) fn offered(&mut self) {
        self.offered = true;
    }

    /// The sole broker calls this only on an exact, positively known Left or
    /// an Enter refusal (which could not admit a foreign member). No public
    /// path, serialized reply or ordinary Drop can return an offered escrow.
    pub(crate) fn settled(mut self) {
        self.offered = false;
    }
}

impl Drop for ForeignGnuEscrow {
    fn drop(&mut self) {
        if self.offered {
            crate::resource_v3::workload::abort_unknown();
        }
        // Return the actual Acquired values before permitting another escrow.
        self.tokens.clear();
        self.fifo.escrowed.store(false, Ordering::Release);
    }
}

#[cfg(test)]
mod tests;

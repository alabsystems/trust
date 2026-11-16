//! Exact committed-source expectations joined to the shared physical guard.
//! Only the SAME original enrolled source constructs this wrapper. The existing
//! maintained selector and actual native closure still issue their own roles.
use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt as _;

use trust_resource_provenance::program::HeldSourceReadSet;
pub use trust_resource_provenance::program::SourceRead;

use super::*;

mod selection;
pub use selection::{DependencySourceRefusal, DependencySourceSnapshot};

/// Bounded physical selected reads retaining the SAME enrolled source and
/// authenticated repository. No caller rows, hashes, path or saved selection
/// can reconstruct this owner. It creates no native/Seed/SDK authority.
pub struct CommittedSourceReadSet {
    repository: Arc<CommittedRepository>,
    selected: HeldSourceReadSet,
    revoked: AtomicBool,
}

fn committed_blob(
    rows: &RepositoryRows,
    object: gix::ObjectId,
    end: Instant,
) -> io::Result<Vec<u8>> {
    rows.blob(object, end)
}
impl CommittedRepository {
    pub fn source_reads(
        self: &Arc<Self>,
        graph: &OriginalHostGraph,
    ) -> io::Result<CommittedSourceReadSet> {
        self.entries(graph)?;
        Ok(CommittedSourceReadSet {
            repository: Arc::clone(self),
            selected: HeldSourceReadSet::capture(self.source.directory()?, self.deadline)?,
            revoked: AtomicBool::new(false),
        })
    }
}
impl CommittedSourceReadSet {
    pub fn check_current(&self, graph: &OriginalHostGraph) -> io::Result<()> {
        let result = (|| {
            if self.revoked.load(Ordering::Acquire) {
                return Err(invalid("original committed source reads are quarantined"));
            }
            self.repository.entries(graph)?;
            self.selected.check_current(self.repository.source.directory()?)?;
            self.repository.entries(graph)?;
            Ok(())
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    /// Observe one exact committed component without following a link/gitlink.
    /// The maintained view resolves its literal links and must explicitly
    /// expand an original gitlink before asking for that child repository.
    /// Physical bytes come from retained no-follow originals, not Git buffers.
    pub fn observe(
        &mut self,
        graph: &OriginalHostGraph,
        relative: &[u8],
    ) -> io::Result<SourceRead> {
        let result = (|| {
            self.check_current(graph)?;
            let expected = match self.repository.lookup(graph, relative)? {
                CommittedLookup::Present(entry) => match entry.mode {
                    0o100644 | 0o100755 => SourceRead::File {
                        mode: entry.mode,
                        bytes: committed_blob(
                            &self.repository.rows,
                            entry.object,
                            self.selected.original_deadline(),
                        )?,
                    },
                    0o120000 => SourceRead::Link {
                        target: committed_blob(
                            &self.repository.rows,
                            entry.object,
                            self.selected.original_deadline(),
                        )?,
                    },
                    0o040000 => SourceRead::Directory,
                    _ => {
                        return Err(invalid(
                            "selected source gitlink needs its original child repository",
                        ));
                    }
                },
                CommittedLookup::Absent => SourceRead::Absent,
                CommittedLookup::Unresolved(_) => {
                    return Err(invalid("selected source crosses an unresolved original boundary"));
                }
            };
            let root_relative = self
                .repository
                .root()
                .strip_prefix(self.repository.source.path())
                .map_err(error)?
                .join(OsStr::from_bytes(relative));
            let value = self.selected.observe(
                self.repository.source.directory()?,
                &root_relative,
                expected,
            )?;
            self.check_current(graph)?;
            Ok(value)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }
}

#[cfg(test)]
mod tests;

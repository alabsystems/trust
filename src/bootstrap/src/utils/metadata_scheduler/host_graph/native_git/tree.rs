//! Exact local immutable tree observations beside the SAME enrolled source.
//! Gitlinks remain explicit unresolved boundaries, never empty directories or
//! proof of transitive completeness. Blob/physical bytes and the full recipe
//! read-set still require their own original guards and equality checks.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use build_helper::trust_repo_lock::management::OriginalSourceRoot;

use super::*;

mod reads;
pub use reads::{
    CommittedSourceReadSet, DependencySourceRefusal, DependencySourceSnapshot, SourceRead,
};
use trust_committed_source::CommittedRepositoryObservation;
pub use trust_committed_source::{CommittedEntry, CommittedLookup};

type RepositoryRows = Arc<CommittedRepositoryObservation>;

fn read_repository(
    directory: std::os::fd::BorrowedFd<'_>,
    root: &Path,
    deadline: Instant,
) -> io::Result<RepositoryRows> {
    CommittedRepositoryObservation::capture(directory, root, deadline).map(Arc::new)
}
fn read_submodule(
    parent: &RepositoryRows,
    relative: &[u8],
    deadline: Instant,
) -> io::Result<RepositoryRows> {
    parent.submodule(relative, deadline).map(Arc::new)
}
/// Non-Clone observation retaining the real original enrolled source. No
/// constructor accepts a path, caller rows, saved census or public digest.
pub struct CommittedRepository {
    source: Arc<OriginalSourceRoot>,
    key: trust_resource_controller::bootstrap_graph::Key,
    deadline: Instant,
    creator: u32,
    revoked: AtomicBool,
    rows: RepositoryRows,
    // A child cannot outlive, replace or forget its original parent census.
    parent: Option<Arc<CommittedRepository>>,
    depth: usize,
}
impl CommittedRepository {
    /// Original observed commit DATA, not currentness or source ownership.
    pub fn commit(&self) -> gix::ObjectId {
        self.rows.commit()
    }

    /// Original physical root DATA, not authority to reopen a different owner.
    pub fn root(&self) -> &Path {
        self.rows.root()
    }

    /// Resolve ONLY an exact parent-committed gitlink into its actual local
    /// repository. No guessed mirror list, arbitrary path/root, implicit
    /// expansion, fetch or saved child rows can supply this population.
    pub fn submodule(
        self: &Arc<Self>,
        graph: &OriginalHostGraph,
        relative: &[u8],
    ) -> io::Result<Self> {
        let result = (|| {
            self.entries(graph)?;
            if self.depth >= 64 {
                return Err(invalid("original committed submodule depth exceeds bound"));
            }
            let rows = read_submodule(&self.rows, relative, self.deadline)?;
            self.entries(graph)?;
            Ok(Self {
                source: Arc::clone(&self.source),
                key: self.key.clone(),
                deadline: self.deadline,
                creator: self.creator,
                revoked: AtomicBool::new(false),
                rows,
                parent: Some(Arc::clone(self)),
                depth: self.depth + 1,
            })
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
            if let Ok(mut state) = lock(&graph.state, self.deadline) {
                state.failed = true;
            }
        }
        result
    }

    pub fn lookup<'a>(
        &'a self,
        graph: &OriginalHostGraph,
        path: &[u8],
    ) -> io::Result<CommittedLookup<'a>> {
        let result = (|| {
            self.entries(graph)?;
            let value = self.rows.lookup(path, self.deadline)?;
            self.source.check_current()?;
            graph.check()?;
            Ok(value)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
            if let Ok(mut state) = lock(&graph.state, self.deadline) {
                state.failed = true;
            }
        }
        result
    }

    pub fn entries<'a>(&'a self, graph: &OriginalHostGraph) -> io::Result<&'a [CommittedEntry]> {
        let result = (|| {
            if self.creator != std::process::id()
                || self.revoked.load(Ordering::Acquire)
                || self.key != graph.key
                || self.deadline > graph.deadline
            {
                return Err(invalid("committed source has another original graph or process"));
            }
            graph.check()?;
            self.source.check_current()?;
            if let Some(parent) = &self.parent {
                parent.entries(graph)?;
            }
            let original = lock(&graph.state, self.deadline)?
                .source
                .as_ref()
                .cloned()
                .ok_or_else(|| invalid("original graph source is absent"))?;
            if !Arc::ptr_eq(&original, &self.source) {
                return Err(invalid("committed source has another original source owner"));
            }
            let entries = self.rows.entries(self.deadline)?;
            self.source.check_current()?;
            graph.check()?;
            Ok(entries)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
            if let Ok(mut state) = lock(&graph.state, self.deadline) {
                state.failed = true;
            }
        }
        result
    }
}
impl OriginalHostGraph {
    pub fn committed_source(&self) -> io::Result<CommittedRepository> {
        self.check()?;
        let result = (|| {
            let source =
                lock(&self.state, self.deadline)?.source.as_ref().cloned().ok_or_else(|| {
                    invalid("committed tree needs the real enrolled original source")
                })?;
            source.check_current()?;
            let deadline = self.deadline.min(source.deadline());
            let rows = read_repository(source.directory()?, source.path(), deadline)?;
            source.check_current()?;
            self.check()?;
            Ok(CommittedRepository {
                source,
                key: self.key.clone(),
                deadline,
                creator: std::process::id(),
                revoked: AtomicBool::new(false),
                rows,
                parent: None,
                depth: 0,
            })
        })();
        if result.is_err() {
            if let Ok(mut state) = lock(&self.state, self.deadline) {
                state.failed = true;
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;

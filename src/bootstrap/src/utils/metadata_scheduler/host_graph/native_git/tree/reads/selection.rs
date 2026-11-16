//! Semantic original-source wrapper around the SAME shared passive capture.
//! Graph/Manager/source and actual closure/join authority stay here. Packet
//! bytes remain DATA; no pathname, packet or caller rows construct this owner.
use std::path::PathBuf;

use build_helper::trust_repo_lock::management::{
    LocalJoinedScope, OriginalSourceOffer, ScopeDispatch,
};
use trust_committed_source::CommittedDependencySnapshot;
use trust_resource_controller::client::bootstrap_graph::InputWorkClosed;

use super::*;

/// Retains the actual SAME graph/source beside its shared passive observations.
pub struct DependencySourceSnapshot {
    graph: Arc<OriginalHostGraph>,
    source: Option<Arc<OriginalSourceRoot>>,
    observation: Option<Box<CommittedDependencySnapshot>>,
    revoked: AtomicBool,
}
pub struct DependencySourceRefusal {
    error: io::Error,
    original: Box<DependencySourceSnapshot>,
}
impl DependencySourceRefusal {
    pub fn into_parts(self) -> (io::Error, Box<DependencySourceSnapshot>) {
        (self.error, self.original)
    }
}

// Pure serializer control; ordinary snapshot packet generation uses the same
// shared implementation through CommittedDependencySnapshot::packet.
#[cfg(test)]
pub(super) fn bounded_packet(value: &serde_json::Value, limit: usize) -> io::Result<Vec<u8>> {
    trust_committed_source::encode_dependency_packet(value, limit)
}

// Feed the original result through one quarantine path. On error, the caller
// first latches its SAME graph and supplies only its already-held scope. Tests
// can exercise actual source/read/serializer refusal on genuine local owners
// without constructing a live Host, Graph or opaque native closure.
pub(super) fn quarantine_on_error<T>(
    result: io::Result<T>,
    revoked: &AtomicBool,
    original_scope: impl FnOnce() -> Option<ScopeDispatch>,
) -> io::Result<T> {
    if result.is_err() {
        revoked.store(true, Ordering::Release);
        if let Some(scope) = original_scope() {
            scope.record_failure("original dependency source snapshot refused");
        }
    }
    result
}

impl DependencySourceSnapshot {
    fn record_result<T>(&self, result: io::Result<T>) -> io::Result<T> {
        quarantine_on_error(result, &self.revoked, || {
            // Every caller has left its fallible read/check closure. Preserve
            // the existing Graph -> protected-scope lock order, and release
            // the Graph mutex before recording the scope's permanent failure.
            if let Ok(mut state) = lock(&self.graph.state, self.graph.deadline) {
                state.failed = true;
                state.scope.as_ref().and_then(|scope| scope.upgrade().ok())
            } else {
                // Poison or the SAME expired endpoint already forbids every
                // graph alias. Never recover/reset it to obtain a dispatcher.
                None
            }
        })
    }

    fn source(&self) -> io::Result<&Arc<OriginalSourceRoot>> {
        self.source.as_ref().ok_or_else(|| invalid("dependency source owner is absent"))
    }
    fn observation(&self) -> io::Result<&CommittedDependencySnapshot> {
        self.observation.as_deref().ok_or_else(|| invalid("dependency passive capture is absent"))
    }

    /// Endpoint DATA from the SAME original, never a renewed budget.
    pub fn original_deadline(&self) -> Instant {
        self.observation
            .as_deref()
            .map_or(self.graph.deadline, |snapshot| snapshot.original_deadline())
    }
    fn current_deadline(&self) -> io::Result<Instant> {
        Ok(self.original_deadline().min(self.graph.input_deadline()?))
    }

    pub fn check_current(&self) -> io::Result<()> {
        let result = (|| {
            if self.revoked.load(Ordering::Acquire) {
                return Err(invalid("dependency source snapshot is quarantined"));
            }
            self.graph.check()?;
            let source = self.source()?;
            let original = lock(&self.graph.state, self.graph.deadline)?
                .source
                .as_ref()
                .cloned()
                .ok_or_else(|| invalid("original graph source is absent"))?;
            let observation = self.observation()?;
            if !Arc::ptr_eq(source, &original)
                || observation.root().as_os_str() != source.path().as_os_str()
                || observation.original_deadline() > self.graph.deadline
                || observation.original_deadline() > source.deadline()
            {
                return Err(invalid("dependency capture has another original source or endpoint"));
            }
            source.check_current()?;
            observation.check_current(source.directory()?, self.current_deadline()?)?;
            source.check_current()?;
            self.graph.check()
        })();
        self.record_result(result)
    }

    /// Discharge only listing requests from the SAME maintained discovery.
    pub fn capture_glob_directories(&mut self, paths: &[PathBuf]) -> io::Result<()> {
        let result = (|| {
            self.check_current()?;
            let source = Arc::clone(self.source()?);
            let deadline = self.current_deadline()?;
            self.observation
                .as_deref_mut()
                .ok_or_else(|| invalid("dependency passive capture is absent"))?
                .capture_glob_directories(source.directory()?, paths, deadline)?;
            self.check_current()
        })();
        self.record_result(result)
    }

    /// Encode only the packet derived by the SAME actual retained capture.
    pub fn packet(&self) -> io::Result<Vec<u8>> {
        let result = (|| {
            self.check_current()?;
            let bytes = self
                .observation()?
                .packet(self.source()?.directory()?, self.current_deadline()?)?;
            self.check_current()?;
            Ok(bytes)
        })();
        self.record_result(result)
    }

    /// Final bookend only after opaque native source closure and actual local
    /// joins. No live OPEN dispatcher or reconstructed closure is consulted.
    pub(in crate::utils::metadata_scheduler::host_graph) fn check_joined(
        &self,
        graph: &Arc<OriginalHostGraph>,
        request: &trust_resource_controller::bootstrap_graph::preparation::Request,
        source: &Arc<OriginalSourceRoot>,
        joined: &LocalJoinedScope,
        offer: &OriginalSourceOffer,
        closed: &InputWorkClosed,
    ) -> io::Result<()> {
        let result = (|| {
            if self.revoked.load(Ordering::Acquire)
                || !Arc::ptr_eq(&self.graph, graph)
                || !Arc::ptr_eq(self.source()?, source)
                || closed.attempt() != request
                || request.key.graph != graph.key
                || closed.source().key != graph.key
                || self.original_deadline() > graph.deadline
                || self.original_deadline() > source.deadline()
            {
                return Err(invalid("joined dependency snapshot has another original closure"));
            }
            let deadline = self.current_deadline()?;
            check_final_graph(graph, deadline)?;
            let directory = source.joined_input_directory(joined, offer, closed)?;
            self.observation()?.check_current(directory, deadline)?;
            source.joined_input_directory(joined, offer, closed)?;
            check_final_graph(graph, deadline)?;
            time(deadline)
        })();
        self.record_result(result)
    }
}

// Preserve negative graph latches after the actual transition consumed its
// connection/source fields. This checks no OPEN dispatcher or native phase.
fn check_final_graph(graph: &OriginalHostGraph, deadline: Instant) -> io::Result<()> {
    let state = lock(&graph.state, deadline)?;
    if state.failed
        || state.failure.is_some()
        || state.graph_failure.is_some()
        || state.object_failure.is_some()
        || state.source_task_active
        || !state.objects.is_empty()
        || state.compilation.is_some()
        || state.compilation_failure.is_some()
    {
        return Err(invalid("joined dependency graph retains an unresolved operation"));
    }
    time(deadline)
}

// The SAME production bookend is shared with the passive snapshot and actual
// joined caller. Real Git/readset tests exercise it without a fake live graph.
#[cfg(test)]
pub(super) fn check_final_rows(
    rows: &[&RepositoryRows],
    selected: &HeldSourceReadSet,
    directory: std::os::fd::BorrowedFd<'_>,
    deadline: Instant,
) -> io::Result<()> {
    trust_committed_source::check_committed_reads(rows, selected, directory, deadline)
}

impl OriginalHostGraph {
    /// The actual graph/source retains the SAME passive capture through both
    /// reader passes, true native source closure and all actual local joins.
    pub fn dependency_source_snapshot(
        self: &Arc<Self>,
    ) -> Result<DependencySourceSnapshot, DependencySourceRefusal> {
        let mut snapshot = DependencySourceSnapshot {
            graph: Arc::clone(self),
            source: None,
            observation: None,
            revoked: AtomicBool::new(false),
        };
        let captured = (|| {
            self.check()?;
            let source = lock(&self.state, self.deadline)?
                .source
                .as_ref()
                .cloned()
                .ok_or_else(|| invalid("dependency capture needs the real enrolled source"))?;
            snapshot.source = Some(Arc::clone(&source));
            source.check_current()?;
            let deadline = self.input_deadline()?.min(source.deadline());
            match CommittedDependencySnapshot::capture(source.directory()?, source.path(), deadline)
            {
                Ok(observation) => snapshot.observation = Some(Box::new(observation)),
                Err(refusal) => {
                    let (error, observation) = refusal.into_parts();
                    snapshot.observation = Some(observation);
                    return Err(error);
                }
            }
            source.check_current()?;
            snapshot.check_current()
        })();
        match snapshot.record_result(captured) {
            Ok(()) => Ok(snapshot),
            Err(error) => Err(DependencySourceRefusal { error, original: Box::new(snapshot) }),
        }
    }
}

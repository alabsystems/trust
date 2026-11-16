//! Original accepted input enrollment advanced in place. No decoded frame,
//! observation or constructor from paths/status can create this opaque owner.
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

use super::*;
use crate::bootstrap_graph::compilation::{AdvanceRequest, Advanced};

mod compiler;
pub use compiler::{
    ClosedLinker, CompilerAdoptionFailure, CompilerLinkerFailure, CompilerMember, PairedLinkerLoan,
    UnlentLinker,
};
pub(in crate::client::bootstrap_graph) mod finish;
pub use finish::RefusedCompilationClose;
mod member;
pub use member::{BootstrapMemberFailure, ResidentBootstrapMember, RetiredBootstrapMember};

/// Retains the SAME original accepted connection and completed input owner.
/// Host support/codec DATA is insufficient: the actual original native issuer
/// must accept the advance before this private constructor can be reached.
#[must_use]
pub struct ResidentBootstrapCompilation {
    graph: OutputBoundBootstrapGraph,
    inputs: ResidentDependencyInputs,
    client: Client,
    request: AdvanceRequest,
    advanced: Advanced,
    deadline: Instant,
    failed: AtomicBool,
    members: Mutex<member::Members>,
}
impl ResidentBootstrapCompilation {
    pub fn data(&self) -> &Advanced {
        &self.advanced
    }
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }
    pub fn input_phase_deadline(&self) -> Instant {
        self.inputs.original_deadline()
    }

    /// Observe ONLY this SAME already-issued Full key under its original Root
    /// bound. No input deadline is reset, owner revived or new Root constructed.
    pub fn check_current(&self, deadline: Instant) -> io::Result<()> {
        if self.failed.load(Ordering::Acquire) {
            return Err(crate::wire::invalid());
        }
        let deadline = deadline.min(self.deadline);
        let result = (|| {
            let original = self.graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
            original.check(deadline)?;
            observe(&self.graph, &self.client, &self.request, deadline, |actual| {
                if actual != &self.advanced {
                    return Err(crate::wire::invalid());
                }
                Ok(())
            })?;
            original.check(deadline)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
}

/// Unknown delivery keeps the actual accepted graph/input owner. No retry,
/// ordinary query/close, release or replacement constructor is exposed here.
#[must_use]
pub struct RefusedCompilationAdvance {
    error: io::Error,
    _graph: Box<OutputBoundBootstrapGraph>,
    _inputs: Box<ResidentDependencyInputs>,
}
impl std::fmt::Debug for RefusedCompilationAdvance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedCompilationAdvance")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for RefusedCompilationAdvance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for RefusedCompilationAdvance {}

fn same_bindings(
    graph: &OutputBoundBootstrapGraph,
    request: &AdvanceRequest,
    value: &Advanced,
) -> io::Result<()> {
    value.validate()?;
    let original = graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
    if value.key.attempt != request.attempt
        || value.source != graph.source
        || value.output != graph.output
        || value.gnu != original.request.gnu
        || value
            .seed
            .compiler_queries
            .iter()
            .any(|query| query.request.cwd != original.request.source)
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
fn observe(
    graph: &OutputBoundBootstrapGraph,
    client: &Client,
    request: &AdvanceRequest,
    deadline: Instant,
    validate: impl FnOnce(&Advanced) -> io::Result<()>,
) -> io::Result<Advanced> {
    let original = graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
    original.check(deadline)?;
    if !Arc::ptr_eq(&original.pin, &client.host) {
        return Err(crate::wire::invalid());
    }
    let host = client.host.connect(deadline)?;
    let mut channel = Channel::new(host.stream().try_clone()?)?;
    host.revalidate(deadline)?;
    channel.send(&request.hello()?, deadline)?;
    channel.send(&request.encode()?, deadline)?;
    let value = Advanced::decode(&channel.receive(deadline)?)?;
    preparation::finish_reply(&mut channel, deadline, || {
        host.revalidate(deadline)?;
        original.check(deadline)?;
        same_bindings(graph, request, &value)?;
        validate(&value)
    })?;
    Ok(value)
}

impl OutputBoundBootstrapGraph {
    /// Consume the actual completed input session into the SAME accepted graph.
    /// The Host must have retained the original Full owner/seed/Root deadline
    /// FROM FIRST ENROLLMENT; a shorter completed phase cannot extend them.
    /// An old/unsupported Host refuses; no Supported/ready result is fabricated.
    pub fn advance_dependency_input_work(
        self,
        client: &Client,
        work: ResidentDependencyInputs,
        original_arguments: Vec<Vec<u8>>,
        deadline: Instant,
    ) -> Result<ResidentBootstrapCompilation, RefusedCompilationAdvance> {
        let request = AdvanceRequest { attempt: work.data().attempt.clone(), original_arguments };
        let result = (|| {
            request.validate()?;
            work.validate_completed_for_advance(&self, client, deadline)?;
            let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
            let root_deadline = original.deadline;
            let at = deadline.min(work.original_deadline()).min(root_deadline);
            time(at)?;
            let advanced = observe(&self, client, &request, at, |value| {
                same_initial_seed(value, work.data())
            })?;
            original.check(at)?;
            Ok((advanced, root_deadline))
        })();
        match result {
            Ok((advanced, deadline)) => Ok(ResidentBootstrapCompilation {
                graph: self,
                inputs: work,
                client: client.clone(),
                request,
                advanced,
                deadline,
                failed: AtomicBool::new(false),
                members: Mutex::new(member::Members::default()),
            }),
            Err(error) => Err(RefusedCompilationAdvance {
                error,
                _graph: Box::new(self),
                _inputs: Box::new(work),
            }),
        }
    }
}

fn same_initial_seed(
    value: &Advanced,
    data: &crate::bootstrap_graph::preparation::work::InputData,
) -> io::Result<()> {
    if value.seed.root != data.seed_root
        || value.seed.compiler != data.compiler
        || value.seed.compiler_queries != data.compiler_queries
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn advance_matches_actual_completed_input_seed_and_every_retained_query_field() {
        // These are DATA joins only; no fake client, Host, SDK or Full owner.
        let value = crate::bootstrap_graph::compilation::tests::advanced();
        let data = crate::bootstrap_graph::preparation::work::tests::inputs();
        same_initial_seed(&value, &data).unwrap();
        for index in 0..5 {
            let mut changed = value.clone();
            match index {
                0 => changed.seed.root = b"/replacement/seed".to_vec(),
                1 => changed.seed.compiler.inode += 1,
                2 => changed.seed.compiler_queries[0].stdout.push(b'x'),
                3 => changed.seed.compiler_queries[0].stderr.push(b'x'),
                _ => changed.seed.compiler_queries[0]
                    .command
                    .environment
                    .push((b"UNISSUED".to_vec(), b"override".to_vec())),
            }
            assert!(same_initial_seed(&changed, &data).is_err());
        }
    }
}

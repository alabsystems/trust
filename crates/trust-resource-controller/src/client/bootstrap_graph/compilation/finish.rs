//! Consuming Full source-work closure. Frames/status cannot construct this path.
use super::*;
use crate::bootstrap_graph::compilation::finish::{CloseRequest, Closed};

/// A refused close owns the SAME actual accepted enrollment. Unknown may only
/// retry this exact Close; no ordinary query/member or owner getter is exposed.
#[must_use]
pub struct RefusedCompilationClose {
    error: io::Error,
    held: Option<Held>,
}
enum Held {
    Shared(Arc<ResidentBootstrapCompilation>),
    Sole(Box<ResidentBootstrapCompilation>),
}
impl RefusedCompilationClose {
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    pub fn retry(mut self, deadline: Instant) -> Result<InputWorkClosed, Self> {
        match self.held.take().expect("same original close owner") {
            Held::Shared(owner) => owner.finish(deadline),
            Held::Sole(owner) => finish(owner, deadline),
        }
    }
}
impl std::fmt::Debug for RefusedCompilationClose {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefusedCompilationClose")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for RefusedCompilationClose {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for RefusedCompilationClose {}
impl Drop for RefusedCompilationClose {
    fn drop(&mut self) {
        if let Some(held) = self.held.take() {
            std::mem::forget(held);
        }
    }
}

/// Private actual-path-only result after native closure AND disposal of the
/// original accepted enrollment. Its sole consumer is the existing source-work
/// witness adapter; there is no constructor from a tuple/frame/bool/status.
#[must_use]
pub(in crate::client::bootstrap_graph) struct ClosedSourceWork {
    work: ResidentDependencyInputs,
    root_deadline: Instant,
}
impl ClosedSourceWork {
    pub(in crate::client::bootstrap_graph) fn into_work(
        self,
    ) -> (ResidentDependencyInputs, Instant) {
        (self.work, self.root_deadline)
    }
}
impl ResidentBootstrapCompilation {
    pub fn finish(
        self: Arc<Self>,
        deadline: Instant,
    ) -> Result<InputWorkClosed, RefusedCompilationClose> {
        match Arc::try_unwrap(self) {
            Ok(owner) => finish(Box::new(owner), deadline),
            Err(owner) => Err(RefusedCompilationClose {
                error: io::Error::other("original Full compilation still has local borrowers"),
                held: Some(Held::Shared(owner)),
            }),
        }
    }
}
fn same_bindings(actual: &Advanced, closed: &Closed) -> io::Result<()> {
    closed.validate()?;
    if closed.request.key != actual.key
        || closed.source != actual.source
        || closed.output != actual.output
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
fn finish(
    mut owner: Box<ResidentBootstrapCompilation>,
    deadline: Instant,
) -> Result<InputWorkClosed, RefusedCompilationClose> {
    let result = (|| {
        let at = deadline.min(owner.deadline);
        time(at)?;
        if owner.failed.load(Ordering::Acquire)
            || !owner.members.get_mut().map_err(|_| crate::wire::invalid())?.idle()
        {
            return Err(crate::wire::invalid());
        }
        // Do not re-enter Advance or the expired900s preparation phase on an
        // idempotent Close retry. The SAME original Root bound/pin remain live.
        let original = owner.graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
        if !Arc::ptr_eq(&original.pin, &owner.client.host) {
            return Err(crate::wire::invalid());
        }
        original.check(at)?;
        let host = owner.client.host.connect(at)?;
        let mut channel = Channel::new(host.stream().try_clone()?)?;
        host.revalidate(at)?;
        let request = CloseRequest { key: owner.advanced.key.clone() };
        channel.send(&request.hello()?, at)?;
        channel.send(&request.encode()?, at)?;
        let closed = Closed::decode(&channel.receive(at)?)?;
        preparation::finish_reply(&mut channel, at, || {
            host.revalidate(at)?;
            original.check(at)?;
            same_bindings(&owner.advanced, &closed)
        })?;
        Ok(())
    })();
    if let Err(error) = result {
        return Err(RefusedCompilationClose { error, held: Some(Held::Sole(owner)) });
    }
    let mut original = owner.graph.original.take().expect("same actual enrolled Full connection");
    // SAFETY: the sole owner now consumed the SAME pinned native all-source-
    // work closure with exact source/output bindings. Physically close its
    // original enrollment before issuing the existing protected-source witness.
    unsafe {
        ManuallyDrop::drop(&mut original.channel);
        ManuallyDrop::drop(&mut original.original);
        ManuallyDrop::drop(&mut original.pin);
    }
    let ResidentBootstrapCompilation { inputs, deadline, .. } = *owner;
    Ok(InputWorkClosed::from_full_source_closed(ClosedSourceWork {
        work: inputs,
        root_deadline: deadline,
    }))
}
#[cfg(test)]
mod tests;

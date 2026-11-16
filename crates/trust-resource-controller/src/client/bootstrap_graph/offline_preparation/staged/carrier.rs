//! The SAME pinned program-selection carrier. Packet/stream state creates no
//! Host, graph, namespace, program or native-completion owner.
use std::mem::ManuallyDrop;
use trust_resource_provenance::Host;
use super::*;

/// The actual authenticated connection is retained before channel construction
/// or any request. Unknown/error/unwind keeps both SAME descriptions; only the
/// physically closed and acknowledged selector reply permits their disposal.
pub(super) struct ProgramsCarrier {
    host: Option<ManuallyDrop<Host>>,
    channel: Option<ManuallyDrop<Channel>>,
    creator: u32,
    deadline: Instant,
    closed: bool,
    failed: bool,
}
impl ProgramsCarrier {
    pub(super) fn new(host: Host, deadline: Instant) -> Self {
        Self { host: Some(ManuallyDrop::new(host)), channel: None,
            creator: std::process::id(), deadline, closed: false, failed: false }
    }
    pub(super) fn open(&mut self, deadline: Instant) -> io::Result<()> {
        if self.creator != std::process::id() || self.failed || self.closed || self.channel.is_some() {
            return Err(crate::wire::invalid());
        }
        bounded(self.deadline, deadline)?;
        let host = self.host.as_ref().ok_or_else(crate::wire::invalid)?;
        host.revalidate(deadline)?;
        self.channel = Some(ManuallyDrop::new(Channel::new(host.stream().try_clone()?)?));
        self.check_current(deadline)
    }
    pub(super) fn check_current(&self, deadline: Instant) -> io::Result<()> {
        if self.creator != std::process::id() || self.failed {
            return Err(crate::wire::invalid());
        }
        bounded(self.deadline, deadline)?;
        if self.closed {
            // This records only the already completed short reply lifetime.
            // The separate original Source connection still owns its graph.
            return Ok(());
        }
        self.host.as_ref().ok_or_else(crate::wire::invalid)?.revalidate(deadline)?;
        if self.channel.as_ref().ok_or_else(crate::wire::invalid)?.poisoned() {
            return Err(crate::wire::invalid());
        }
        time(deadline)
    }
    pub(super) fn parts(&mut self, deadline: Instant) -> io::Result<(&Host, &mut Channel)> {
        self.check_current(deadline)?;
        if self.closed { return Err(crate::wire::invalid()); }
        Ok((self.host.as_ref().ok_or_else(crate::wire::invalid)?,
            self.channel.as_mut().ok_or_else(crate::wire::invalid)?))
    }
    pub(super) fn restrict(&mut self, deadline: Instant) {
        self.deadline = self.deadline.min(deadline);
    }
    pub(super) fn poison(&mut self) {
        self.failed = true;
        if let Some(channel) = &mut self.channel { channel.poison(); }
    }
    pub(super) fn closed_reply(&mut self) {
        // Called only after real reply EOF, validation, ACK and postchecks on
        // this SAME carrier. This closes no Source/root/native work owner.
        self.closed = true;
        if let Some(channel) = self.channel.take() { drop(ManuallyDrop::into_inner(channel)); }
        if let Some(host) = self.host.take() { drop(ManuallyDrop::into_inner(host)); }
    }
}

fn observed<T>(channel: &mut Channel, result: io::Result<T>) -> io::Result<T> {
    if result.is_err() { channel.poison(); }
    result
}
pub(super) fn reserve(
    channel: &mut Channel, query: &ProgramSelectionQuery, deadline: Instant,
) -> io::Result<ReservedPrograms> {
    let result = (|| {
        channel.send(&query.hello()?, deadline)?;
        channel.send(&query.encode()?, deadline)?;
        ReservedPrograms::decode(&channel.receive(deadline)?, query)
    })();
    observed(channel, result)
}

pub(super) fn reservation_boundary(
    channel: &mut Channel, deadline: Instant,
    validate: impl FnOnce() -> io::Result<()>,
) -> io::Result<()> {
    // ReservedPrograms is an intermediate observation. The real native handler
    // now waits for ProgramSelection on this SAME channel; no EOF or ACK here.
    let result = (|| { time(deadline)?; validate()?; time(deadline) })();
    observed(channel, result)
}

pub(super) fn select(
    channel: &mut Channel, selection: &ProgramSelection, deadline: Instant,
) -> io::Result<ProgramSelectionReply> {
    let result = (|| {
        channel.send(&selection.encode()?, deadline)?;
        ProgramSelectionReply::decode(&channel.receive(deadline)?, selection)
    })();
    observed(channel, result)
}

#[cfg(test)]
mod tests;

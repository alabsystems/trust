//! Live pinned input client; observations never construct these owners.
use super::super::*;
use crate::bootstrap_graph::preparation::Request;
use crate::bootstrap_graph::preparation::work::{Action, InputData, WorkReply, WorkRequest};

#[must_use]
pub struct ResidentDependencyInputs {
    pin: Arc<PinnedHelper>,
    context: ContextReply,
    deadline: Instant,
    data: InputData,
    source: SourceAttachment,
    output: OutputAttachment,
    finished: u32,
    failed: bool,
}
impl ResidentDependencyInputs {
    pub fn data(&self) -> &InputData {
        &self.data
    }
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }
    fn exchange(&self, action: Action, deadline: Instant) -> io::Result<WorkReply> {
        let deadline = deadline.min(self.deadline);
        time(deadline)?;
        if self.failed {
            return Err(crate::wire::invalid());
        }
        live(&self.context, deadline)?;
        let original = self.pin.connect(deadline)?;
        let mut channel = Channel::new(original.stream().try_clone()?)?;
        let request = WorkRequest { attempt: self.data.attempt.clone(), action };
        original.revalidate(deadline)?;
        channel.send(&request.hello()?, deadline)?;
        channel.send(&request.encode()?, deadline)?;
        let reply = WorkReply::decode(&channel.receive(deadline)?)?;
        super::finish_reply(&mut channel, deadline, || {
            original.revalidate(deadline)?;
            self.pin.validate(deadline)?;
            live(&self.context, deadline)
        })?;
        Ok(reply)
    }
    pub fn check_current(&self, deadline: Instant) -> io::Result<()> {
        match self.exchange(Action::Inputs, deadline)? {
            WorkReply::Inputs(actual) if actual.as_ref() == &self.data => Ok(()),
            _ => Err(crate::wire::invalid()),
        }
    }
    pub(in crate::client::bootstrap_graph) fn validate_completed_for_advance(
        &self,
        graph: &OutputBoundBootstrapGraph,
        client: &Client,
        deadline: Instant,
    ) -> io::Result<()> {
        let original = graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
        let attempt = graph.preparation.as_ref().ok_or_else(crate::wire::invalid)?;
        if !Arc::ptr_eq(&self.pin, &client.host)
            || !Arc::ptr_eq(&self.pin, &original.pin)
            || self.data.attempt != attempt.request
            || !attempt.opened
            || self.source != graph.source
            || self.output != graph.output
            || self.finished != self.data.total()?
            || self.failed
        {
            return Err(crate::wire::invalid());
        }
        // A Full owner must have retained its Root lifetime up front. This
        // check still enforces the ORIGINAL input phase deadline before advance.
        original.check(deadline.min(self.deadline))?;
        self.check_current(deadline)
    }

    /// # Safety
    /// Only the original authenticated Targo adapter may call this after its
    /// SAME scoped Cargo library fetched the next exact manifest with locked
    /// policy and the planned offline mode. A saved status, arbitrary closure,
    /// subset or replacement compiler cannot substitute for actual resolution.
    pub unsafe fn recipe_completed(&mut self, deadline: Instant) -> io::Result<()> {
        if self.finished >= self.data.total()? {
            return Err(crate::wire::invalid());
        }
        let next = self.finished + 1;
        let result = match self.exchange(Action::Checkpoint(next), deadline) {
            Ok(WorkReply::Checked { attempt, finished })
                if attempt == self.data.attempt && finished == next =>
            {
                Ok(())
            }
            Ok(_) => Err(crate::wire::invalid()),
            Err(error) => Err(error),
        };
        self.failed = result.is_err();
        result?;
        self.finished = next;
        Ok(())
    }
}

/// Only the same pinned exchange after actual native source-work closure and
/// physical enrollment disposal constructs this witness. Component Close or
/// the strictly stronger consuming Full close may issue it. CPU/GNU/Root
/// retirement remains a separate owner; no decoded status/frame constructs it.
#[must_use]
pub struct InputWorkClosed {
    pin: Arc<PinnedHelper>,
    context: ContextReply,
    deadline: Instant,
    attempt: Request,
    source: SourceAttachment,
    output: OutputAttachment,
}
impl InputWorkClosed {
    // This private adapter consumes ONLY the opaque actual Full native closure,
    // never its frame/status. The Root bound was captured before any input work.
    pub(in crate::client::bootstrap_graph) fn from_full_source_closed(
        closed: super::super::compilation::finish::ClosedSourceWork,
    ) -> Self {
        let (work, deadline) = closed.into_work();
        Self {
            pin: work.pin,
            context: work.context,
            deadline,
            attempt: work.data.attempt,
            source: work.source,
            output: work.output,
        }
    }

    pub fn source(&self) -> &SourceAttachment {
        &self.source
    }
    pub fn output(&self) -> &OutputAttachment {
        &self.output
    }
    pub fn attempt(&self) -> &Request {
        &self.attempt
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        let deadline = deadline.min(self.deadline);
        time(deadline)?;
        self.pin.validate(deadline)?;
        live(&self.context, deadline)
    }
}
impl OutputBoundBootstrapGraph {
    pub fn dependency_input_work(
        &mut self,
        client: &Client,
        request: &Request,
        deadline: Instant,
    ) -> io::Result<ResidentDependencyInputs> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        let attempt = self.preparation.as_mut().ok_or_else(crate::wire::invalid)?;
        if &attempt.request != request
            || attempt.opened
            || !Arc::ptr_eq(&original.pin, &client.host)
        {
            return Err(crate::wire::invalid());
        }
        let deadline = deadline.min(attempt.deadline);
        time(deadline)?;
        let host = client.host.connect(deadline)?;
        let mut channel = Channel::new(host.stream().try_clone()?)?;
        let operation = WorkRequest { attempt: request.clone(), action: Action::Inputs };
        host.revalidate(deadline)?;
        channel.send(&operation.hello()?, deadline)?;
        channel.send(&operation.encode()?, deadline)?;
        let WorkReply::Inputs(data) = WorkReply::decode(&channel.receive(deadline)?)? else {
            return Err(crate::wire::invalid());
        };
        super::finish_reply(&mut channel, deadline, || {
            host.revalidate(deadline)?;
            original.check(deadline)?;
            if &data.attempt != request || data.source != original.request.source {
                return Err(crate::wire::invalid());
            }
            Ok(())
        })?;
        attempt.opened = true;
        Ok(ResidentDependencyInputs {
            pin: Arc::clone(&client.host),
            context: original.context.clone(),
            deadline: attempt.deadline,
            data: *data,
            source: self.source.clone(),
            output: self.output.clone(),
            finished: 0,
            failed: false,
        })
    }
    pub fn finish_dependency_input_work(
        &mut self,
        client: &Client,
        work: ResidentDependencyInputs,
        deadline: Instant,
    ) -> io::Result<InputWorkClosed> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        let attempt = self.preparation.as_ref().ok_or_else(crate::wire::invalid)?;
        if !Arc::ptr_eq(&work.pin, &client.host)
            || work.data.attempt != attempt.request
            || !attempt.opened
            || work.source != self.source
            || work.output != self.output
            || work.finished != work.data.total()?
            || work.failed
        {
            return Err(crate::wire::invalid());
        }
        original.check(deadline)?;
        match work.exchange(Action::Close, deadline)? {
            WorkReply::Closed { attempt, source, output }
                if attempt == work.data.attempt
                    && *source == work.source
                    && output == work.output => {}
            _ => return Err(crate::wire::invalid()),
        }
        let mut original = self.original.take().expect("same pinned original connection");
        // Close the ACTUAL enrollment channel before the opaque client witness.
        // Failed/unwound paths retain the original connection instead.
        unsafe {
            ManuallyDrop::drop(&mut original.channel);
            ManuallyDrop::drop(&mut original.original);
            ManuallyDrop::drop(&mut original.pin);
        }
        Ok(InputWorkClosed {
            pin: work.pin,
            context: work.context,
            deadline: work.deadline,
            attempt: work.data.attempt,
            source: work.source,
            output: work.output,
        })
    }
}

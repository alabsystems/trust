//! Selector transfer on the SAME pinned original support. This carrier's ACK
//! acknowledges only retained DATA; it cannot settle the native operation,
//! clear its reservation, return a loan or retire any source/output/SDK owner.
use super::*;
use crate::bootstrap_graph::offline_preparation::{Intent, IntentQuery, IntentReply};

mod staged;
pub(super) use staged::StagedAttempt;

pub(super) struct IntentAttempt {
    query: IntentQuery,
    started: Instant,
    deadline: Instant,
    intent: Option<Intent>,
    acknowledged: bool,
    failed: bool,
}
impl IntentAttempt {
    fn binding(&self, key: &Key, queries: &QueryState, deadline: Instant) -> io::Result<()> {
        if self.failed || &self.query.key != key || !queries.offline_reserved {
            return Err(crate::wire::invalid());
        }
        bounded(self.deadline, deadline)
    }
    pub(super) fn ready(
        &self,
        key: &Key,
        queries: &QueryState,
        deadline: Instant,
    ) -> io::Result<()> {
        self.binding(key, queries, deadline)?;
        if !self.acknowledged || self.intent.is_none() {
            return Err(io::Error::other("original offline intent carrier remains unresolved"));
        }
        Ok(())
    }
    pub(super) fn enrolled(
        &self,
        enrollment: &Enrollment,
        queries: &QueryState,
        deadline: Instant,
    ) -> io::Result<()> {
        self.ready(&enrollment.key, queries, deadline)?;
        let intent = self.intent.as_ref().ok_or_else(crate::wire::invalid)?;
        if enrollment.source != intent.selection.source_root
            || enrollment.output != intent.selection.output_root
        {
            return Err(crate::wire::invalid());
        }
        Ok(())
    }
    fn observe(&mut self, reply: IntentReply, started: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed
                || reply.query != self.query
                || self.intent.as_ref().is_some_and(|intent| intent != &reply.intent)
            {
                return Err(crate::wire::invalid());
            }
            // The FIRST attempt starts the caller's budget. The response's
            // remaining bound starts before THIS connect, so transport time
            // can never renew it.
            self.deadline = self
                .deadline
                .min(original_deadline(started, reply.remaining_root_ns)?)
                .min(original_deadline(self.started, reply.intent.selection.budget_ns)?);
            self.intent = Some(reply.intent);
            time(self.deadline)
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
}

impl Client {
    /// Pull initial selector DATA only from the SAME authenticated admitted Host
    /// job. The Host must have retained it through a distinct typed native
    /// preparation submission before dispatch. This API neither enrolls source
    /// nor turns its path/environment bytes into native ownership.
    ///
    /// First call reserves this support BEFORE connect. Retry uses the SAME
    /// query/intent and original endpoint; uncertainty cannot create a new
    /// admission. A physical EOF, live same-peer/context checks and carrier ACK
    /// are required before actual source/output offers may begin.
    pub fn bootstrap_offline_preparation_intent(
        &self,
        support: &mut BootstrapGraphSupport,
        deadline: Instant,
    ) -> io::Result<Intent> {
        bounded(support.deadline, deadline)?;
        support.queries.enrollment_allowed()?;
        if !Arc::ptr_eq(&support.pin, &self.host) {
            return Err(crate::wire::invalid());
        }
        self.host.validate(deadline)?;
        live(&support.context, deadline)?;
        if support.offline_intent.is_none() {
            let started = Instant::now();
            let query = IntentQuery { key: support.key.clone() };
            query.encode()?;
            support.queries.reserve_offline()?;
            support.offline_intent = Some(IntentAttempt {
                query,
                started,
                deadline: support.deadline,
                intent: None,
                acknowledged: false,
                failed: false,
            });
        }
        let attempt = support.offline_intent.as_mut().ok_or_else(crate::wire::invalid)?;
        let at = deadline.min(attempt.deadline);
        attempt.binding(&support.key, &support.queries, at)?;
        let started = Instant::now();
        let host = self.host.connect(at)?;
        let mut channel = Channel::new(host.stream().try_clone()?)?;
        let result = (|| {
            host.revalidate(at)?;
            channel.send(&attempt.query.hello()?, at)?;
            channel.send(&attempt.query.encode()?, at)?;
            let bytes = channel.receive(at)?;
            let reply = match IntentReply::decode(&bytes, &attempt.query) {
                Ok(reply) => reply,
                Err(error) => {
                    attempt.failed = true;
                    return Err(error);
                }
            };
            attempt.observe(reply, started)?;
            // Retain the decoded immutable intent and shorter endpoint BEFORE
            // ACK. Lost ACK may reconnect, but never retarget this attempt.
            support.deadline = support.deadline.min(attempt.deadline);
            let at = at.min(attempt.deadline);
            preparation::finish_reply(&mut channel, at, || {
                host.revalidate(at)?;
                self.host.validate(at)?;
                attempt.binding(&support.key, &support.queries, at)?;
                live(&support.context, at)
            })?;
            host.revalidate(at)?;
            live(&support.context, at)?;
            attempt.acknowledged = true;
            attempt.ready(&support.key, &support.queries, at)?;
            attempt.intent.clone().ok_or_else(crate::wire::invalid)
        })();
        if result.is_err() {
            channel.poison();
        }
        result
    }
}

impl BootstrapGraphSupport {
    /// Negative routing observation only; it grants no original input owner.
    pub fn offline_preparation_selected(&self, deadline: Instant) -> io::Result<bool> {
        bounded(self.deadline, deadline)?;
        if let Some(attempt) = &self.offline_intent {
            attempt.ready(&self.key, &self.queries, deadline)?;
        }
        if let Some(attempt) = &self.offline_staged {
            attempt.ready(&self.key, &self.queries, deadline)?;
        }
        Ok(self.offline_intent.is_some() || self.offline_staged.is_some())
    }
    /// Retained original selectors only after their carrier finished. Still
    /// DATA: actual Managers and source/config/materialization offers are owed.
    pub fn offline_preparation_intent(&self, deadline: Instant) -> io::Result<Option<&Intent>> {
        let Some(attempt) = &self.offline_intent else { return Ok(None) };
        attempt.ready(&self.key, &self.queries, deadline)?;
        Ok(attempt.intent.as_ref())
    }
}

impl EnrolledBootstrapGraph {
    /// Negative routing observation only, never configuration/native custody.
    pub fn offline_preparation_selected(&self, deadline: Instant) -> io::Result<bool> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        Ok(original.offline_intent.is_some() || original.offline_staged.is_some())
    }
}
impl SourceBoundBootstrapGraph {
    pub fn offline_preparation_selected(&self, deadline: Instant) -> io::Result<bool> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        Ok(original.offline_intent.is_some() || original.offline_staged.is_some())
    }
}

impl OutputBoundBootstrapGraph {
    pub fn offline_preparation_selected(&self, deadline: Instant) -> io::Result<bool> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        Ok(original.offline_intent.is_some() || original.offline_staged.is_some())
    }
    /// Same initial DATA carried through genuine source/output enrollment.
    /// This does not supply the still-required actual materialization owner.
    pub fn offline_preparation_intent(&self, deadline: Instant) -> io::Result<Option<&Intent>> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        Ok(original.offline_intent.as_ref().and_then(|attempt| attempt.intent.as_ref())
            .or_else(|| original.offline_staged.as_ref().and_then(|attempt| attempt.complete())))
    }
}

#[cfg(test)]
mod tests;

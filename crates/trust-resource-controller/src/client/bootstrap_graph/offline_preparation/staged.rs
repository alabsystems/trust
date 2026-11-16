//! SAME pinned Root selector sequence. Every reply remains DATA: the actual
//! SourceBound phase and native Host retain their original source/workspace.
use super::*;
use crate::bootstrap_graph::offline_preparation::{
    IntentSelection, ProgramSelection, ProgramSelectionQuery, ProgramSelectionReply,
    ReservedPrograms, StagedIntent, StagedIntentQuery, StagedIntentReply,
};

pub(in crate::client::bootstrap_graph) struct StagedAttempt {
    query: StagedIntentQuery,
    started: Instant,
    deadline: Instant,
    intent: Option<StagedIntent>,
    acknowledged: bool,
    reserved: Option<ReservedPrograms>,
    reservation_retained: bool,
    programs: Option<ProgramSelection>,
    complete: Option<Intent>,
    programs_acknowledged: bool,
    failed: bool,
    carrier: Option<carrier::ProgramsCarrier>,
    programs_in_flight: bool,
}
impl StagedAttempt {
    fn new(query: StagedIntentQuery, deadline: Instant) -> Self {
        Self { query, started: Instant::now(), deadline, intent: None,
            acknowledged: false, reserved: None, reservation_retained: false,
            programs: None, complete: None, programs_acknowledged: false, failed: false, carrier: None, programs_in_flight: false }
    }
    fn binding(&self, key: &Key, queries: &QueryState, deadline: Instant) -> io::Result<()> {
        if self.failed || &self.query.key != key || !queries.offline_reserved {
            return Err(crate::wire::invalid());
        }
        bounded(self.deadline, deadline)?;
        if let Some(carrier) = &self.carrier { carrier.check_current(deadline)?; }
        Ok(())
    }
    pub(in crate::client::bootstrap_graph) fn ready(
        &self, key: &Key, queries: &QueryState, deadline: Instant,
    ) -> io::Result<()> {
        if self.programs_in_flight { return Err(crate::wire::invalid()); }
        self.binding(key, queries, deadline)?;
        if !self.acknowledged || self.intent.is_none() { return Err(crate::wire::invalid()); }
        Ok(())
    }
    pub(in crate::client::bootstrap_graph) fn original_intent(
        &self, key: &Key, queries: &QueryState, deadline: Instant,
    ) -> io::Result<&StagedIntent> {
        self.ready(key, queries, deadline)?;
        self.intent.as_ref().ok_or_else(crate::wire::invalid)
    }
    pub(in crate::client::bootstrap_graph) fn enrolled(
        &self, enrollment: &Enrollment, queries: &QueryState, deadline: Instant,
    ) -> io::Result<()> {
        self.ready(&enrollment.key, queries, deadline)?;
        let intent = self.intent.as_ref().ok_or_else(crate::wire::invalid)?;
        if enrollment.source != intent.selection.source_root
            || enrollment.output != intent.selection.output_root
        { return Err(crate::wire::invalid()); }
        Ok(())
    }
    fn record<T>(&mut self, result: io::Result<T>) -> io::Result<T> {
        if result.is_err() { self.failed = true; }
        result
    }
    fn restrict_remaining(deadline: &mut Instant, started: Instant, remaining: u64) -> io::Result<()> {
        if !matches!(remaining, 1..=crate::bootstrap_graph::offline_preparation::MAX_BUDGET_NS) {
            return Err(crate::wire::invalid());
        }
        let end = started.checked_add(Duration::from_nanos(remaining))
            .ok_or_else(crate::wire::invalid)?;
        *deadline = (*deadline).min(end); // retain even an already expired endpoint
        time(*deadline)
    }
    fn observe_intent(&mut self, reply: StagedIntentReply, started: Instant) -> io::Result<()> {
        let checked = (|| {
            if self.failed || reply.query != self.query
                || self.intent.as_ref().is_some_and(|prior| prior != &reply.intent)
            { return Err(crate::wire::invalid()); }
            self.deadline = self.deadline
                .min(original_deadline(started, reply.remaining_root_ns)?)
                .min(original_deadline(self.started, reply.intent.selection.budget_ns)?);
            self.intent = Some(reply.intent);
            time(self.deadline)
        })();
        self.record(checked)
    }
    fn reservation_query(&self) -> io::Result<ProgramSelectionQuery> {
        let intent = self.intent.as_ref().ok_or_else(crate::wire::invalid)?;
        if !self.acknowledged || self.failed { return Err(crate::wire::invalid()); }
        Ok(ProgramSelectionQuery { key: intent.key.clone() })
    }
    fn observe_reservation(&mut self, reply: ReservedPrograms, started: Instant) -> io::Result<()> {
        let checked = (|| {
            if reply.query != self.reservation_query()?
                || self.reserved.as_ref().is_some_and(|prior|
                    prior.query != reply.query || prior.namespace != reply.namespace)
            { return Err(crate::wire::invalid()); }
            Self::restrict_remaining(&mut self.deadline, started, reply.remaining_root_ns)?;
            self.reserved = Some(reply); // retain before later selector delivery/ACK
            time(self.deadline)
        })();
        self.record(checked)
    }
    fn select(&mut self, selection: &ProgramSelection) -> io::Result<()> {
        let checked = (|| {
            selection.validate()?;
            if self.failed || !self.reservation_retained
                || self.reserved.is_none() || selection.key != self.reservation_query()?.key
                || self.programs.as_ref().is_some_and(|prior| prior != selection)
            { return Err(crate::wire::invalid()); }
            // Freeze before selector send: a lost reply cannot retarget this attempt.
            self.programs = Some(selection.clone());
            Ok(())
        })();
        self.record(checked)
    }
    fn observe_programs(&mut self, reply: ProgramSelectionReply, started: Instant) -> io::Result<()> {
        let checked = (|| {
            if self.failed { return Err(crate::wire::invalid()); }
            let intent = self.intent.as_ref().ok_or_else(crate::wire::invalid)?;
            let reserved = self.reserved.as_ref().ok_or_else(crate::wire::invalid)?;
            if self.programs.as_ref() != Some(&reply.selection)
                || reply.namespace != reserved.namespace || reply.selection.key != intent.key
            { return Err(crate::wire::invalid()); }
            Self::restrict_remaining(&mut self.deadline, started, reply.remaining_root_ns)?;
            let complete = Intent { key: intent.key.clone(), selection: IntentSelection {
                source_root: intent.selection.source_root.clone(),
                output_root: intent.selection.output_root.clone(),
                configured_targo: reply.selection.configured_targo,
                configured_compiler: reply.selection.configured_compiler,
                environment: intent.selection.environment.clone(),
                budget_ns: intent.selection.budget_ns,
            }};
            complete.validate()?;
            if self.complete.as_ref().is_some_and(|prior| prior != &complete) {
                return Err(crate::wire::invalid());
            }
            self.complete = Some(complete); // DATA only, retained before ACK
            time(self.deadline)
        })();
        self.record(checked)
    }
    pub(in crate::client::bootstrap_graph) fn complete(&self) -> Option<&Intent> {
        if self.failed || !self.programs_acknowledged { None } else { self.complete.as_ref() }
    }
}

mod carrier;

#[cfg(test)]
mod tests;

impl Client {
    /// Distinct128 submission/129pull on the SAME authenticated Root. This only
    /// retains original selector DATA; it cannot enroll a source or reserve a
    /// private producer. Original126 and ordinary query/object cannot alias it.
    pub fn bootstrap_staged_offline_preparation_intent(
        &self, support: &mut BootstrapGraphSupport, deadline: Instant,
    ) -> io::Result<StagedIntent> {
        bounded(support.deadline, deadline)?;
        support.queries.enrollment_allowed()?;
        if !Arc::ptr_eq(&support.pin, &self.host) { return Err(crate::wire::invalid()); }
        self.host.validate(deadline)?;
        live(&support.context, deadline)?;
        if support.offline_staged.is_none() {
            let query = StagedIntentQuery { key: support.key.clone() };
            query.encode()?;
            support.queries.reserve_offline()?;
            support.offline_staged = Some(StagedAttempt::new(query, support.deadline));
        }
        let attempt = support.offline_staged.as_mut().ok_or_else(crate::wire::invalid)?;
        let at = deadline.min(attempt.deadline);
        attempt.binding(&support.key, &support.queries, at)?;
        let started = Instant::now();
        let host = self.host.connect(at)?;
        let mut channel = Channel::new(host.stream().try_clone()?)?;
        let result = (|| {
            host.revalidate(at)?;
            channel.send(&attempt.query.hello()?, at)?;
            channel.send(&attempt.query.encode()?, at)?;
            let reply = match StagedIntentReply::decode(&channel.receive(at)?, &attempt.query) {
                Ok(reply) => reply,
                Err(error) => { attempt.failed = true; return Err(error); }
            };
            attempt.observe_intent(reply, started)?;
            support.deadline = support.deadline.min(attempt.deadline);
            let at = at.min(attempt.deadline);
            preparation::finish_reply(&mut channel, at, || {
                host.revalidate(at)?; self.host.validate(at)?;
                attempt.binding(&support.key, &support.queries, at)?;
                live(&support.context, at)
            })?;
            host.revalidate(at)?; live(&support.context, at)?;
            attempt.acknowledged = true;
            attempt.ready(&support.key, &support.queries, at)?;
            attempt.intent.clone().ok_or_else(crate::wire::invalid)
        })();
        if result.is_err() { channel.poison(); }
        result
    }
}
impl BootstrapGraphSupport {
    pub fn staged_offline_preparation_intent(&self, deadline: Instant) -> io::Result<Option<&StagedIntent>> {
        let Some(attempt) = &self.offline_staged else { return Ok(None) };
        attempt.ready(&self.key, &self.queries, deadline)?;
        Ok(attempt.intent.as_ref())
    }
}

impl SourceBoundBootstrapGraph {
    /// Retained reservation DATA on the SAME still-open authenticated carrier.
    /// Only the later final program reply has an EOF/ACK boundary.
    pub fn reserved_offline_preparation_programs(
        &self, deadline: Instant,
    ) -> io::Result<Option<&ReservedPrograms>> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        let Some(attempt) = &original.offline_staged else { return Ok(None) };
        if !attempt.reservation_retained { return Err(crate::wire::invalid()); }
        Ok(attempt.reserved.as_ref())
    }
    fn refuse_program_carrier(&mut self) {
        if let Some(attempt) = self.original.as_mut().and_then(|original| original.offline_staged.as_mut()) {
            attempt.failed = true;
            if let Some(carrier) = &mut attempt.carrier { carrier.poison(); }
        }
    }

    /// Observe the actual Host reservation only after original source and
    /// materialization acceptance. Names/time remain DATA. Retain the SAME
    /// original Host and stream before any fallible clone/send/postcheck.
    pub fn reserve_offline_preparation_programs(
        &mut self, client: &Client, deadline: Instant,
    ) -> io::Result<ReservedPrograms> {
        let result = self.reserve_program_carrier(client, deadline);
        if result.is_err() { self.refuse_program_carrier(); }
        result
    }
    fn reserve_program_carrier(
        &mut self, client: &Client, deadline: Instant,
    ) -> io::Result<ReservedPrograms> {
        self.require_preparation_output(deadline)?;
        let original = self.original.as_mut().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        original.deadline = original.deadline.min(deadline);
        if self.materialization.is_none() || !self.configuration.is_empty()
            || !Arc::ptr_eq(&original.pin, &client.host)
        { return Err(crate::wire::invalid()); }
        let attempt = original.offline_staged.as_mut().ok_or_else(crate::wire::invalid)?;
        attempt.deadline = attempt.deadline.min(original.deadline);
        let query = attempt.reservation_query()?;
        let at = deadline.min(attempt.deadline);
        attempt.binding(&original.request.key, &original.queries, at)?;
        if attempt.reservation_retained {
            // Idempotent observation reuses the already held stream and child;
            // it sends no new query and never resets the original endpoint.
            return attempt.reserved.clone().ok_or_else(crate::wire::invalid);
        }
        if attempt.carrier.is_some() { return Err(crate::wire::invalid()); }
        let host = client.host.connect(at)?;
        attempt.carrier = Some(carrier::ProgramsCarrier::new(host, at));
        attempt.carrier.as_mut().expect("same original carrier").open(at)?;
        // Before moving the unique guard locally, revoke public access. An
        // unwind retains the guard's ManuallyDrop descriptions and this sticky
        // in-flight restriction; no alias can start a replacement connection.
        attempt.programs_in_flight = true;
        let mut carrier = attempt.carrier.take().expect("same original carrier");
        let started = Instant::now();
        let result = (|| {
            let (host, channel) = carrier.parts(at)?;
            host.revalidate(at)?;
            let reply = carrier::reserve(channel, &query, at)?;
            attempt.observe_reservation(reply, started)?;
            let at = at.min(attempt.deadline);
            carrier::reservation_boundary(channel, at, || {
                host.revalidate(at)?; client.host.validate(at)?;
                original.original.revalidate(at)?;
                attempt.binding(&original.request.key, &original.queries, at)?;
                live(&original.context, at)
            })?;
            host.revalidate(at)?; live(&original.context, at)?;
            attempt.reservation_retained = true;
            attempt.reserved.clone().ok_or_else(crate::wire::invalid)
        })();
        carrier.restrict(attempt.deadline);
        attempt.carrier = Some(carrier); // errors retain the SAME actual guard
        attempt.programs_in_flight = false;
        original.deadline = original.deadline.min(attempt.deadline);
        result?;
        original.check(original.deadline)?;
        original.offline_staged.as_ref().and_then(|attempt| attempt.reserved.clone())
            .ok_or_else(crate::wire::invalid)
    }

    /// Freeze exact program spelling, then send it on the SAME still-held
    /// reservation stream. Only this final reply closes via physical EOF/ACK;
    /// no reconnect, second HELLO, fresh child or new original budget occurs.
    pub fn finalize_offline_preparation_programs(
        &mut self, client: &Client, selection: ProgramSelection, deadline: Instant,
    ) -> io::Result<Intent> {
        let result = self.finalize_program_carrier(client, selection, deadline);
        if result.is_err() { self.refuse_program_carrier(); }
        result
    }
    fn finalize_program_carrier(
        &mut self, client: &Client, selection: ProgramSelection, deadline: Instant,
    ) -> io::Result<Intent> {
        let original = self.original.as_mut().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        original.deadline = original.deadline.min(deadline);
        if self.materialization.is_none() || !self.configuration.is_empty()
            || !Arc::ptr_eq(&original.pin, &client.host)
        { return Err(crate::wire::invalid()); }
        let attempt = original.offline_staged.as_mut().ok_or_else(crate::wire::invalid)?;
        attempt.deadline = attempt.deadline.min(original.deadline);
        attempt.select(&selection)?; // immutable selector before any I/O
        let at = deadline.min(attempt.deadline);
        attempt.binding(&original.request.key, &original.queries, at)?;
        if attempt.programs_acknowledged {
            return attempt.complete().cloned().ok_or_else(crate::wire::invalid);
        }
        attempt.programs_in_flight = true;
        let mut carrier = attempt.carrier.take().ok_or_else(crate::wire::invalid)?;
        let started = Instant::now();
        let result = (|| {
            let (host, channel) = carrier.parts(at)?;
            host.revalidate(at)?;
            let reply = carrier::select(channel, &selection, at)?;
            attempt.observe_programs(reply, started)?;
            let at = at.min(attempt.deadline);
            preparation::finish_reply(channel, at, || {
                host.revalidate(at)?; client.host.validate(at)?;
                original.original.revalidate(at)?;
                attempt.binding(&original.request.key, &original.queries, at)?;
                live(&original.context, at)
            })?;
            host.revalidate(at)?; live(&original.context, at)?;
            attempt.programs_acknowledged = true;
            attempt.complete().cloned().ok_or_else(crate::wire::invalid)
        })();
        carrier.restrict(attempt.deadline);
        if result.is_ok() { carrier.closed_reply(); }
        attempt.carrier = Some(carrier);
        attempt.programs_in_flight = false;
        original.deadline = original.deadline.min(attempt.deadline);
        result?;
        original.check(original.deadline)?;
        original.offline_staged.as_ref().and_then(|attempt| attempt.complete().cloned())
            .ok_or_else(crate::wire::invalid)
    }

    /// Final selectors only after physical reply EOF and native carrier ACK.
    /// It creates no source/materialization/configuration or semantic Seed owner.
    pub fn offline_preparation_intent(&self, deadline: Instant) -> io::Result<Option<&Intent>> {
        let original = self.original.as_ref().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        Ok(original.offline_intent.as_ref().and_then(|attempt| attempt.intent.as_ref())
            .or_else(|| original.offline_staged.as_ref().and_then(|attempt| attempt.complete())))
    }
}

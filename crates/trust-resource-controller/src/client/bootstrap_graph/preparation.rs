//! Reconnect to the same resident attempt through the SAME pinned original Host.
//! A failed exchange retains the original graph and immutable attempt/endpoint;
//! observations cannot retire it or manufacture a prepared input/SDK owner.
use super::*;
use crate::bootstrap_graph::preparation::{Observation, Request};

/// Retain the same native peer through physical reply EOF and every caller
/// validation. ACK only ends this reply lifetime; it grants no work or closure.
pub(super) fn finish_reply(
    channel: &mut Channel,
    deadline: Instant,
    validate: impl FnOnce() -> io::Result<()>,
) -> io::Result<()> {
    crate::runtime_input_retention::transport::require_reply_eof(channel, deadline)?;
    validate()?;
    time(deadline)?;
    channel.send(&[1], deadline)
}

mod work;
pub use work::{InputWorkClosed, ResidentDependencyInputs};

#[cfg(test)]
#[path = "preparation/reply_tests.rs"]
mod reply_tests;

pub(super) struct Attempt {
    request: Request,
    deadline: Instant,
    observation: Option<Observation>,
    opened: bool,
}

impl Attempt {
    fn restrictions(
        &self,
        key: &Key,
        queries: &QueryState,
        deadline: Instant,
    ) -> io::Result<Instant> {
        if &self.request.key.graph != key || queries.active != Some(self.request.key.sequence) {
            return Err(crate::wire::invalid());
        }
        let deadline = deadline.min(self.deadline);
        time(deadline)?;
        Ok(deadline)
    }
    pub(super) fn revalidate(&self, original: &Connection, deadline: Instant) -> io::Result<()> {
        original.check(self.restrictions(&original.request.key, &original.queries, deadline)?)
    }
}

impl OutputBoundBootstrapGraph {
    /// Begin once, or observe the exact same originally submitted operation.
    /// A lost ACK may reconnect with this request; replacing its nonce, mode,
    /// sequence or budget refuses. Neither reconnect nor I/O deadline extends
    /// the original endpoint. This returns progress DATA, never completion or
    /// readiness authority, and keeps all actual graph owners in this value.
    pub fn dependency_inputs(
        &mut self,
        client: &Client,
        request: Request,
        deadline: Instant,
    ) -> io::Result<Observation> {
        request.validate()?;
        let original = self.original.as_mut().ok_or_else(crate::wire::invalid)?;
        original.check(deadline)?;
        if request.key.graph != original.request.key || !Arc::ptr_eq(&original.pin, &client.host) {
            return Err(crate::wire::invalid());
        }
        if let Some(attempt) = &self.preparation {
            if attempt.request != request {
                return Err(crate::wire::invalid());
            }
            time(attempt.deadline)?;
        } else {
            original.queries.check(request.key.sequence)?;
            let endpoint = Instant::now()
                .checked_add(Duration::from_nanos(request.timeout_ns))
                .ok_or_else(crate::wire::invalid)?
                .min(original.deadline);
            time(endpoint)?;
            // Record BEFORE connect/send. Unknown delivery cannot create a new
            // nonce, repeat the admission, clear the original query or reset time.
            original.queries.begin()?;
            self.preparation = Some(Attempt {
                request: request.clone(),
                deadline: endpoint,
                observation: None,
                opened: false,
            });
        }
        let attempt = self.preparation.as_mut().expect("same original preparation attempt");
        let at = deadline.min(attempt.deadline);
        time(at)?;
        let host = client.host.connect(at)?;
        let mut channel = Channel::new(host.stream().try_clone()?)?;
        host.revalidate(at)?;
        channel.send(&request.hello()?, at)?;
        channel.send(&request.encode()?, at)?;
        let observation = Observation::decode(&channel.receive(at)?)?;
        finish_reply(&mut channel, at, || {
            host.revalidate(at)?;
            original.check(at)?;
            if observation.request != attempt.request
                || attempt.observation.as_ref().is_some_and(|previous| {
                    observation.revision < previous.revision
                        || (observation.revision == previous.revision && &observation != previous)
                })
            {
                return Err(crate::wire::invalid());
            }
            Ok(())
        })?;
        attempt.observation = Some(observation.clone());
        Ok(observation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn same_reserved_attempt_revalidates_without_clearing_other_operation_restrictions() {
        let request = Request {
            key: crate::bootstrap_graph::query::tests::request().key,
            mode: crate::bootstrap_graph::preparation::Mode::Check,
            timeout_ns: 1_000_000_000,
        };
        let deadline = Instant::now() + Duration::from_secs(30);
        let attempt =
            Attempt { request: request.clone(), deadline, observation: None, opened: false };
        let mut actual = QueryState::new();
        assert!(attempt.restrictions(&request.key.graph, &actual, deadline).is_err());
        actual.begin().unwrap();
        assert_eq!(
            attempt
                .restrictions(&request.key.graph, &actual, deadline + Duration::from_secs(30))
                .unwrap(),
            deadline
        );
        assert!(
            actual.enrollment_allowed().is_err(),
            "observation must not clear the original reservation"
        );
        assert!(
            actual.check(2).is_err(),
            "no ordinary query may dispatch while resident inputs own the graph"
        );
        actual.active = Some(2);
        assert!(attempt.restrictions(&request.key.graph, &actual, deadline).is_err());
        actual.active = Some(request.key.sequence);
        assert!(
            attempt
                .restrictions(&request.key.graph, &actual, Instant::now() - Duration::from_nanos(1))
                .is_err()
        );
    }
}

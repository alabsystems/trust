//! One bounded source request on the original custodied cache/source carrier.
//!139 accepts pending work DATA; it never closes that work or enables Config.
use std::io;
use std::os::fd::BorrowedFd;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};

use super::{SourceBoundBootstrapGraph, bounded, live, time};
use crate::bootstrap_graph::offline_preparation::{
    ArchiveCandidate, Request, SourceCapture, SourceCaptureAccepted,
};
use crate::bootstrap_graph::transport;
use crate::descriptors::AdmittedDirectory;
use crate::{Channel, ContextReply};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Pending,
    Bound,
    Sent,
    Accepted,
    Failed,
}
pub(super) struct Attempt {
    candidates: Vec<ArchiveCandidate>,
    selection: Option<SourceCapture>,
    digest: Option<[u8; 32]>,
    home: Option<Arc<AdmittedDirectory>>,
    first_send: Option<Instant>,
    end: Instant,
    phase: Phase,
}
impl Attempt {
    fn retain(candidates: Vec<ArchiveCandidate>, end: Instant) -> Self {
        Self {
            candidates,
            selection: None,
            digest: None,
            home: None,
            first_send: None,
            end,
            phase: Phase::Pending,
        }
    }
    fn bind(
        &mut self,
        request: Request,
        home: Arc<AdmittedDirectory>,
        original_cache_end: Instant,
    ) -> io::Result<()> {
        let result = (|| {
            if self.phase != Phase::Pending {
                return Err(crate::wire::invalid());
            }
            // SAME actual Custodied137 producer, retained before content checks.
            self.home = Some(home);
            self.end = self.end.min(original_cache_end);
            self.selection =
                Some(SourceCapture { request, candidates: std::mem::take(&mut self.candidates) });
            let selection = self.selection.as_ref().ok_or_else(crate::wire::invalid)?;
            let bytes = selection.encode()?;
            self.digest = Some(Sha256::digest(&bytes).into());
            self.home.as_ref().ok_or_else(crate::wire::invalid)?.validate(self.end)?;
            time(self.end)?;
            self.phase = Phase::Bound;
            Ok(())
        })();
        if result.is_err() {
            self.phase = Phase::Failed;
        }
        result
    }
    fn observe(
        &mut self,
        bytes: &[u8],
        context: &ContextReply,
    ) -> io::Result<SourceCaptureAccepted> {
        let result = (|| {
            if self.phase != Phase::Sent {
                return Err(crate::wire::invalid());
            }
            let selection = self.selection.as_ref().ok_or_else(crate::wire::invalid)?;
            let accepted = SourceCaptureAccepted::decode(
                bytes,
                selection,
                self.digest.ok_or_else(crate::wire::invalid)?,
            )?;
            if accepted.context != *context {
                return Err(crate::wire::invalid());
            }
            // Preserve the old/cache endpoint. Anchor the NEW remaining value
            // BEFORE this request's first send, never at receipt or a retry.
            let observed_end = self
                .first_send
                .ok_or_else(crate::wire::invalid)?
                .checked_add(Duration::from_nanos(accepted.remaining_input_ns))
                .ok_or_else(crate::wire::invalid)?;
            self.end = self.end.min(observed_end);
            time(self.end)?;
            self.home.as_ref().ok_or_else(crate::wire::invalid)?.validate(self.end)?;
            self.phase = Phase::Accepted;
            Ok(accepted)
        })();
        if result.is_err() {
            self.phase = Phase::Failed;
        }
        result
    }
    pub(super) fn check(&self, deadline: Instant) -> io::Result<()> {
        if self.phase != Phase::Accepted {
            return Err(crate::wire::invalid());
        }
        bounded(self.end, deadline)?;
        self.home.as_ref().ok_or_else(crate::wire::invalid)?.validate(deadline)
    }
    pub(super) fn configuration_ready(&self) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "accepted source capture has no configured completion",
        ))
    }
}

struct Exchange<'a> {
    channel: &'a mut Channel,
    attempt: &'a mut Attempt,
    returned: bool,
}
impl Drop for Exchange<'_> {
    fn drop(&mut self) {
        if !self.returned {
            self.attempt.phase = Phase::Failed;
            self.channel.poison();
        }
    }
}
fn exchange(
    channel: &mut Channel,
    attempt: &mut Attempt,
    context: &ContextReply,
    mut check: impl FnMut(Instant) -> io::Result<()>,
) -> io::Result<SourceCaptureAccepted> {
    let mut held = Exchange { channel, attempt, returned: false };
    let result = (|| {
        if held.attempt.phase != Phase::Bound {
            return Err(crate::wire::invalid());
        }
        time(held.attempt.end)?;
        check(held.attempt.end)?;
        let bytes = held.attempt.selection.as_ref().ok_or_else(crate::wire::invalid)?.encode()?;
        held.attempt.first_send = Some(Instant::now());
        held.attempt.phase = Phase::Sent; // BEFORE even a failed/unknown send
        held.channel.send(&bytes, held.attempt.end)?;
        let reply = held.channel.receive(held.attempt.end)?;
        let accepted = held.attempt.observe(&reply, context)?;
        check(held.attempt.end)?;
        held.attempt.check(held.attempt.end)?;
        Ok(accepted)
    })();
    held.returned = result.is_ok();
    result // Keep SAME open channel; no EOF/ACK/reconnect or completed work.
}

struct Original<'a> {
    graph: &'a mut SourceBoundBootstrapGraph,
    returned: bool,
}
impl Drop for Original<'_> {
    fn drop(&mut self) {
        if !self.returned {
            if let Some(attempt) = &mut self.graph.preparation_source {
                attempt.phase = Phase::Failed;
            }
            if let Some(original) = &mut self.graph.original {
                original.channel.poison();
            }
        }
    }
}
impl Original<'_> {
    fn send(
        &mut self,
        source: &[BorrowedFd<'_>; 4],
        deadline: Instant,
    ) -> io::Result<SourceCaptureAccepted> {
        self.graph.require_preparation_output(deadline)?;
        let (request, home, cache_end) = self
            .graph
            .preparation_cache
            .as_ref()
            .ok_or_else(crate::wire::invalid)?
            .source_binding(deadline)?;
        let original = self.graph.original.as_mut().ok_or_else(crate::wire::invalid)?;
        bounded(original.deadline, deadline)?;
        original.deadline = original.deadline.min(deadline).min(cache_end);
        original.check(original.deadline)?;
        if !self.graph.configuration.is_empty() {
            return Err(crate::wire::invalid());
        }
        let intent = original
            .offline_staged
            .as_ref()
            .and_then(|staged| staged.complete())
            .ok_or_else(crate::wire::invalid)?;
        intent.matches_request(&request)?;
        if request.key.graph != original.request.key {
            return Err(crate::wire::invalid());
        }
        transport::check_source(&self.graph.source, source, original.deadline)?;
        let attempt = self.graph.preparation_source.as_mut().ok_or_else(crate::wire::invalid)?;
        attempt.end = attempt.end.min(original.deadline);
        attempt.bind(request, home, cache_end)?;
        let host = &original.original;
        let pin = &original.pin;
        let context = &original.context;
        let accepted = exchange(&mut original.channel, attempt, context, |end| {
            host.revalidate(end)?;
            pin.validate(end)?;
            live(context, end)?;
            transport::check_source(&self.graph.source, source, end)
        });
        original.deadline = original.deadline.min(attempt.end); // even on refusal
        let accepted = accepted?;
        original.check(original.deadline)?;
        attempt.check(original.deadline)?;
        Ok(accepted)
    }
}
impl SourceBoundBootstrapGraph {
    /// Caller supplies bounded candidate DATA only. The original114 and SAME
    /// physical directory come exclusively from the actual Custodied137 state.
    ///139 accepts pending fixed work, not its result or any native/Seed owner.
    ///
    /// # Safety
    /// `source` borrows the SAME retained original SourceOffer descriptions,
    /// with its original source/scope/manager checks around this ENTIRE call,
    /// including errors/unwind. The owning graph must retain all real source,
    /// output, cache and protected-scope resources until actual native closure.
    pub unsafe fn capture_original_preparation_source(
        &mut self,
        candidates: Vec<ArchiveCandidate>,
        source: &[BorrowedFd<'_>; 4],
        deadline: Instant,
    ) -> io::Result<SourceCaptureAccepted> {
        if self.preparation_source.is_some() {
            if let Some(attempt) = &mut self.preparation_source {
                attempt.phase = Phase::Failed;
            }
            if let Some(original) = &mut self.original {
                original.channel.poison();
            }
            return Err(crate::wire::invalid());
        }
        // Retain even malformed initial candidate DATA before fallible checks.
        self.preparation_source = Some(Attempt::retain(candidates, deadline));
        let mut held = Original { graph: self, returned: false };
        let result = held.send(source, deadline);
        held.returned = result.is_ok();
        result
    }
}

#[cfg(test)]
mod tests;

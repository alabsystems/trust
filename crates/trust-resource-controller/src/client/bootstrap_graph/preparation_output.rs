//! Intermediate physical custody on the SAME source channel. No EOF, final
//! output/configuration transition, native completion or Seed is supplied.
use std::io;
use std::os::fd::BorrowedFd;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};

use super::{SourceBoundBootstrapGraph, bounded, live, time};
use crate::bootstrap_graph::offline_preparation::{
    PreparationOutputAttachment, PreparationOutputReply,
};
use crate::bootstrap_graph::{OutputAttachment, transport};
use crate::{Channel, ContextReply};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Requested,
    Prepared,
    Custodied,
    Failed,
}
pub(super) struct Attempt {
    request: PreparationOutputAttachment,
    digest: [u8; 32],
    started: Instant,
    deadline: Instant,
    phase: Phase,
}
impl Attempt {
    fn new(request: PreparationOutputAttachment, deadline: Instant) -> io::Result<Self> {
        time(deadline)?;
        request.validate()?;
        let digest = Sha256::digest(request.binding_preimage()?).into();
        Ok(Self { request, digest, started: Instant::now(), deadline, phase: Phase::Requested })
    }
    fn observe(&mut self, bytes: &[u8], context: &ContextReply) -> io::Result<()> {
        let result = (|| {
            let reply = PreparationOutputReply::decode(bytes, &self.request, self.digest)?;
            let (remaining, next) = match reply {
                PreparationOutputReply::Prepared {
                    context: observed, remaining_input_ns, ..
                } if observed == *context && self.phase == Phase::Requested => {
                    (remaining_input_ns, Phase::Prepared)
                }
                PreparationOutputReply::Custodied {
                    context: observed, remaining_input_ns, ..
                } if observed == *context && self.phase == Phase::Prepared => {
                    (remaining_input_ns, Phase::Custodied)
                }
                _ => return Err(crate::wire::invalid()),
            };
            // Retain a received restrictive endpoint even when it has already
            // expired; the following refusal cannot restore the older bound.
            let observed_end = self
                .started
                .checked_add(Duration::from_nanos(remaining))
                .ok_or_else(crate::wire::invalid)?;
            self.deadline = self.deadline.min(observed_end);
            time(self.deadline)?;
            self.phase = next;
            Ok(())
        })();
        if result.is_err() {
            self.phase = Phase::Failed;
        }
        result
    }
    pub(super) fn check(&self, deadline: Instant) -> io::Result<()> {
        if self.phase != Phase::Custodied {
            return Err(crate::wire::invalid());
        }
        bounded(self.deadline, deadline)
    }
    pub(super) fn original(&self, deadline: Instant) -> io::Result<&PreparationOutputAttachment> {
        self.check(deadline)?;
        Ok(&self.request)
    }
}

/// The actual production I/O path, independently exercised with native socket
/// and descriptor controls. Its packets/check callback construct no owner.
fn exchange(
    channel: &mut Channel,
    attempt: &mut Attempt,
    context: &ContextReply,
    files: &[BorrowedFd<'_>; 2],
    mut check: impl FnMut(Instant) -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        if attempt.phase != Phase::Requested {
            return Err(crate::wire::invalid());
        }
        time(attempt.deadline)?;
        check(attempt.deadline)?;
        channel.send(&attempt.request.encode()?, attempt.deadline)?;
        attempt.observe(&channel.receive(attempt.deadline)?, context)?;
        check(attempt.deadline)?;
        transport::send_preparation_output(
            channel,
            &attempt.request,
            files,
            attempt.deadline,
            || check(attempt.deadline),
        )?;
        attempt.observe(&channel.receive(attempt.deadline)?, context)?;
        check(attempt.deadline)?;
        attempt.check(attempt.deadline)
    })();
    if result.is_err() {
        attempt.phase = Phase::Failed;
        channel.poison();
    }
    result // SAME channel remains open for later source/configuration work.
}

impl SourceBoundBootstrapGraph {
    /// Negative prerequisite only. Complete126 and ordinary query/object do
    /// not acquire the distinct early-output purpose through this predicate.
    pub(super) fn require_preparation_output(&self, deadline: Instant) -> io::Result<()> {
        if self.original.as_ref().is_some_and(|original| original.offline_staged.is_some()) {
            self.preparation_output.as_ref().ok_or_else(crate::wire::invalid)?.check(deadline)?;
        }
        Ok(())
    }

    /// Lend the SAME acquired OutputLock before the first Configuration byte.
    /// The accepted reply is physical custody DATA, never configured output or
    /// native closure. Uncertain delivery is one-use and cannot be resent.
    ///
    /// # Safety
    /// The actual original coordinator must already retain the SAME withheld
    /// Source Manager, SourceOffer, output guard and protected scope before
    /// entering, through every failure/unwind and actual native retirement.
    /// `source` and `output` borrow those originals; the guard and every loan
    /// remain close-only. All issuer guards must bookend the whole
    /// exchange. Paths, reopened files, metadata and ACK cannot supply custody.
    pub unsafe fn attach_original_preparation_output(
        &mut self,
        physical: OutputAttachment,
        source: &[BorrowedFd<'_>; 4],
        output: &[BorrowedFd<'_>; 2],
        deadline: Instant,
    ) -> io::Result<()> {
        // Restriction only, installed even before fallible preflight. A local
        // error/unwind cannot return this phase to an unused output route.
        if self.preparation_output_started {
            if let Some(attempt) = &mut self.preparation_output {
                attempt.phase = Phase::Failed;
            }
            if let Some(original) = &mut self.original {
                original.channel.poison();
            }
            return Err(crate::wire::invalid());
        }
        self.preparation_output_started = true;
        let original = self.original.as_mut().ok_or_else(crate::wire::invalid)?;
        let request = (|| {
            bounded(original.deadline, deadline)?;
            original.deadline = original.deadline.min(deadline);
            original.queries.enrollment_allowed()?;
            if self.preparation_output.is_some()
                || !self.configuration.is_empty()
                || physical.key != original.request.key
            {
                return Err(crate::wire::invalid());
            }
            let staged = original.offline_staged.as_ref().ok_or_else(crate::wire::invalid)?;
            let intent =
                staged.original_intent(&original.request.key, &original.queries, deadline)?;
            let materialization = self.materialization.as_ref().ok_or_else(crate::wire::invalid)?;
            materialization.check(self.source.source_directory, Some(&physical))?;
            transport::check_source(&self.source, source, deadline)?;
            transport::check_output(&physical, output)?;
            original.check(deadline)?;
            Ok(PreparationOutputAttachment {
                key: intent.key.clone(),
                root: physical.root,
                lock: physical.lock,
            })
        })();
        let request = match request {
            Ok(request) => request,
            Err(error) => {
                original.channel.poison();
                return Err(error);
            }
        };
        // Retain immutable attempt and endpoint BEFORE request encoding/send.
        // Same original channel remains in self on every error and unwind.
        self.preparation_output = Some(match Attempt::new(request, deadline) {
            Ok(attempt) => attempt,
            Err(error) => {
                original.channel.poison();
                return Err(error);
            }
        });
        let attempt = self.preparation_output.as_mut().expect("same retained output attempt");
        let host = &original.original;
        let pin = &original.pin;
        let context = &original.context;
        let result = exchange(&mut original.channel, attempt, context, output, |end| {
            host.revalidate(end)?;
            pin.validate(end)?;
            live(context, end)?;
            transport::check_source(&self.source, source, end)?;
            transport::check_output(&physical, output)
        });
        original.deadline = original.deadline.min(attempt.deadline);
        let result = result.and_then(|()| original.check(original.deadline));
        if result.is_err() {
            attempt.phase = Phase::Failed;
            original.channel.poison();
        }
        result
    }
}

#[cfg(test)]
mod tests;

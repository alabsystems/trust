//! Physical caller-directory handoff on the SAME original source channel.
//! Only the native receiver issues its real SourceCacheGuard. These packets,
//! the retained directory and their accepted equality do not create that role.
use std::io;
use std::os::unix::ffi::OsStrExt as _;
use std::sync::Arc;
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};

use super::{SourceBoundBootstrapGraph, bounded, live, time};
use crate::bootstrap_graph::offline_preparation::{PreparationCacheReply, Request};
use crate::bootstrap_graph::transport;
use crate::descriptors::AdmittedDirectory;
use crate::{Channel, ContextReply};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Pending,
    Requested,
    Prepared,
    Custodied,
    Failed,
}
pub(super) struct Attempt {
    home: Arc<AdmittedDirectory>,
    request: Option<Request>,
    digest: Option<[u8; 32]>,
    started: Instant,
    end: Instant,
    phase: Phase,
}
impl Attempt {
    fn retain(home: Arc<AdmittedDirectory>, end: Instant) -> Self {
        Self {
            home,
            request: None,
            digest: None,
            started: Instant::now(),
            end,
            phase: Phase::Pending,
        }
    }
    fn freeze(&mut self, request: Request) -> io::Result<()> {
        if self.phase != Phase::Pending
            || request.cargo_home != self.home.path().as_os_str().as_bytes()
        {
            return Err(crate::wire::invalid());
        }
        request.validate()?;
        self.end = self.end.min(
            self.started
                .checked_add(Duration::from_nanos(request.budget_ns))
                .ok_or_else(crate::wire::invalid)?,
        );
        self.digest = Some(Sha256::digest(request.binding_preimage()?).into());
        self.request = Some(request); // immutable original114 before any send
        self.phase = Phase::Requested;
        self.home.validate(self.end)?;
        time(self.end)
    }
    fn observe(&mut self, bytes: &[u8], context: &ContextReply) -> io::Result<()> {
        let result = (|| {
            let original = self.request.as_ref().ok_or_else(crate::wire::invalid)?;
            let reply = PreparationCacheReply::decode(
                bytes,
                original,
                self.digest.ok_or_else(crate::wire::invalid)?,
            )?;
            let (remaining, next) = match reply {
                PreparationCacheReply::Prepared {
                    context: observed, remaining_input_ns, ..
                } if observed == *context && self.phase == Phase::Requested => {
                    (remaining_input_ns, Phase::Prepared)
                }
                PreparationCacheReply::Custodied {
                    context: observed, remaining_input_ns, ..
                } if observed == *context && self.phase == Phase::Prepared => {
                    (remaining_input_ns, Phase::Custodied)
                }
                _ => return Err(crate::wire::invalid()),
            };
            self.end = self.end.min(
                self.started
                    .checked_add(Duration::from_nanos(remaining))
                    .ok_or_else(crate::wire::invalid)?,
            );
            time(self.end)?;
            self.home.validate(self.end)?;
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
        bounded(self.end, deadline)?;
        self.home.validate(deadline)
    }
    pub(super) fn source_binding(
        &self,
        deadline: Instant,
    ) -> io::Result<(Request, Arc<AdmittedDirectory>, Instant)> {
        self.check(deadline)?;
        Ok((
            self.request.clone().ok_or_else(crate::wire::invalid)?,
            Arc::clone(&self.home),
            self.end,
        ))
    }
}

fn exchange(
    channel: &mut Channel,
    attempt: &mut Attempt,
    context: &ContextReply,
    mut check: impl FnMut(Instant) -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        if attempt.phase != Phase::Requested {
            return Err(crate::wire::invalid());
        }
        check(attempt.end)?;
        let request = attempt.request.as_ref().ok_or_else(crate::wire::invalid)?;
        channel.send(&request.encode()?, attempt.end)?;
        attempt.observe(&channel.receive(attempt.end)?, context)?;
        check(attempt.end)?;
        transport::send_preparation_cache_directory(
            channel,
            attempt.home.path(),
            attempt.home.descriptor(attempt.end)?,
            attempt.end,
            || check(attempt.end),
        )?;
        attempt.observe(&channel.receive(attempt.end)?, context)?;
        check(attempt.end)?;
        attempt.check(attempt.end)
    })();
    if result.is_err() {
        attempt.phase = Phase::Failed;
        channel.poison();
    }
    result // intermediate custody: no EOF, write shutdown, final ACK or reconnect
}

impl SourceBoundBootstrapGraph {
    pub(super) fn require_preparation_cache(&self, deadline: Instant) -> io::Result<()> {
        if self.original.as_ref().is_some_and(|original| original.offline_staged.is_some()) {
            self.preparation_cache.as_ref().ok_or_else(crate::wire::invalid)?.check(deadline)?;
        }
        Ok(())
    }

    /// Freeze canonical114 from this actual staged source/output/Root before
    /// offering the caller context's SAME readonly directory. A successful137
    /// is equality/physical-custody DATA, never a transferable cache-lock owner.
    ///
    /// # Safety
    /// `home` must be the directory actually selected by the original Targo
    /// GlobalContext, with its full original environment/cwd association and
    /// all pre-Config checks retained by the trusted runtime adapter. The SAME
    /// original SourceOffer lends `source`; its real owner and this physical
    /// producer must remain retained through every error/unwind and native
    /// retirement. Arbitrary paths, DTOs or observer success cannot supply them.
    /// The runtime veto checks only its retained context and cannot substitute
    /// for any actual original owner or reenter the locked caller graph.
    pub unsafe fn attach_original_preparation_cache(
        &mut self,
        home: Arc<AdmittedDirectory>,
        source: &[std::os::fd::BorrowedFd<'_>; 4],
        deadline: Instant,
        mut runtime_current: impl FnMut() -> io::Result<()>,
    ) -> io::Result<Request> {
        if self.preparation_cache.is_some() {
            if let Some(attempt) = &mut self.preparation_cache {
                attempt.phase = Phase::Failed;
            }
            if let Some(original) = &mut self.original {
                original.channel.poison();
            }
            return Err(crate::wire::invalid());
        }
        // Retain the exact producer before ANY fallible owner/preflight check.
        self.preparation_cache = Some(Attempt::retain(home, deadline));
        let result = (|| {
            self.require_preparation_output(deadline)?;
            let original = self.original.as_mut().ok_or_else(crate::wire::invalid)?;
            bounded(original.deadline, deadline)?;
            original.deadline = original.deadline.min(deadline);
            original.check(deadline)?;
            runtime_current()?; // veto only; this callback creates no owner
            if !self.configuration.is_empty() {
                return Err(crate::wire::invalid());
            }
            let intent = original
                .offline_staged
                .as_ref()
                .and_then(|staged| staged.complete())
                .ok_or_else(crate::wire::invalid)?;
            let output = self
                .preparation_output
                .as_ref()
                .ok_or_else(crate::wire::invalid)?
                .original(deadline)?;
            if intent.key != output.key {
                return Err(crate::wire::invalid());
            }
            let attempt =
                self.preparation_cache.as_mut().expect("same retained physical caller directory");
            let sdk = original.context.context.sdk.as_ref().ok_or_else(crate::wire::invalid)?;
            let remaining =
                deadline.checked_duration_since(Instant::now()).ok_or(io::ErrorKind::TimedOut)?;
            let request = Request {
                key: intent.key.clone(),
                gnu: original.request.gnu.clone(),
                control_sdk_root: sdk.execution.clone(),
                source_root: original.request.source.clone(),
                source_directory: self.source.source_directory,
                output_root: original.request.output.clone(),
                output_directory: output.root,
                output_lock: output.lock,
                configured_targo: intent.selection.configured_targo.clone(),
                configured_compiler: intent.selection.configured_compiler.clone(),
                cargo_home: attempt.home.path().as_os_str().as_bytes().to_vec(),
                environment: intent.selection.environment.clone(),
                budget_ns: u64::try_from(remaining.as_nanos())
                    .map_err(|_| crate::wire::invalid())?
                    .min(intent.selection.budget_ns),
            };
            intent.matches_request(&request)?;
            transport::check_source(&self.source, source, deadline)?;
            attempt.freeze(request)?;
            let host = &original.original;
            let pin = &original.pin;
            let context = &original.context;
            let transferred = exchange(&mut original.channel, attempt, context, |end| {
                host.revalidate(end)?;
                pin.validate(end)?;
                live(context, end)?;
                transport::check_source(&self.source, source, end)?;
                runtime_current()
            });
            original.deadline = original.deadline.min(attempt.end);
            transferred?;
            original.check(original.deadline)?;
            attempt.check(original.deadline)?;
            attempt.request.clone().ok_or_else(crate::wire::invalid)
        })();
        if result.is_err() {
            if let Some(attempt) = &mut self.preparation_cache {
                attempt.phase = Phase::Failed;
            }
            if let Some(original) = &mut self.original {
                original.channel.poison();
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;

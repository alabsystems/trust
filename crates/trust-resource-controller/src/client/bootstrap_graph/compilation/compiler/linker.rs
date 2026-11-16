//! Same actual Fixed compiler primary, lent only after the built-in backend's
//! separately established join and admission pause. No local process/CPU grant.
use std::collections::BTreeSet;

use super::*;
use crate::bootstrap_graph::compilation::compiler::{
    LinkerRetire, LinkerRetired, PairedLinkerRequest,
};
use crate::{Status, StatusFrame};

#[derive(Default)]
pub(super) struct Loans {
    last: u64,
    used: BTreeSet<[u8; 16]>,
    active: Option<(u64, [u8; 16])>,
}
impl Loans {
    fn begin(&mut self, request: &PairedLinkerRequest) -> io::Result<()> {
        request.validate()?;
        if self.active.is_some()
            || request.generation <= self.last
            || self.used.contains(&request.member)
        {
            return Err(crate::wire::invalid());
        }
        self.last = request.generation;
        self.used.insert(request.member);
        self.active = Some((request.generation, request.member));
        Ok(())
    }
    fn end(&mut self, request: &LinkerRetire) -> io::Result<()> {
        if self.active != Some((request.generation, request.member)) {
            return Err(crate::wire::invalid());
        }
        self.active = None;
        Ok(())
    }
}
#[must_use]
pub struct PairedLinkerLoan {
    parent: Arc<CompilerMember>,
    request: PairedLinkerRequest,
    observation: Option<Status>,
    retired: bool,
}
impl Drop for PairedLinkerLoan {
    fn drop(&mut self) {
        if !self.retired {
            std::mem::forget(Arc::clone(&self.parent));
        }
    }
}
#[must_use]
pub struct CompilerLinkerFailure {
    delivery: Delivery,
    unlent: bool,
    error: io::Error,
    parent: Arc<CompilerMember>,
    request: Box<PairedLinkerRequest>,
    loan: Option<Box<PairedLinkerLoan>>,
}
impl CompilerLinkerFailure {
    pub fn delivery(&self) -> Delivery {
        self.delivery
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    pub fn into_loan(mut self) -> Result<PairedLinkerLoan, Self> {
        match self.loan.take() {
            Some(loan) => Ok(*loan),
            None => Err(self),
        }
    }
    /// Consume only the lexical no-request failure from THIS exact original
    /// compiler and pause generation. DATA/error status cannot create this token.
    pub fn into_unoffered(
        self,
        owner: &Arc<CompilerMember>,
        generation: u64,
    ) -> Result<UnlentLinker, Self> {
        if !self.unlent
            || self.delivery != Delivery::BeforeRequest
            || self.loan.is_some()
            || !Arc::ptr_eq(&self.parent, owner)
            || self.request.generation != generation
        {
            return Err(self);
        }
        Ok(UnlentLinker { parent: Arc::clone(&self.parent), generation })
    }
}
impl std::fmt::Debug for CompilerLinkerFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompilerLinkerFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CompilerLinkerFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for CompilerLinkerFailure {}

/// Only an actual before-first-send exchange creates this un-lent local pause.
#[must_use]
pub struct UnlentLinker {
    parent: Arc<CompilerMember>,
    generation: u64,
}
impl UnlentLinker {
    pub fn belongs_to(&self, owner: &CompilerMember, generation: u64) -> bool {
        std::ptr::eq(self.parent.as_ref(), owner) && self.generation == generation
    }
}
/// Actual separate native owning retirement, never decoded status/EOF alone.
#[must_use]
pub struct ClosedLinker {
    parent: Arc<CompilerMember>,
    request: PairedLinkerRequest,
    status: Status,
}
impl ClosedLinker {
    pub fn belongs_to(&self, owner: &CompilerMember, generation: u64) -> bool {
        std::ptr::eq(self.parent.as_ref(), owner) && self.request.generation == generation
    }
    pub fn request(&self) -> &PairedLinkerRequest {
        &self.request
    }
    pub fn status(&self) -> &Status {
        &self.status
    }
}
impl CompilerMember {
    fn current_pin(&self, at: Instant) -> io::Result<()> {
        time(at)?;
        own(self.data.request.compiler)?;
        self.accepted.validate(at)?;
        self.client.host.validate(at)?;
        crate::bootstrap_graph::transport::check_gnu_identity(
            &self.data.request.gnu,
            &self.gnu.each_ref().map(AsFd::as_fd),
        )
    }
    /// # Safety
    /// Built-in post-join backend only: the SAME actual compiler's registry and
    /// all original GNU helpers/offers must be paused before call, with its
    /// actual Root-queued primary retained until consuming ClosedLinker or the
    /// exact lexical UnlentLinker. Unknown MUST terminate before that pause or
    /// queued credit drops. No local fallback or offered execution retry exists.
    pub unsafe fn paired_linker(
        self: &Arc<Self>,
        request: PairedLinkerRequest,
        stdio: [OwnedFd; 3],
        deadline: Instant,
    ) -> Result<PairedLinkerLoan, CompilerLinkerFailure> {
        let mut booked = false;
        let before = (|| {
            let at = deadline.min(self.original_deadline()?);
            self.check_current(at)?;
            request.validate()?;
            if !request.adopted.same_owner(&self.data)
                || request.command.program != self.data.inputs.paired_linker.path
            {
                return Err(crate::wire::invalid());
            }
            self.loans.lock().map_err(|_| crate::wire::invalid())?.begin(&request)?;
            booked = true;
            let host = self.client.host.connect(at)?;
            let channel = Channel::new(host.stream().try_clone()?)?;
            host.revalidate(at)?;
            self.current_pin(at)?;
            Ok((host, channel, at))
        })();
        let (host, mut channel, at) = match before {
            Ok(value) => value,
            Err(error) => {
                // Only this actually booked-and-never-offered generation may
                // cancel its pause. A duplicate preflight rejected while a
                // different loan is active cannot manufacture an un-lent token.
                let unlent = booked
                    && self
                        .loans
                        .lock()
                        .map_err(|_| crate::wire::invalid())
                        .and_then(|mut loans| loans.end(&request.retirement()))
                        .is_ok();
                if booked && !unlent {
                    self.failed.store(true, Ordering::Release);
                }
                return Err(CompilerLinkerFailure {
                    delivery: Delivery::BeforeRequest,
                    unlent,
                    error,
                    parent: Arc::clone(self),
                    request: Box::new(request),
                    loan: None,
                });
            }
        };
        let mut loan = PairedLinkerLoan {
            parent: Arc::clone(self),
            request,
            observation: None,
            retired: false,
        };
        // Caller arms its execution/pause guard BEFORE this first send attempt.
        let result = deliver(&mut channel, &loan.request, stdio, &self.gnu, at, || {
            host.revalidate(at)?;
            self.current_pin(at)
        });
        match result {
            Ok(status) => {
                loan.observation = Some(status);
                Ok(loan)
            }
            Err(error) => Err(CompilerLinkerFailure {
                delivery: Delivery::Unknown,
                unlent: false,
                error,
                parent: Arc::clone(self),
                request: Box::new(loan.request.clone()),
                loan: Some(Box::new(loan)),
            }),
        }
    }
}
fn deliver(
    channel: &mut Channel,
    request: &PairedLinkerRequest,
    stdio: [OwnedFd; 3],
    gnu: &[OwnedFd; 2],
    at: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<Status> {
    let result = (|| {
        current()?;
        channel.send(&request.hello()?, at)?;
        channel.send(&request.encode()?, at)?;
        let first = channel.receive(at)?;
        let rights = first == [crate::bootstrap_graph::compilation::RIGHTS_MARKER];
        let bytes = if rights {
            transport::send_linker_io(
                channel,
                request,
                &[
                    stdio[0].as_fd(),
                    stdio[1].as_fd(),
                    stdio[2].as_fd(),
                    gnu[0].as_fd(),
                    gnu[1].as_fd(),
                ],
                at,
                &mut current,
            )?;
            channel.receive(at)?
        } else {
            first
        };
        let status = StatusFrame::decode(
            &bytes,
            request.adopted.request.query.binding.root_attempt,
            request.member,
        )?
        .status;
        if !matches!(status, Status::Refused { .. })
            && !(rights && matches!(status, Status::Attached))
        {
            return Err(crate::wire::invalid());
        }
        preparation::finish_reply(channel, at, current)?;
        Ok(status)
    })();
    drop(stdio); // Actual EOF must not wait on local offered writer duplicates.
    if result.is_err() {
        channel.poison();
    }
    result
}
impl PairedLinkerLoan {
    pub fn observation(&self) -> Option<&Status> {
        self.observation.as_ref()
    }
    pub fn request(&self) -> &PairedLinkerRequest {
        &self.request
    }
    pub fn retire(mut self, deadline: Instant) -> Result<ClosedLinker, CompilerLinkerFailure> {
        let result = (|| {
            let at = deadline.min(self.parent.original_deadline()?);
            self.parent.current_pin(at)?;
            let host = self.parent.client.host.connect(at)?;
            let mut channel = Channel::new(host.stream().try_clone()?)?;
            host.revalidate(at)?;
            let request = self.request.retirement();
            channel.send(&request.hello()?, at)?;
            channel.send(&request.encode()?, at)?;
            let value = LinkerRetired::decode(&channel.receive(at)?)?;
            preparation::finish_reply(&mut channel, at, || {
                host.revalidate(at)?;
                self.parent.current_pin(at)?;
                if !value.request.same_loan(&request) {
                    return Err(crate::wire::invalid());
                }
                Ok(())
            })?;
            self.parent.loans.lock().map_err(|_| crate::wire::invalid())?.end(&request)?;
            Ok(value.status)
        })();
        match result {
            Ok(status) => {
                self.retired = true;
                Ok(ClosedLinker {
                    parent: Arc::clone(&self.parent),
                    request: self.request.clone(),
                    status,
                })
            }
            Err(error) => Err(CompilerLinkerFailure {
                delivery: Delivery::Unknown,
                unlent: false,
                error,
                parent: Arc::clone(&self.parent),
                request: Box::new(self.request.clone()),
                loan: Some(Box::new(self)),
            }),
        }
    }
}
#[cfg(test)]
mod tests;

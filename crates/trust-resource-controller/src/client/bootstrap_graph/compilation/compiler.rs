//! Actual private Fixed compiler adoption; never an inherited Root/lease import.
use std::os::fd::{AsFd, OwnedFd};

use trust_resource_provenance::{Host, PinnedHelper, process};

use super::*;

mod linker;
pub use linker::{ClosedLinker, CompilerLinkerFailure, PairedLinkerLoan, UnlentLinker};

use crate::bootstrap_graph::compilation::compiler::{
    AdoptRequest, Adopted, GNU_RIGHTS_MARKER, transport,
};
use crate::client::Delivery;
use crate::{BirthKind, Identity};

/// Only a pinned actual native registered-compiler exchange constructs this
/// owner. No saved context, Adopted bytes, source path, CPU FD or pool does so.
#[must_use]
pub struct CompilerMember {
    client: Client,
    accepted: PinnedHelper,
    data: Adopted,
    gnu: [OwnedFd; 2],
    deadline: Mutex<Instant>,
    failed: AtomicBool,
    loans: Mutex<linker::Loans>,
}
impl CompilerMember {
    pub fn data(&self) -> &Adopted {
        &self.data
    }
    pub fn original_deadline(&self) -> io::Result<Instant> {
        self.deadline.lock().map(|at| *at).map_err(|_| crate::wire::invalid())
    }
    pub fn check_current(&self, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed.load(Ordering::Acquire) {
                return Err(crate::wire::invalid());
            }
            let bound = self.original_deadline()?;
            let at = deadline.min(bound);
            time(at)?;
            self.accepted.validate(at)?;
            let gnu = [self.gnu[0].try_clone()?, self.gnu[1].try_clone()?];
            let mut actual =
                OriginalAdoption::new(self.client.clone(), self.data.request.clone(), gnu, at);
            let value = actual
                .exchange(|value, started| {
                    if !value.same_owner(&self.data) {
                        return Err(crate::wire::invalid());
                    }
                    let mut original = self.deadline.lock().map_err(|_| crate::wire::invalid())?;
                    *original = restrict(started, value.remaining_ns, Some(*original))?;
                    Ok(())
                })
                .map_err(|error| {
                    self.failed.store(true, Ordering::Release);
                    io::Error::other(CompilerAdoptionFailure::retaining(error, actual).to_string())
                })?;
            if !value.same_owner(&self.data) {
                return Err(crate::wire::invalid());
            }
            self.accepted.validate(at)?;
            time(self.original_deadline()?)
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
}
struct OriginalAdoption {
    client: Client,
    request: AdoptRequest,
    gnu: Option<[OwnedFd; 2]>,
    deadline: Instant,
    started: Instant,
    offered: bool,
    host: Option<Host>,
    channel: Option<Channel>,
    accepted: Option<PinnedHelper>,
}
impl OriginalAdoption {
    fn new(client: Client, request: AdoptRequest, gnu: [OwnedFd; 2], deadline: Instant) -> Self {
        Self {
            client,
            request,
            gnu: Some(gnu),
            deadline,
            started: Instant::now(),
            offered: false,
            host: None,
            channel: None,
            accepted: None,
        }
    }
    fn exchange(
        &mut self,
        validate: impl FnOnce(&Adopted, Instant) -> io::Result<()>,
    ) -> io::Result<Adopted> {
        let Self { client, request, gnu, deadline, started, offered, host, channel, accepted } =
            self;
        let at = *deadline;
        time(at)?;
        own(request.compiler)?;
        request.validate()?;
        let gnu = gnu.as_ref().ok_or_else(crate::wire::invalid)?;
        crate::bootstrap_graph::transport::check_gnu_identity(
            &request.gnu,
            &gnu.each_ref().map(AsFd::as_fd),
        )?;
        *host = Some(client.host.connect(at)?);
        *channel =
            Some(Channel::new(host.as_ref().expect("actual adoption peer").stream().try_clone()?)?);
        let channel = channel.as_mut().expect("actual adoption channel");
        host.as_ref().expect("actual adoption peer").revalidate(at)?;
        // BEFORE the first send. Unknown cannot fall back to local/ordinary
        // startup or construct another compiler owner from a decoded receipt.
        *offered = true;
        channel.send(&request.hello()?, at)?;
        channel.send(&request.encode()?, at)?;
        if channel.receive(at)? != [GNU_RIGHTS_MARKER] {
            return Err(crate::wire::invalid());
        }
        transport::send_gnu(channel, request, &gnu.each_ref().map(AsFd::as_fd), at, || {
            host.as_ref().expect("same actual adoption peer").revalidate(at)
        })?;
        let value = Adopted::decode(&channel.receive(at)?)?;
        preparation::finish_reply(channel, at, || {
            host.as_ref().expect("same actual adoption peer").revalidate(at)?;
            client.host.validate(at)?;
            own(request.compiler)?;
            crate::bootstrap_graph::transport::check_gnu_identity(
                &request.gnu,
                &gnu.each_ref().map(AsFd::as_fd),
            )?;
            if value.request != *request {
                return Err(crate::wire::invalid());
            }
            validate(&value, *started)?;
            // Convert the SAME live accepted peer before ACK lets the server
            // close it (Darwin loses peer audit identity after full closure).
            match host.take().expect("same actual adoption peer").into_helper_preserving(at) {
                Ok(pin) => *accepted = Some(pin),
                Err(failure) => {
                    let (original, error) = *failure;
                    *host = Some(original);
                    return Err(error);
                }
            }
            Ok(())
        })?;
        Ok(value)
    }
}
fn own(identity: Identity) -> io::Result<()> {
    let actual = process::read_identity(std::process::id())?;
    if identity.pid != actual.pid
        || identity.birth != actual.birth
        || !matches!(identity.birth_kind,BirthKind::MacosWallMicroseconds if cfg!(target_os="macos"))
            && !matches!(identity.birth_kind,BirthKind::LinuxStartTicks if cfg!(target_os="linux"))
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
fn restrict(started: Instant, remaining: u64, original: Option<Instant>) -> io::Result<Instant> {
    if remaining == 0 {
        return Err(io::ErrorKind::TimedOut.into());
    }
    let observed =
        started.checked_add(Duration::from_nanos(remaining)).ok_or_else(crate::wire::invalid)?;
    let restricted = original.map_or(observed, |original| original.min(observed));
    time(restricted)?;
    Ok(restricted)
}
#[must_use]
pub struct CompilerAdoptionFailure {
    error: io::Error,
    original: Option<Box<OriginalAdoption>>,
}
impl CompilerAdoptionFailure {
    fn retaining(error: io::Error, original: OriginalAdoption) -> Self {
        Self { error, original: Some(Box::new(original)) }
    }
    pub fn delivery(&self) -> Delivery {
        if self.original.as_ref().is_some_and(|original| original.offered) {
            Delivery::Unknown
        } else {
            Delivery::BeforeRequest
        }
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
}
impl Drop for CompilerAdoptionFailure {
    fn drop(&mut self) {
        if let Some(original) = self.original.take() {
            std::mem::forget(original);
        }
    }
}
impl std::fmt::Debug for CompilerAdoptionFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompilerAdoptionFailure")
            .field("delivery", &self.delivery())
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for CompilerAdoptionFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for CompilerAdoptionFailure {}
impl Client {
    pub fn adopt_bootstrap_fixed_compiler(
        &self,
        request: AdoptRequest,
        gnu: [OwnedFd; 2],
        deadline: Instant,
    ) -> Result<Arc<CompilerMember>, CompilerAdoptionFailure> {
        let mut original = OriginalAdoption::new(self.clone(), request, gnu, deadline);
        let mut bound = None;
        let result = original.exchange(|value, started| {
            bound = Some(restrict(started, value.remaining_ns, None)?);
            Ok(())
        });
        match result {
            Err(error) => Err(CompilerAdoptionFailure::retaining(error, original)),
            Ok(data) => {
                let deadline = bound.expect("original native Root bound");
                if let Err(error) = time(deadline) {
                    return Err(CompilerAdoptionFailure::retaining(error, original));
                }
                Ok(Arc::new(CompilerMember {
                    client: self.clone(),
                    accepted: original.accepted.take().expect("actual accepted issuer"),
                    data,
                    gnu: original.gnu.take().expect("same original GNU witnesses"),
                    deadline: Mutex::new(deadline),
                    failed: AtomicBool::new(false),
                    loans: Mutex::new(linker::Loans::default()),
                }))
            }
        }
    }
}
#[cfg(test)]
mod tests;

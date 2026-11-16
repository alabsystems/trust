//! Direct original-Root member sessions. No local helper or extra GNU credit.
use std::collections::{BTreeMap, BTreeSet};
use std::os::fd::{AsFd, OwnedFd};

use super::*;
use crate::bootstrap_graph::compilation::{
    MemberRequest, ProgramRole, RIGHTS_MARKER, RetireRequest, Retired, transport,
};
use crate::client::Delivery;
use crate::{Status, StatusFrame};

/// Restriction only. A booked sequence/nonce is never refunded or replayed,
/// even when a failed connect spends a sequence the native Host never saw.
#[derive(Default)]
pub(super) struct Members {
    last: u64,
    used: BTreeSet<[u8; 16]>,
    active: BTreeMap<u64, [u8; 16]>,
}
impl Members {
    pub(super) fn idle(&self) -> bool {
        self.active.is_empty()
    }

    fn begin(&mut self, request: &MemberRequest) -> io::Result<()> {
        request.validate()?;
        if request.sequence <= self.last || self.used.contains(&request.member) {
            return Err(crate::wire::invalid());
        }
        self.last = request.sequence;
        self.used.insert(request.member);
        self.active.insert(request.sequence, request.member);
        Ok(())
    }
    fn completed(&mut self, request: &RetireRequest) -> io::Result<()> {
        if self.active.get(&request.sequence) != Some(&request.member) {
            return Err(crate::wire::invalid());
        }
        self.active.remove(&request.sequence);
        Ok(())
    }
}

/// The actual accepted member and original GNU descriptions. The enclosing
/// Cargo queue must retain its actual acquired/implicit credit until consuming
/// opaque retirement; Attached/Refused/EOF and dropping this value cannot do so.
#[must_use]
pub struct ResidentBootstrapMember {
    parent: Arc<ResidentBootstrapCompilation>,
    request: MemberRequest,
    gnu: Option<[OwnedFd; 2]>,
    observation: Option<Status>,
    retired: bool,
}
impl Drop for ResidentBootstrapMember {
    fn drop(&mut self) {
        if !self.retired {
            // Unknown abandonment cannot close the actual original accepted
            // boundary or make its GNU descriptions an apparent release.
            std::mem::forget(Arc::clone(&self.parent));
            if let Some(gnu) = self.gnu.take() {
                std::mem::forget(gnu);
            }
        }
    }
}

/// A lexical BeforeRequest owns no delivered member. Unknown retains the
/// actual member and permits only consuming retirement of that SAME attempt.
#[must_use]
pub struct BootstrapMemberFailure {
    delivery: Delivery,
    error: io::Error,
    member: Option<Box<ResidentBootstrapMember>>,
}
impl BootstrapMemberFailure {
    pub fn delivery(&self) -> Delivery {
        self.delivery
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
    pub fn into_member(mut self) -> Result<ResidentBootstrapMember, Self> {
        match self.member.take() {
            Some(member) => Ok(*member),
            None => Err(self),
        }
    }
}
impl std::fmt::Debug for BootstrapMemberFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BootstrapMemberFailure")
            .field("delivery", &self.delivery)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}
impl std::fmt::Display for BootstrapMemberFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for BootstrapMemberFailure {}

/// Private construction only after the distinct pinned native Retire exchange
/// proves actual owning closure. A decoded Retired frame cannot construct it.
#[must_use]
pub struct RetiredBootstrapMember {
    parent: Arc<ResidentBootstrapCompilation>,
    request: MemberRequest,
    status: Status,
}
impl RetiredBootstrapMember {
    pub fn request(&self) -> &MemberRequest {
        &self.request
    }
    pub fn status(&self) -> &Status {
        &self.status
    }
    pub fn revalidate(&self, deadline: Instant) -> io::Result<()> {
        self.parent.original_current(deadline.min(self.parent.deadline))
    }
}

impl ResidentBootstrapCompilation {
    fn original_current(&self, deadline: Instant) -> io::Result<()> {
        time(deadline)?;
        let original = self.graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
        if !Arc::ptr_eq(&original.pin, &self.client.host) {
            return Err(crate::wire::invalid());
        }
        original.check(deadline)
    }

    /// Consume actual held stdio3 + SAME original GNU2. This borrows the Cargo
    /// queue's already-held execution, never acquiring any supplementary byte.
    /// The caller must hold its real queue guard until opaque native retirement.
    pub fn member(
        self: &Arc<Self>,
        request: MemberRequest,
        descriptions: [OwnedFd; 5],
        deadline: Instant,
    ) -> Result<ResidentBootstrapMember, BootstrapMemberFailure> {
        let deadline = deadline.min(self.deadline);
        let mut booked = false;
        let before = (|| {
            self.check_current(deadline)?;
            same_member_bindings(&self.advanced, &request)?;
            let original = self.graph.original.as_ref().ok_or_else(crate::wire::invalid)?;
            if !matches!(original.context.context.cpu, crate::Cpu::RetainedFixed { units, .. }
                if request.fixed_units <= units)
            {
                return Err(crate::wire::invalid());
            }
            transport::check(&request, &descriptions.each_ref().map(AsFd::as_fd), deadline)?;
            self.members
                .lock()
                .map_err(|_| io::Error::other("Full member registry poisoned"))?
                .begin(&request)?;
            booked = true;
            let host = self.client.host.connect(deadline)?;
            let channel = Channel::new(host.stream().try_clone()?)?;
            host.revalidate(deadline)?;
            self.original_current(deadline)?;
            Ok((host, channel))
        })();
        let (host, mut channel) = match before {
            Ok(value) => value,
            Err(error) => {
                if booked {
                    // This lexical branch never called any send. It may end
                    // an unused local reservation; nonce/sequence stay spent.
                    let key = RetireRequest {
                        key: request.key.clone(),
                        sequence: request.sequence,
                        member: request.member,
                    };
                    if self
                        .members
                        .lock()
                        .map_err(|_| crate::wire::invalid())
                        .and_then(|mut members| members.completed(&key))
                        .is_err()
                    {
                        self.failed.store(true, Ordering::Release);
                    }
                }
                return Err(BootstrapMemberFailure {
                    delivery: Delivery::BeforeRequest,
                    error,
                    member: None,
                });
            }
        };
        let [stdin, stdout, stderr, reader, writer] = descriptions;
        let mut member = ResidentBootstrapMember {
            parent: Arc::clone(self),
            request,
            gnu: Some([reader, writer]),
            observation: None,
            retired: false,
        };
        // Arm the enclosing execution loan BEFORE this call: even hello/send
        // failure may offer an operation. No replacement Member is retried.
        let result = deliver(
            &mut channel,
            &member.request,
            [stdin, stdout, stderr],
            member.gnu.as_ref().expect("original GNU descriptions"),
            deadline,
            || {
                host.revalidate(deadline)?;
                self.original_current(deadline)?;
                same_member_bindings(&self.advanced, &member.request)
            },
        );
        match result {
            Ok(status) => {
                member.observation = Some(status);
                Ok(member)
            }
            Err(error) => Err(BootstrapMemberFailure {
                delivery: Delivery::Unknown,
                error,
                member: Some(Box::new(member)),
            }),
        }
    }
}

/// Protocol DATA only. Actual caller owns the pin/Root and private member.
/// Consuming the actual stdio3 here closes all local writer copies on success,
/// error and unwind, while the distinct original GNU2 owner stays retained.
fn deliver(
    channel: &mut Channel,
    request: &MemberRequest,
    stdio: [OwnedFd; 3],
    gnu: &[OwnedFd; 2],
    deadline: Instant,
    mut current: impl FnMut() -> io::Result<()>,
) -> io::Result<Status> {
    let result = (|| {
        current()?;
        channel.send(&request.hello()?, deadline)?;
        channel.send(&request.encode()?, deadline)?;
        let first = channel.receive(deadline)?;
        let status = if first == [RIGHTS_MARKER] {
            transport::send(
                channel,
                request,
                &[
                    stdio[0].as_fd(),
                    stdio[1].as_fd(),
                    stdio[2].as_fd(),
                    gnu[0].as_fd(),
                    gnu[1].as_fd(),
                ],
                deadline,
                &mut current,
            )?;
            member_status(request, &channel.receive(deadline)?, true)?
        } else {
            member_status(request, &first, false)?
        };
        preparation::finish_reply(channel, deadline, current)?;
        Ok(status)
    })();
    if result.is_err() {
        channel.poison();
    }
    drop(stdio);
    result
}

fn same_member_bindings(value: &Advanced, request: &MemberRequest) -> io::Result<()> {
    request.validate()?;
    let expected = match request.program {
        ProgramRole::SeedCompiler => Some(&value.seed.compiler.path),
        ProgramRole::SeedTargo => Some(&value.seed.targo.path),
        ProgramRole::SeedFormatter => Some(&value.seed.formatter.path),
        // Only the actual native retained producer may validate this role.
        ProgramRole::IssuedProgram { .. } => None,
    };
    if request.key != value.key
        || request.gnu != value.gnu
        || expected.is_some_and(|path| path != &request.command.program)
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
fn member_status(request: &MemberRequest, bytes: &[u8], rights: bool) -> io::Result<Status> {
    let status = StatusFrame::decode(
        bytes,
        request.key.attempt.key.graph.query.binding.root_attempt,
        request.member,
    )?
    .status;
    if !matches!(status, Status::Refused { .. }) && !(rights && matches!(status, Status::Attached))
    {
        return Err(crate::wire::invalid());
    }
    Ok(status)
}
impl ResidentBootstrapMember {
    /// Observation only: neither Attached nor Refused settles an execution loan.
    pub fn observation(&self) -> Option<&Status> {
        self.observation.as_ref()
    }
    pub fn request(&self) -> &MemberRequest {
        &self.request
    }
    pub fn retire(
        mut self,
        deadline: Instant,
    ) -> Result<RetiredBootstrapMember, BootstrapMemberFailure> {
        // The attach I/O bound and execution timeout cannot shorten or reset
        // the original owning retirement endpoint. Native enforces execution
        // timeout; closure still needs the SAME original Root settlement.
        let deadline = deadline.min(self.parent.deadline);
        let request = RetireRequest {
            key: self.request.key.clone(),
            sequence: self.request.sequence,
            member: self.request.member,
        };
        let result = (|| {
            self.parent.original_current(deadline)?;
            let host = self.parent.client.host.connect(deadline)?;
            let mut channel = Channel::new(host.stream().try_clone()?)?;
            host.revalidate(deadline)?;
            channel.send(&request.hello()?, deadline)?;
            channel.send(&request.encode()?, deadline)?;
            let value = Retired::decode(&channel.receive(deadline)?)?;
            preparation::finish_reply(&mut channel, deadline, || {
                host.revalidate(deadline)?;
                self.parent.original_current(deadline)?;
                if value.request != request {
                    return Err(crate::wire::invalid());
                }
                Ok(())
            })?;
            self.parent
                .members
                .lock()
                .map_err(|_| io::Error::other("Full member registry poisoned"))?
                .completed(&request)?;
            Ok(value.status)
        })();
        match result {
            Ok(status) => {
                self.retired = true;
                Ok(RetiredBootstrapMember {
                    parent: Arc::clone(&self.parent),
                    request: self.request.clone(),
                    status,
                })
            }
            Err(error) => Err(BootstrapMemberFailure {
                delivery: Delivery::Unknown,
                error,
                member: Some(Box::new(self)),
            }),
        }
    }
}

#[cfg(test)]
mod tests;

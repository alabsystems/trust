//! Trusted native SDK output registration on the SAME sole control owner.
#[cfg(test)]
use std::os::fd::AsFd;
use std::os::fd::BorrowedFd;

use super::*;
use crate::workload::host::produced::{
    REGISTRATION_MARKER, Registration, RegistrationAck, RegistrationReply,
};

/// NonClone, nonDeserialize live exchange result. This is a continuation to
/// the original host's private registry, not a recreated UnitOutput or an
/// execution grant. The caller must retain its real original artifact/leases.
pub struct RegisteredOutput {
    pub(super) registration: Registration,
    pub(super) acknowledged: RegistrationAck,
    pub(super) host: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
}
impl RegisteredOutput {
    pub fn registration(&self) -> &Registration {
        &self.registration
    }
    pub fn observation(&self) -> &RegistrationAck {
        &self.acknowledged
    }
    pub(crate) fn matches(&self, client: &super::super::Client) -> bool {
        std::sync::Arc::ptr_eq(&self.host, &client.host)
    }
    pub(crate) fn matches_pin(
        &self,
        pin: &std::sync::Arc<trust_resource_provenance::PinnedHelper>,
    ) -> bool {
        std::sync::Arc::ptr_eq(&self.host, pin)
    }
}
fn executable(fd: BorrowedFd<'_>) -> io::Result<(crate::FileIdentity, u64)> {
    // SAFETY: observe existing flags on the caller's live borrowed description.
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    // SAFETY: local descriptor flags only; this does not mutate the description.
    let local = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    if flags < 0
        || flags & libc::O_ACCMODE != libc::O_RDONLY
        || local < 0
        || local & libc::FD_CLOEXEC == 0
    {
        return Err(refused());
    }
    let file = File::from(fd.try_clone_to_owned()?);
    use std::os::unix::fs::MetadataExt;
    let meta = file.metadata()?;
    // SAFETY: read the current effective identity, with no process mutation.
    let uid = unsafe { libc::geteuid() };
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != uid
        || meta.mode() & 0o022 != 0
        || meta.len() == 0
        || meta.len() > 1024 * 1024 * 1024
    {
        return Err(refused());
    }
    Ok((crate::FileIdentity { device: meta.dev(), inode: meta.ino() }, meta.len()))
}
impl WorkloadControl {
    /// Register only the actual output of the SAME live trusted native SDK
    /// compilation coordinator after its current compiler writers have joined.
    /// # Safety
    /// The caller retains the original compilation/Layout output leases,
    /// HeldOutputRoot, original HeldProgram SDK and fully validated
    /// HeldProducedProgram through registration AND actual member retirement.
    /// `original` must borrow that exact held program's original readonly FD,
    /// never a file opened from saved/path/JSON data. Cold output names its
    /// actual successfully retired matching compiler member; None certifies
    /// only trusted current warm materialization. The original queue is parked,
    /// all current workers/loans have positively retired and Enter is active.
    /// This trusted contract cannot be satisfied by decoding Registration.
    pub unsafe fn register_output(
        &mut self,
        request: &Registration,
        original: BorrowedFd<'_>,
        deadline: Instant,
    ) -> Result<RegisteredOutput, WorkloadControlError> {
        if self.failed
            || self.output_locks.is_none()
            || self.drained
            || self.pending.is_some()
            || self.active_phase != Some((request.key.phase, request.key.ordinal))
            || request.key.root_attempt != self.root_attempt
            || request.key.invocation_sha256 != self.invocation_sha256
        {
            return Err(WorkloadControlError::BeforeRequest(refused()));
        }
        let payload = request.encode().map_err(WorkloadControlError::BeforeRequest)?;
        let before = executable(original).map_err(WorkloadControlError::BeforeRequest)?;
        let result = (|| {
            self.host.validate(deadline)?;
            self.channel.send(&payload, deadline)?;
            // One close-only socket duplicate, no independent protocol reader.
            let socket = self.channel.as_fd().try_clone_to_owned()?;
            let stream = std::os::unix::net::UnixStream::from(socket);
            jobserver_utils::descriptor_transfer::send(
                &stream,
                &[original],
                REGISTRATION_MARKER,
                deadline,
            )?;
            let reply = RegistrationReply::decode(&self.channel.receive(deadline)?, request)?;
            self.host.validate(deadline)?;
            match &reply {
                RegistrationReply::Registered(ack)
                    if (ack.executable.device, ack.executable.inode, ack.executable.bytes)
                        == (before.0.device, before.0.inode, before.1)
                        && executable(original)? == before => {}
                RegistrationReply::Registered(_) => return Err(refused()),
                RegistrationReply::Refused { .. } => {}
            }
            Ok(reply)
        })();
        match result {
            Ok(RegistrationReply::Registered(acknowledged)) => Ok(RegisteredOutput {
                registration: request.clone(),
                acknowledged,
                host: self.host.clone(),
            }),
            // A known bound refusal admits no produced child; retain SAME
            // control so the coordinator can positively Leave its phase.
            Ok(RegistrationReply::Refused { reason, .. }) => {
                Err(WorkloadControlError::Refused { reason })
            }
            Err(error) => {
                self.failed = true;
                Err(WorkloadControlError::Unknown(error))
            }
        }
    }
}

#[cfg(test)]
mod tests;

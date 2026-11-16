//! Same original root control transfers the actual close-only Layout OFDs.
#[cfg(test)]
use std::os::fd::AsFd;
use std::os::fd::BorrowedFd;
use std::os::unix::fs::MetadataExt;

use super::*;
use crate::workload::host::output::{self, Reply, Request};

/// Positive live handoff observation, not a lock constructor or execution
/// grant. The host privately retains the actual originals through root/cohort
/// settlement; it does not release them at a phase boundary or this Drop.
pub struct RetainedOutputLocks {
    request: Request,
}
impl RetainedOutputLocks {
    pub fn observation(&self) -> &Request {
        &self.request
    }
}

fn originals(request: &Request, descriptions: &[BorrowedFd<'_>]) -> io::Result<()> {
    request.validate()?;
    if descriptions.len() != request.locks.len() {
        return Err(refused());
    }
    let mut fds = std::collections::BTreeSet::new();
    for (observed, fd) in request.locks.iter().zip(descriptions) {
        // SAFETY: observe flags/identity of an existing caller-owned description.
        let mode = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
        let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
        let meta = File::from(fd.try_clone_to_owned()?).metadata()?;
        let uid = unsafe { libc::geteuid() };
        if mode < 0
            || mode & libc::O_ACCMODE != libc::O_RDWR
            || flags < 0
            || flags & libc::FD_CLOEXEC == 0
            || !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != uid
            || meta.mode() & 0o022 != 0
            || (meta.dev(), meta.ino()) != (observed.backing.device, observed.backing.inode)
            || !fds.insert(fd.as_raw_fd())
        {
            return Err(refused());
        }
    }
    Ok(())
}
impl WorkloadControl {
    /// Transfer the complete actual original workload Layout guard census.
    /// # Safety
    /// SAME trusted SDK coordinator owns the original compile/output capsule;
    /// every guard was switched to close-only BEFORE any duplicate/SCM offer.
    /// These borrowed descriptions come directly from that capsule, not opens,
    /// paths, saved records, generic files or another worktree. No compiler was
    /// dispatched for legacy40/60. Distinct native49/v3 may add another declared
    /// output only after all earlier actual member/phase/loan owners retired.
    /// All earlier query loans retired. No guard is omitted or
    /// truncated to satisfy MAX_LOCKS. The caller retains the same capsule
    /// through actual compilation/actions, and Host retains received originals
    /// independently through real root/cohort settlement. No re-lock is allowed.
    pub unsafe fn retain_output_locks(
        &mut self,
        request: &Request,
        descriptions: &[BorrowedFd<'_>],
        deadline: Instant,
    ) -> Result<RetainedOutputLocks, WorkloadControlError> {
        if self.failed
            || self.drained
            || self.pending.is_some()
            || self.active_phase.is_some()
            || (self.native_outputs.is_none() && self.output_locks.is_some())
            || self.native_outputs.as_ref().is_some_and(|roots| {
                !roots.contains(&request.output_root)
                    || self.retained_outputs.contains_key(&request.output_root)
            })
            || request.key.root_attempt != self.root_attempt
            || request.key.invocation_sha256 != self.invocation_sha256
        {
            return Err(WorkloadControlError::BeforeRequest(refused()));
        }
        let payload = request
            .encode()
            .map_err(WorkloadControlError::BeforeRequest)?;
        originals(request, descriptions).map_err(WorkloadControlError::BeforeRequest)?;
        let result = (|| {
            self.host.validate(deadline)?;
            self.channel.send(&payload, deadline)?;
            let stream =
                std::os::unix::net::UnixStream::from(self.channel.as_fd().try_clone_to_owned()?);
            jobserver_utils::descriptor_transfer::send(
                &stream,
                descriptions,
                output::MARKER,
                deadline,
            )?;
            let reply = Reply::decode(&self.channel.receive(deadline)?, request)?;
            self.host.validate(deadline)?;
            originals(request, descriptions)?;
            Ok(reply)
        })();
        match result {
            Ok(Reply::Retained { .. }) => {
                self.output_locks = Some(request.clone());
                if self.native_outputs.is_some() {
                    self.retained_outputs
                        .insert(request.output_root.clone(), request.clone());
                }
                Ok(RetainedOutputLocks {
                    request: request.clone(),
                })
            }
            Ok(Reply::Refused { reason, .. }) => Err(WorkloadControlError::Refused { reason }),
            Err(error) => {
                self.failed = true;
                Err(WorkloadControlError::Unknown(error))
            }
        }
    }
    /// Select only a genuine retained original receipt in the SAME distinct
    /// native startup. The actual broker/Host must positively drain the current
    /// bank, phase and member owners before calling; this never acquires locks.
    pub fn select_output_locks(
        &mut self,
        retained: &RetainedOutputLocks,
        attempt: [u8; 16],
        deadline: Instant,
    ) -> Result<(), WorkloadControlError> {
        let request = &retained.request;
        let before = (|| -> io::Result<_> {
            if self.failed
                || self.drained
                || self.pending.is_some()
                || self.active_phase.is_some()
                || self.local_active.is_some()
                || self
                    .native_outputs
                    .as_ref()
                    .is_none_or(|roots| !roots.contains(&request.output_root))
                || self.retained_outputs.get(&request.output_root) != Some(request)
                || request.key.root_attempt != self.root_attempt
                || request.key.invocation_sha256 != self.invocation_sha256
            {
                return Err(refused());
            }
            let selection = output::Selection {
                retained: request.clone(),
                sequence: self
                    .last_output_selection
                    .checked_add(1)
                    .ok_or_else(refused)?,
                attempt,
            };
            let bytes = selection.encode()?;
            Ok((selection, bytes))
        })()
        .map_err(WorkloadControlError::BeforeRequest)?;
        let (selection, bytes) = before;
        let received = (|| -> io::Result<_> {
            self.host.validate(deadline)?;
            self.channel.send(&bytes, deadline)?;
            let reply =
                output::SelectionReply::decode(&self.channel.receive(deadline)?, &selection)?;
            self.host.validate(deadline)?;
            Ok(reply)
        })();
        match received {
            Ok(reply) => {
                self.last_output_selection = selection.sequence;
                match reply.decision {
                    output::SelectionDecision::Selected => {
                        self.output_locks = Some(request.clone());
                        Ok(())
                    }
                    output::SelectionDecision::Refused { reason } => {
                        Err(WorkloadControlError::Refused { reason })
                    }
                }
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

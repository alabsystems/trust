// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual pending native/shadow/common-M descriptions from the SAME original
//! Host channel. Retaining these resources creates no executable unit, claim
//! writer, adopted controller or independent Host approval.
use super::*;
use crate::workload::host::keeper as wire;

/// The original receiver must keep this owner in its real SDK/worker scope,
/// including failure paths. Field observations and a Retained reply cannot
/// construct it. Its read-only common-M descriptor is not a claim writer.
pub struct AuthenticatedPendingKeeper {
    request: wire::Request,
    originals: jobserver_utils::fork_custody::ProtectedOriginals<3>,
    host: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
    // LAST: actual originals close before their original FD envelope retires.
    _fd_charge: crate::descriptors::OriginalInputPermit,
}
impl AuthenticatedPendingKeeper {
    pub fn observation(&self) -> &wire::Request {
        &self.request
    }
    // Borrow only inside this controller's original-channel return path. Bank
    // consumers retain the opaque owner, not a descriptor-copy/unlock API.
    fn descriptions(&self) -> io::Result<[std::os::fd::BorrowedFd<'_>; 3]> {
        Ok([
            self.originals.get(0).ok_or_else(refused)?,
            self.originals.get(1).ok_or_else(refused)?,
            self.originals.get(2).ok_or_else(refused)?,
        ])
    }
    fn check_descriptions(&self) -> io::Result<()> {
        let originals = self.descriptions()?;
        for (original, expected) in originals.iter().zip([
            self.request.native,
            self.request.shadow,
            self.request.memory_guard,
        ]) {
            if identity(original.as_raw_fd())? != expected {
                return Err(refused());
            }
        }
        // SAFETY: inspect flags of the privately owned original descriptor;
        // this neither changes its OFD nor creates a writer.
        let flags = unsafe { libc::fcntl(originals[2].as_raw_fd(), libc::F_GETFL) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::O_ACCMODE != libc::O_RDONLY {
            return Err(refused());
        }
        Ok(())
    }
}

impl WorkloadControl {
    pub(super) fn receive_pending_keeper(
        &mut self,
        request: wire::Request,
        bank: &mut dyn partial::PartialBank,
        deadline: Instant,
    ) -> io::Result<()> {
        request.validate()?;
        if self.failed
            || self.drained
            || self.pending.is_some()
            || request.root_attempt != self.root_attempt
            || request.invocation_sha256 != self.invocation_sha256
            || !self.keeper_phase_matches(request.phase)
        {
            return Err(refused());
        }
        self.host.validate(deadline)?;
        let fd_charge = bank.reserve_pending_keeper()?;
        self.host.validate(deadline)?;
        let originals = receive_protected_marked(&self.channel, wire::ORIGINALS_MARKER, deadline)?;
        let owner = std::sync::Arc::new(AuthenticatedPendingKeeper {
            request,
            originals,
            host: self.host.clone(),
            _fd_charge: fd_charge,
        });
        owner.check_descriptions()?;
        self.host.validate(deadline)?;
        bank.retain_pending_keeper(owner.clone())?;
        // Bookend the actual storage callback. No counter, capacity grant or
        // renewed deadline follows from its return or from the acknowledgement.
        if !std::sync::Arc::ptr_eq(&self.host, &owner.host)
            || !self.keeper_phase_matches(owner.request.phase)
        {
            return Err(refused());
        }
        owner.check_descriptions()?;
        self.host.validate(deadline)?;
        self.channel.send(&wire::Retained { request: owner.request }.encode()?, deadline)?;
        jobserver_utils::descriptor_transfer::send(
            &self.channel.as_fd(),
            &owner.descriptions()?,
            wire::ORIGINALS_MARKER,
            deadline,
        )?;
        self.host.validate(deadline)
    }
}

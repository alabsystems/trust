// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Initial inherited DATA custody, never admission from descriptor numbers.
use jobserver_utils::fork_custody::ProtectedOriginals;

use super::*;
use crate::workload::host::initial as wire;

pub struct PendingInitialKeeper {
    native: FileIdentity,
    originals: [(RawFd, FileIdentity); 2],
}
pub struct EarlyInitialKeeper {
    native: FileIdentity,
    originals: ProtectedOriginals<2>,
}
/// Only the SAME authenticated Initial exchange constructs this owner. It
/// retains actual installed originals but creates no writer, loan or grant.
pub struct AuthenticatedInitialKeeper {
    binding: host::keeper::Request,
    _originals: EarlyInitialKeeper,
}
impl AuthenticatedInitialKeeper {
    pub fn observation(&self) -> &host::keeper::Request {
        &self.binding
    }
}

/// Observe only the fixed Initial mapping before other imports allocate FDs.
/// A full-width mapping must never be reinterpreted as Initial keeper inputs.
pub fn snapshot_initial_keeper(cpus: &PendingCpuSet) -> io::Result<PendingInitialKeeper> {
    if cpus.originals.len() != 1 || cpus.originals[0].0 != wire::PRIMARY_FD {
        return Err(refused());
    }
    let native = cpus.originals[0].1;
    let originals = [
        (wire::SHADOW_FD, identity(wire::SHADOW_FD)?),
        (wire::MEMORY_GUARD_FD, identity(wire::MEMORY_GUARD_FD)?),
    ];
    if originals[0].1 == native || originals[1].1 == native || originals[0].1 == originals[1].1 {
        return Err(refused());
    }
    readonly_memory(wire::MEMORY_GUARD_FD)?;
    Ok(PendingInitialKeeper { native, originals })
}

fn readonly_memory(fd: RawFd) -> io::Result<()> {
    // SAFETY: observe only the actual inherited or privately owned descriptor.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if flags & libc::O_ACCMODE != libc::O_RDONLY {
        return Err(refused());
    }
    Ok(())
}

/// Move the existing two mapped descriptions; allocate no descriptor copies.
/// # Safety
/// Same fixed single-threaded entry as capture_cpu_set. Both mappings are
/// exclusively transferred, disjoint from CPU/store/SDK/GNU/stdio, and no
/// code may close/reuse them between snapshot and capture.
pub unsafe fn capture_initial_keeper(
    pending: PendingInitialKeeper,
    deadline: Instant,
) -> io::Result<EarlyInitialKeeper> {
    // SAFETY: fixed single-threaded entry transfers both exact inherited
    // slots. Adopt before any refusal so an expired capture closes both too.
    let owned = pending.originals.map(|(fd, _)| unsafe { OwnedFd::from_raw_fd(fd) });
    let originals = ProtectedOriginals::capture(deadline, move |capture| {
        for original in owned {
            capture.push(original)?;
        }
        Ok(())
    })?;
    for (index, (_, expected)) in pending.originals.iter().enumerate() {
        if identity(originals.get(index).ok_or_else(refused)?.as_raw_fd())? != *expected {
            return Err(refused());
        }
    }
    readonly_memory(originals.get(1).ok_or_else(refused)?.as_raw_fd())?;
    Ok(EarlyInitialKeeper { native: pending.native, originals })
}

impl EarlyInitialKeeper {
    fn check_binding(&self, binding: &host::keeper::Request) -> io::Result<()> {
        binding.validate()?;
        if self.native != binding.native
            || identity(self.originals.get(0).ok_or_else(refused)?.as_raw_fd())? != binding.shadow
            || identity(self.originals.get(1).ok_or_else(refused)?.as_raw_fd())?
                != binding.memory_guard
        {
            return Err(refused());
        }
        readonly_memory(self.originals.get(1).ok_or_else(refused)?.as_raw_fd())
    }
    pub(super) fn authenticate(
        self,
        reply: &wire::ReadyReply,
    ) -> io::Result<std::sync::Arc<AuthenticatedInitialKeeper>> {
        let binding = reply.keeper;
        if self.native != reply.primary.backing
            || binding.root_attempt != reply.context.context.root_attempt
            || binding.invocation_sha256 != reply.invocation_sha256
            || binding.phase != reply.phase
            || binding.native_slot != reply.primary.slot
            || binding.memory_guard != reply.context.context.memory.guard
            || binding.memory_epoch != reply.context.context.memory.epoch
        {
            return Err(refused());
        }
        use sha2::Digest as _;
        let memory = &reply.context.context.memory;
        let scope: [u8; 32] = sha2::Sha256::digest(host::keeper::memory_scope_bytes(
            memory.namespace,
            &memory.marker,
            memory.epoch,
            memory.guard,
        )?)
        .into();
        if binding.memory_scope_sha256 != scope {
            return Err(refused());
        }
        self.check_binding(&binding)?;
        Ok(std::sync::Arc::new(AuthenticatedInitialKeeper { binding, _originals: self }))
    }
}

#[cfg(test)]
mod tests;

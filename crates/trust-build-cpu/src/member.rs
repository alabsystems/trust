// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Actual retained scheduling backing shared by native member executors.
//!
//! Construction consumes live checked CPU/fence/GNU owners, never environment
//! advertisements or a decoded context. This creates no CPU capacity or memory
//! reservation. An execution owner must separately admit the member, retain its
//! original memory custody, and hold this value until descendant drain.

use std::ffi::OsString;
use std::io;
use std::os::fd::{AsFd as _, AsRawFd as _, OwnedFd};
use std::sync::Arc;

use jobserver_utils::{CPU_HANDOFF_ENV, CpuLeaseHandoff, Jobserver};

use crate::{IMPLICIT_FD_ENV, Lease, LegacyFence};

/// One original native CPU unit, its epoch fences and the selected GNU server.
///
/// The scheduler retains responsibility for logical borrowed-credit exclusion
/// and descriptor admission. Dropping a separate diagnostic record or copied
/// context cannot release this backing. Neither this value nor its descriptor
/// advertisements authorize a new execution or confer memory custody.
pub struct MemberScheduling {
    // Retain the actual origin, not just its duplicated transport descriptors.
    _lease: Arc<Lease>,
    _fence: Arc<LegacyFence>,
    cpu: Arc<OwnedFd>,
    fences: Vec<Arc<OwnedFd>>,
    handoff: CpuLeaseHandoff,
    jobserver: Jobserver,
}

impl MemberScheduling {
    /// Retain existing checked backing without creating a pool, epoch or token.
    ///
    /// `jobserver` must be the caller's already-selected original GNU transport;
    /// importing an advertised descriptor or replacing an ancestor's capacity
    /// with a newly constructed server belongs to neither this API nor a member.
    pub fn retain(
        lease: Arc<Lease>,
        fence: Arc<LegacyFence>,
        jobserver: Jobserver,
    ) -> io::Result<Self> {
        let cpu = Arc::new(lease.as_fd().try_clone_to_owned()?);
        let fences = fence
            .files()
            .iter()
            .map(|file| file.as_fd().try_clone_to_owned().map(Arc::new))
            .collect::<io::Result<Vec<_>>>()?;
        let handoff = CpuLeaseHandoff::new_bundle(
            cpu.as_fd().try_clone_to_owned()?,
            fences
                .iter()
                .map(|file| file.as_fd().try_clone_to_owned())
                .collect::<io::Result<Vec<_>>>()?,
        )?;
        Ok(Self { _lease: lease, _fence: fence, cpu, fences, handoff, jobserver })
    }

    /// The same selected GNU owner. Reading it acquires or creates no credits.
    pub fn jobserver(&self) -> &Jobserver {
        &self.jobserver
    }

    /// Exact owned CPU/fence descriptions for explicit child-only inheritance.
    /// GNU descriptors remain with [`Self::jobserver`], which regenerates its
    /// own transport. Callers must retain this owner through the complete wait.
    pub fn descriptors(&self) -> impl Iterator<Item = &Arc<OwnedFd>> {
        std::iter::once(&self.cpu).chain(&self.fences)
    }

    /// Transport advertisements regenerated solely from this owner's backing.
    /// These locators are not admission, proof, memory or release authority.
    pub fn environment(&self) -> [(&'static str, OsString); 3] {
        [
            (IMPLICIT_FD_ENV, self.cpu.as_raw_fd().to_string().into()),
            (CPU_HANDOFF_ENV, self.handoff.advertisement().to_os_string()),
            (
                "BUILD_SLOT_FENCE_FDS",
                self.fences
                    .iter()
                    .map(|file| file.as_raw_fd().to_string())
                    .collect::<Vec<_>>()
                    .join(",")
                    .into(),
            ),
        ]
    }
}

#[cfg(test)]
mod tests;

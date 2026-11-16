//! Durable in-process ownership of the manager's original acquisition.

use std::io;

use super::{Acquire, HeldAcquisition, HeldRecord, Manager, Release, Status, invalid};
use crate::trust_build_lock::NamespaceGuard;

/// A process either owns or borrows a pinned holder, or observes contention.
pub enum LeaseAcquisition {
    Granted(Lease),
    Busy(Status),
}

/// Retains the actual root, directory and record descriptions captured while
/// acquiring under the namespace mutex. No token-to-guard reconstruction.
/// A borrowed lease never releases its live ancestor's holder.
#[must_use = "retain the original lease until protected work and child ownership settle"]
pub struct Lease {
    manager: Manager,
    held: Box<HeldRecord>,
    token: String,
    process: u32,
    borrowed: bool,
    release_on_drop: bool,
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    maintenance: Option<Box<withholding::MaintenanceState>>,
}

impl Manager {
    /// Acquire for this durable process using the same recovery, waiting,
    /// writer discovery and validated ancestry as the administrative front door.
    pub fn acquire_lease(self, request: &Acquire) -> io::Result<LeaseAcquisition> {
        if request.owner_pid != std::process::id() {
            return Err(invalid("a native lease must belong to the acquiring process"));
        }
        let (token, held, borrowed) = match self.acquire_held(request)? {
            HeldAcquisition::Acquired(token, held) => (token, held, false),
            HeldAcquisition::Borrowed(token, held) => (token, held, true),
            HeldAcquisition::Busy(status) => return Ok(LeaseAcquisition::Busy(status)),
        };
        Ok(LeaseAcquisition::Granted(Lease {
            manager: self,
            held: Box::new(held),
            token,
            process: std::process::id(),
            borrowed,
            release_on_drop: true,
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            maintenance: None,
        }))
    }
}

impl Lease {
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn configure_child(&self, command: &mut std::process::Command) -> io::Result<()> {
        self.check_current()?;
        command.env("TRUST_BUILD_LOCK_TOKEN", &self.token);
        command.env("TRUST_REPO", &self.manager.root.physical);
        Ok(())
    }

    pub fn is_borrowed(&self) -> bool {
        self.borrowed
    }

    /// Observe only the original pinned holder. Replacement, mutation or a
    /// forked copy cannot acquire authority by presenting its token.
    pub fn check_current(&self) -> io::Result<()> {
        if self.process != std::process::id() {
            return Err(invalid("a forked lease has no original process authority"));
        }
        let _namespace = NamespaceGuard::acquire(&self.manager.root.physical)?;
        self.manager.check_record(&self.held)
    }

    /// Observe the requested repository against the SAME retained original
    /// root, without acquiring, borrowing or reconstructing another lease.
    pub fn check_root(&self, root: &std::path::Path) -> io::Result<()> {
        self.check_current()?;
        self.manager.root.check_expected(root).map_err(invalid)
    }

    fn release_original(&self) -> io::Result<Release> {
        if self.process != std::process::id() || self.borrowed {
            return Err(invalid("this process does not own the original lease release"));
        }
        let _namespace = NamespaceGuard::acquire(&self.manager.root.physical)?;
        self.manager.check_record(&self.held)?;
        #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
        if self.maintenance.is_some() {
            return self.release_maintenance();
        }
        self.manager.release_locked(&self.token)
    }
}

impl Drop for Lease {
    fn drop(&mut self) {
        if self.release_on_drop && !self.borrowed && self.process == std::process::id() {
            // The existing manager retains unknown/surviving writers; failure
            // keeps exclusion and never deletes a replacement holder.
            let _ = self.release_original();
        }
    }
}

mod withholding;
pub use withholding::{
    JoinedChild, LaunchIdentity, LaunchRegistration, LocalJoinedScope, OriginalSourceOffer,
    OriginalSourceRoot, ProtectedWorkScope, ScopeDispatch, ScopeFailure, ScopeIdentity,
    ScopedCapture, ScopedChild, ScopedReader, ScopedThread, ScopedThreads, ScopedWorker,
    SealedWorkScope, SourceOfferData, WeakScopeDispatch, WithheldLease, WithholdFailure,
    WithholdPublication, WorkerRegistration,
};

#[cfg(test)]
mod tests;

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub(crate) use withholding::{MaintenanceBinding, MaintenanceLease};
#[cfg(feature = "resident-inputs")]
pub use withholding::{RefusedInputRetirement, RetiredResidentInputs};

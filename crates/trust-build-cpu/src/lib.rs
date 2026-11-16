// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Kernel-held CPU leases for cooperating build schedulers.
//!
//! A lease covers one executing unit, not a whole build. There is no daemon,
//! permanent reservation, or process-name registry. A scheduler acquires a
//! lease before starting a unit and keeps it until the unit and its inherited
//! work end. Dropping the final descriptor releases the kernel lock, including
//! after an abnormal process exit. Local jobserver and memory policy remain
//! the caller's responsibilities.
//!
//! Ordinary `Pool` slot records are diagnostics, not authority. Only the kernel lock makes a
//! slot busy; a stale record in an unlocked file never consumes capacity.
//! An owner read while a lock is held is a reported identity, not independent
//! proof that the process currently holds that descriptor.
//!
//! `RetainedPool` is a separate, explicitly created private domain. It records
//! debt before exposing a release capability, so controller death cannot release
//! capacity still used by descendants. It does not select or migrate the global
//! pool. Its caller must establish actual work completion before settlement.

#![warn(missing_docs)]

use std::io;

/// The versioned directory under the native per-account capacity directory.
pub const DIRECTORY_NAME: &str = "build-cpu-v1";
/// Largest slot count accepted from a caller, bounding initialization and scans.
pub const MAX_SLOTS: u32 = 65_536;
/// Largest diagnostic record accepted from a slot file.
pub const MAX_RECORD_BYTES: usize = 256;

/// Reported process identity. It is not a permission or proof capability.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Owner {
    /// Process the scheduler reports as owning this unit.
    pub pid: u32,
    /// Platform process-birth identity, if the scheduler measured one.
    pub birth: Option<u64>,
}

impl Owner {
    /// This process, with an optional measured platform birth identity.
    #[must_use]
    pub fn current(birth: Option<u64>) -> Self {
        Self { pid: std::process::id(), birth }
    }
}

/// Version-one diagnostic record written only while a slot is exclusively held.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Record {
    /// Slot index, starting at zero.
    pub slot: u32,
    /// The scheduler's reported owner.
    pub owner: Owner,
}

impl Record {
    /// Canonical bounded record. `held=1` is a diagnostic label; readers must
    /// separately observe the kernel lock before reporting a held slot.
    #[must_use]
    pub fn encode(self) -> String {
        let birth = self.owner.birth.map_or_else(|| "-".into(), |value| value.to_string());
        format!(
            "trust-build-cpu-v1 slot={} pid={} birth={birth} held=1\n",
            self.slot, self.owner.pid
        )
    }

    /// Parse a canonical record, rejecting unknown versions and malformed data.
    pub fn parse(text: &str) -> io::Result<Self> {
        if text.len() > MAX_RECORD_BYTES {
            return Err(invalid("CPU slot record exceeds its size bound"));
        }
        let words: Vec<_> = text
            .strip_suffix('\n')
            .ok_or_else(|| invalid("unterminated CPU slot record"))?
            .split(' ')
            .collect();
        if words.len() != 5 || words[0] != "trust-build-cpu-v1" || words[4] != "held=1" {
            return Err(invalid("unsupported CPU slot record"));
        }
        let number = |word: &str, key: &str| -> io::Result<u64> {
            let value = word.strip_prefix(key).ok_or_else(|| invalid("missing CPU slot field"))?;
            if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
                return Err(invalid("invalid CPU slot number"));
            }
            value.parse().map_err(|_| invalid("CPU slot number overflow"))
        };
        let slot = u32::try_from(number(words[1], "slot=")?)
            .map_err(|_| invalid("CPU slot index overflow"))?;
        let pid = u32::try_from(number(words[2], "pid=")?)
            .map_err(|_| invalid("CPU owner pid overflow"))?;
        if pid == 0 {
            return Err(invalid("CPU owner pid is zero"));
        }
        let birth = if words[3] == "birth=-" { None } else { Some(number(words[3], "birth=")?) };
        let record = Self { slot, owner: Owner { pid, birth } };
        if record.encode() != text {
            return Err(invalid("non-canonical CPU slot record"));
        }
        Ok(record)
    }
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[cfg(feature = "observations")]
mod observation;
#[cfg(feature = "observations")]
pub use observation::{Measurements, MemoryPressure, Observation, ThermalPressure};

#[cfg(all(unix, feature = "observations"))]
mod monitor;
#[cfg(all(unix, feature = "observations"))]
pub use monitor::Monitor;
#[cfg(all(unix, feature = "observations"))]
mod host_policy;
#[cfg(all(unix, feature = "observations"))]
pub use host_policy::{HostPolicy, ObservationSource};

/// One nonblocking observation. Held-owner metadata can be absent or invalid;
/// an unreadable identity must never turn a held kernel lease into a free slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SlotState {
    /// A shared kernel lock succeeded at the observation point.
    Available {
        /// Slot index.
        slot: u32,
    },
    /// A shared kernel lock was refused by an exclusive holder.
    Held {
        /// Slot index.
        slot: u32,
        /// Diagnostic identity, not independently authenticated.
        reported_owner: Option<Owner>,
    },
}

#[cfg(unix)]
mod unix;
#[cfg(all(unix, feature = "observations"))]
pub use unix::LegacyFixedTransaction;
#[cfg(unix)]
pub use unix::{Lease, Pool, capacity_dir};
#[cfg(all(unix, feature = "observations"))]
mod external;
#[cfg(all(unix, feature = "observations"))]
pub use external::LegacyFixedRoom;
#[cfg(unix)]
mod fence;
#[cfg(unix)]
pub use fence::LegacyFence;
#[cfg(all(any(target_os = "linux", target_os = "macos"), feature = "member"))]
mod member;
#[cfg(all(any(target_os = "linux", target_os = "macos"), feature = "member"))]
pub use member::MemberScheduling;
#[cfg(unix)]
mod kernel_memory;
#[cfg(unix)]
pub use kernel_memory::{available_memory, default_memory_reserve};
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
mod native_observation;
#[cfg(unix)]
mod native_usage;
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub use native_observation::NativeHostObservation;
#[cfg(unix)]
pub mod process_cpu;
#[cfg(unix)]
pub use native_usage::NativeUsage;
#[cfg(unix)]
mod protocol;
#[cfg(unix)]
pub use protocol::{IMPLICIT_FD_ENV, duplicate_descriptor, duplicate_descriptors};

#[cfg(all(unix, feature = "jobserver"))]
mod worker;
#[cfg(all(unix, feature = "jobserver"))]
pub use worker::{Credit, WorkerClient, WorkerHelper, WorkerPause};

#[cfg(unix)]
mod retained;
#[cfg(unix)]
pub use retained::{
    PreparedReservation, RETAINED_DIRECTORY_NAME, RecoveredReservation, RecoveryCandidate,
    RetainedLease, RetainedLeaseIdentity, RetainedPool, RetainedSlotState,
};

#[cfg(test)]
mod tests;

#[cfg(all(test, unix))]
mod retained_tests;

#[cfg(all(test, unix))]
mod admission_tests;
#[cfg(unix)]
mod legacy_retirement;
#[cfg(unix)]
pub use legacy_retirement::LegacyRetirement;

#[cfg(unix)]
mod external_debt;
#[cfg(unix)]
pub use external_debt::{
    ExternalDebt, NativeCapacityBank, NativeCapacityLoan, NativeCapacityReturnError,
    NativeDomainReservation, PendingNativePair, PendingNativePairCustody,
    PreparingNativeCapacityBank, ScopedNativeCapacityBank,
};
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub use external_debt::{InitialNativeOriginals, NativeJobOriginals, PartialNativeOriginals};

#[cfg(unix)]
mod recovery_material;
#[cfg(unix)]
pub use recovery_material::{PreparedRecovery, RecoveryAuthority, RecoveryMaterial};

#[cfg(unix)]
mod native_domain;
#[cfg(unix)]
pub use native_domain::{NativeDomain, NativeMigrationStatus};

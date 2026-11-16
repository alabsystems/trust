//! Fixed-command admission in the existing legacy/native CPU protocols.
//!
//! A fixed claim retains original worktree/slot descriptions. It is not an
//! original GNU credit, an SDK/Host loan, or evidence of descendant closure.

use std::num::NonZeroU32;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_build_cpu::{LegacyFixedRoom, Pool};

use super::*;

#[path = "machine/handoff.rs"]
mod handoff;
#[path = "machine/policy.rs"]
mod policy;
#[path = "machine/quiet.rs"]
mod quiet;
#[cfg(feature = "native-exec")]
#[path = "machine/runtime.rs"]
mod runtime;
pub use handoff::{
    EarlyFixedClaim, FIXED_HANDOFF_ENV, FixedCommandSignal, InheritedFixedClaim,
    PreparedFixedCommand, RunningFixedCommand, RunningFixedGroup,
};
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use handoff::{PreparedNestedFixedCommand, RunningNestedFixedCommand};
pub use policy::{FixedCommandAdmission, FixedCpuRequest};
#[cfg(feature = "native-exec")]
pub use runtime::{RuntimeClaimCurrency, RuntimeFixedClaim};

impl Coordinator {
    /// Acquire worktree, legacy slots and actual native CPU room as one
    /// unlaunched queue attempt. A busy/unknown CPU domain releases every
    /// partial resource and preserves this request's original priority ticket.
    /// This does not establish GNU credits, descendant completion, SDK/Host
    /// custody or the measured quietness required by an exclusive launcher.
    pub fn attempt_fixed(
        &mut self,
        memory: Option<u64>,
        maximum: u32,
        budget: NonZeroU32,
    ) -> io::Result<Attempt<FixedClaim>> {
        let (legacy, _) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        if fs::canonicalize(legacy)? != fs::canonicalize(&self.directory.path)? {
            return Err(invalid(
                "custom coordination namespace cannot select machine CPU authority",
            ));
        }
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?.ok_or_else(|| {
            io::Error::new(io::ErrorKind::NotFound, "original native CPU pool is unavailable")
        })?;
        self.attempt_fixed_in_pool(memory, maximum, budget, &pool)
    }

    fn attempt_fixed_in_pool(
        &mut self,
        memory: Option<u64>,
        maximum: u32,
        budget: NonZeroU32,
        pool: &Pool,
    ) -> io::Result<Attempt<FixedClaim>> {
        self.attempt_fixed_with_budget(memory, maximum, pool, |_| Ok(budget))
    }

    fn attempt_fixed_with_budget(
        &mut self,
        memory: Option<u64>,
        maximum: u32,
        pool: &Pool,
        budget: impl FnOnce(&Reservation) -> io::Result<NonZeroU32>,
    ) -> io::Result<Attempt<FixedClaim>> {
        let mut native_wait = None;
        let result = self.attempt_with(memory, maximum, |mut reservation| {
            if reservation.exclusive && !reservation.try_drain_exclusive()? {
                return Ok(None);
            }
            let Some(transaction) = pool.try_legacy_fixed_transaction()? else {
                native_wait = Some(LegacyFixedRoom::Busy);
                return Ok(None);
            };
            let selected = budget(&reservation)?;
            let claim = reservation.publish_fixed(pool.slots(), selected)?;
            let original_admission = claim.original_exclusive_admission()?;
            let room = transaction.observe(
                &claim.reservation.namespace,
                NonZeroU32::new(claim.reservation.minimum_slots).unwrap(),
                original_admission,
            )?;
            claim.check_current()?;
            match room {
                LegacyFixedRoom::Fits { .. } => Ok(Some(claim)),
                waiting => {
                    native_wait = Some(waiting);
                    Ok(None)
                }
            }
        })?;
        Ok(match (result, native_wait) {
            (Attempt::Waiting(super::super::Waiting::ResourcesBusy), Some(reason)) => {
                Attempt::Waiting(super::super::Waiting::NativeCpu(reason))
            }
            (result, _) => result,
        })
    }
}

/// Original published fixed reservation. The complete claim stays live while
/// native workers drain. No path, integer budget or marker constructs this type.
pub struct FixedClaim {
    reservation: Reservation,
    lease_id: String,
    cpus: NonZeroU32,
    budget: NonZeroU32,
    record_pool_slots: u32,
    record: Vec<u8>,
}

impl Reservation {
    /// Publish the exact existing fixed-v1 protocol before judging native room.
    /// CPU count is a measured machine width, not a caller's parallelism. The
    /// requested budget must fit the ACTUAL retained legacy slot share.
    /// This consumes no native CPU lease and launches nothing.
    fn publish_fixed(self, cpus: NonZeroU32, budget: NonZeroU32) -> io::Result<FixedClaim> {
        self.check_current()?;
        if cpus.get() > trust_build_cpu::MAX_SLOTS {
            return Err(invalid("fixed machine width exceeds the native bound"));
        }
        if !self.drained {
            return Err(invalid("exclusive admission has not drained its original slots"));
        }
        let reserved = self.slots.len() as u64;
        let share = u64::from(cpus.get()) * reserved / u64::from(self.minimum_slots);
        if budget.get() > cpus.get() || u64::from(budget.get()) > share.max(1) {
            return Err(invalid("fixed CPU budget exceeds its actual original slot share"));
        }
        let mut random = [0_u8; 16];
        // This public lease ID correlates records; it is never an authority or
        // a recovery secret. Read native random bytes without a helper process.
        File::open("/dev/urandom")?.read_exact(&mut random)?;
        let lease_id: String = random.iter().map(|byte| format!("{byte:02x}")).collect();
        let mut record_pool_slots = self.minimum_slots;
        for lease in &self.slots {
            let index = lease
                .name
                .to_str()
                .and_then(|name| name.strip_prefix("slot-"))
                .and_then(|value| value.parse::<u32>().ok())
                .and_then(|index| index.checked_add(1))
                .filter(|width| *width <= trust_build_cpu::MAX_SLOTS)
                .ok_or_else(|| {
                    invalid("fixed historical slot is outside the native record bound")
                })?;
            record_pool_slots = record_pool_slots.max(index);
        }
        let mut claim = FixedClaim {
            reservation: self,
            lease_id,
            cpus,
            budget,
            record_pool_slots,
            record: Vec::new(),
        };
        claim.publish_owner(std::process::id(), None)?;
        // Ordinary fixed commands release admission after publishing their
        // complete slot records. Exclusive commands retain the same EX fence.
        if !claim.reservation.exclusive {
            let admission = claim
                .reservation
                .held
                .pop()
                .ok_or_else(|| invalid("fixed claim lost original admission"))?;
            if admission.name != std::ffi::OsStr::new("admission.lock") {
                return Err(invalid("fixed claim admission identity changed"));
            }
            admission.check()?;
            drop(admission);
        }
        claim.reservation.check_current()?;
        Ok(claim)
    }
}

impl FixedClaim {
    fn original_exclusive_admission(&self) -> io::Result<Option<&File>> {
        if self.reservation.exclusive {
            Ok(Some(
                &self
                    .reservation
                    .held
                    .last()
                    .ok_or_else(|| invalid("exclusive claim lost original admission"))?
                    .file,
            ))
        } else {
            Ok(None)
        }
    }
    /// Current desired CPU ceiling, bound to the actual held fixed claim.
    pub fn budget(&self) -> NonZeroU32 {
        self.budget
    }

    /// Revalidate actual retained namespace/record owners and observe the SAME
    /// existing native manifest. Never creates or repairs a native CPU pool.
    pub fn observe_native_room(&self) -> io::Result<LegacyFixedRoom> {
        let (canonical_legacy, _) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        if fs::canonicalize(canonical_legacy)? != fs::canonicalize(&self.reservation.namespace)? {
            return Err(invalid(
                "custom coordination namespace cannot select machine CPU authority",
            ));
        }
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?.ok_or_else(|| {
            io::Error::new(io::ErrorKind::NotFound, "original native CPU pool is unavailable")
        })?;
        self.observe_in_pool(&pool)
    }

    fn observe_in_pool(&self, pool: &Pool) -> io::Result<LegacyFixedRoom> {
        self.check_current()?;
        if pool.slots() != self.cpus {
            return Err(invalid("fixed claim and original native machine width differ"));
        }
        let original_admission = self.original_exclusive_admission()?;
        let observed = pool.observe_legacy_fixed_room(
            &self.reservation.namespace,
            NonZeroU32::new(self.reservation.minimum_slots).unwrap(),
            original_admission,
        )?;
        self.check_current()?;
        Ok(observed)
    }

    /// Native observations do not substitute for original record custody.
    pub fn check_current(&self) -> io::Result<()> {
        self.reservation.check_current()?;
        for lease in self.reservation.held.iter().chain(&self.reservation.slots) {
            if read_record(&lease.file)? != self.record {
                return Err(invalid("original fixed reservation record changed"));
            }
        }
        Ok(())
    }

    fn publish_owner(&mut self, pid: u32, supervisor_pid: Option<u32>) -> io::Result<()> {
        if pid == 0 {
            return Err(invalid("fixed command owner PID is zero"));
        }
        let started =
            SystemTime::now().duration_since(UNIX_EPOCH).map_err(io::Error::other)?.as_secs_f64();
        let cwd = std::env::current_dir()?;
        let (claim_file_count, claim_files_sha256) = handoff::fingerprint_claim(self)?;
        let record = serde_json::to_vec(&serde_json::json!({
            "pid":pid,"supervisor_pid":supervisor_pid,"cmd":"native fixed command",
            "cwd":cwd.to_string_lossy(),"cwd_bytes":cwd.as_os_str().as_bytes(),"started":started,
            "cpu_mode":"fixed-v1","cpu_budget":self.budget.get(),
            "pool_slots":self.record_pool_slots,"lease_id":self.lease_id,
            "exclusive":self.reservation.exclusive,"native_fixed_version":1,
            "machine_cpus":self.cpus.get(),"minimum_slots":self.reservation.minimum_slots,
            "claim_file_count":claim_file_count,"claim_files_sha256":claim_files_sha256
        }))
        .map_err(io::Error::other)?;
        if record.len() as u64 > MAX_RECORD {
            return Err(invalid("fixed owner record exceeds its bound"));
        }
        for lease in self.reservation.held.iter_mut().chain(&mut self.reservation.slots) {
            lease.check()?;
            lease.file.seek(SeekFrom::Start(0))?;
            lease.file.set_len(0)?;
            lease.file.write_all(&record)?;
            lease.file.flush()?;
            lease.check()?;
        }
        self.record = record;
        Ok(())
    }
}

#[cfg(test)]
#[path = "machine/tests.rs"]
mod tests;

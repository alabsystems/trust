// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-retained external reservations bound to the native CPU manifest.
//!
//! Activation requires the host's durable legacy-client exclusion. This module
//! supplies accounting and settlement capabilities, not descendant custody.

use std::fs::{File, OpenOptions};
use std::io::{self, Seek, SeekFrom, Write};
use std::num::NonZeroU32;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;

use sha2::{Digest, Sha256};

use crate::recovery_material::{PreparedRecovery, RecoveryAuthority, RecoveryMaterial};
use crate::unix::{Probe, check_private, open_parent, read_text};
use crate::{
    Lease, LegacyRetirement, Owner, Pool, PreparedReservation, RecoveredReservation, RetainedLease,
    RetainedPool, RetainedSlotState, SlotState, invalid,
};

const ANCHOR: &str = "external-debt-v1";
const DOMAIN: &str = "external-debt-domain-v1";
const VERSION: &str = "trust-external-debt-v3";

mod bank;
pub use bank::{
    NativeCapacityBank, NativeCapacityLoan, NativeCapacityReturnError, PendingNativePair,
    PendingNativePairCustody, PreparingNativeCapacityBank, ScopedNativeCapacityBank,
};

/// Durable external debt which every participating native admission must count.
/// An existing anchor is never repaired, removed, or interpreted as zero debt.
#[derive(Clone, Debug)]
pub struct ExternalDebt {
    native: Pool,
    retained: RetainedPool,
    binding: Binding,
    retirement: LegacyRetirement,
}

/// One actual native lease per slot, paired with crash-retained exclusion for
/// that SAME domain. The exclusion is not another set of execution credits.
/// Dropping either live description set never settles the durable obligation.
/// No record, count or public observation can construct this value.
pub struct NativeDomainReservation {
    native: Vec<Lease>,
    retained: Vec<RetainedLease>,
    domain: [u8; 32],
    context: [u8; 32],
}
impl NativeDomainReservation {
    /// Retain this actual native/shadow reservation as one original machine
    /// bank. It creates no pool or extra credit; only this owner may loan its
    /// already-funded units to cooperating scopes. Generic external readers
    /// remain conservative and never infer aliasing from diagnostic records.
    pub fn into_capacity_bank(self) -> io::Result<NativeCapacityBank> {
        NativeCapacityBank::new(self)
    }
    /// Original live kernel guards. A custodian may explicitly inherit these
    /// SAME descriptions; it must never synthesize replacements from a count.
    pub fn native_leases(&self) -> &[Lease] {
        &self.native
    }

    /// Settle only after independently establishing the original execution
    /// scope's positive retirement. This primitive observes no process and is
    /// not a closure proof. Native guards remain held while exclusion settles.
    pub fn settle_exclusion(&mut self) -> io::Result<()> {
        while let Some(lease) = self.retained.last_mut() {
            lease.settle_held()?;
            self.retained.pop();
        }
        Ok(())
    }
    /// Whether this original capability's exclusion has settled. This is
    /// bookkeeping only and establishes no process or execution-scope closure.
    pub fn exclusion_settled(&self) -> bool {
        self.retained.is_empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Binding {
    native_dev: u64,
    native_ino: u64,
    root_dev: u64,
    root_ino: u64,
    width: u32,
    legacy_dev: u64,
    legacy_ino: u64,
    legacy_boot: String,
}

impl ExternalDebt {
    /// Continue the actual primary lent to a registered produced coordinator.
    /// The opaque same-Host receiver remains owned by the caller, including
    /// on failure; neither a Context nor an arbitrary File can call this path.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_coordinator_original(
        &self,
        received: &trust_resource_controller::client::CoordinatorOriginals,
        deadline: std::time::Instant,
    ) -> io::Result<Lease> {
        received.validate(deadline)?;
        self.validate()?;
        let reply = received.observation();
        let (device, inode) = self.native_manifest_identity()?;
        let trust_resource_controller::Cpu::CooperativeShared { ceiling, native_manifest } =
            reply.context.context.cpu
        else {
            return Err(invalid("coordinator original is not cooperative"));
        };
        let width = self.native.slots().get();
        if native_manifest.device != device
            || native_manifest.inode != inode
            || ceiling != width
            || self.reserved()? != width
        {
            return Err(invalid("coordinator original domain or held exclusion differs"));
        }
        let original = File::from(received.primary().try_clone_to_owned()?);
        let lease = self.native.continue_workload_original(reply.primary.slot, original)?;
        received.validate(deadline)?;
        Ok(lease)
    }
    /// Consume ONLY original descriptions received on the authenticated live
    /// workload startup exchange. Ordinary inherited-file adoption is unchanged
    /// and cannot bypass retained headroom. No lock is acquired or replaced.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_workload_startup(
        &self,
        startup: trust_resource_controller::client::workload::AuthenticatedWorkloadStartup,
    ) -> io::Result<(
        trust_resource_controller::workload::host::ReadyReply,
        Vec<Lease>,
        trust_resource_controller::client::workload::WorkloadControl,
    )> {
        let (reply, files, control) = startup.into_originals();
        let leases = self.adopt_original_workload_set(
            &reply.context.context,
            reply.cpu_set().cloned().collect(),
            files,
        )?;
        Ok((reply, leases, control))
    }

    /// Distinct initial-pair adoption. The opaque live Host transfer, not a
    /// partial V1 reply or domain count, supplies the actual original guard.
    /// The independently opened native domain remains the original maximum.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_initial_workload_startup(
        &self,
        startup: trust_resource_controller::client::workload::AuthenticatedInitialStartup,
    ) -> io::Result<InitialNativeOriginals> {
        self.validate()?;
        let (reply, mut files, control, keeper) = startup.into_originals();
        reply.encode()?;
        let trust_resource_controller::Cpu::CooperativeShared { ceiling, native_manifest } =
            reply.context.context.cpu
        else {
            return Err(invalid("initial pair cannot adopt fixed or borrowed-primary custody"));
        };
        let (device, inode) = self.native_manifest_identity()?;
        if ceiling != self.native.slots().get()
            || native_manifest.device != device
            || native_manifest.inode != inode
            || files.len() != 1
            || self.reserved()? == 0
        {
            return Err(invalid("initial original differs from the independently opened domain"));
        }
        let file = files.pop().ok_or_else(|| invalid("actual initial description missing"))?;
        let primary = self.native.continue_workload_original(reply.primary.slot, file)?;
        if keeper.observation() != &reply.keeper {
            return Err(invalid("Initial original keeper binding changed"));
        }
        Ok(InitialNativeOriginals { reply, primary, control, keeper })
    }
    /// Continue only the opaque paired startup's actual original descriptions.
    /// The v2 reply/full60 digest stays paired; no decoded observation, v1
    /// conversion, fresh acquisition or partial grant can enter this path.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_paired_qualification_startup(
        &self,
        startup: trust_resource_controller::client::paired_qualification::AuthenticatedPairedQualificationStartup,
    ) -> io::Result<(
        trust_resource_controller::paired_qualification::host::ReadyReply,
        Vec<Lease>,
        trust_resource_controller::client::workload::WorkloadControl,
    )> {
        let (reply, files, control) = startup.into_originals();
        let leases = self.adopt_original_workload_set(
            &reply.context.context,
            reply.cpu_set().cloned().collect(),
            files,
        )?;
        Ok((reply, leases, control))
    }
    /// Continue the actual authenticated general-job originals. The opaque
    /// startup remains retained with the adopted set, including its SAME
    /// descriptor reservation; this never manufactures a workload-v1 owner.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_native_job_startup(
        &self,
        mut startup: trust_resource_controller::client::native_job::AuthenticatedNativeJobStartup,
    ) -> io::Result<NativeJobOriginals> {
        let files = startup.take_originals()?;
        let reply = startup.observation();
        let leases = self.adopt_original_workload_set(
            &reply.context.context,
            reply.cpu_set().cloned().collect(),
            files,
        )?;
        Ok(NativeJobOriginals { leases: Some(leases), startup })
    }

    /// Adopt only actual replacement descriptions received by the original
    /// pinned Host channel. No observation, PID, ACK or FD pathname constructs
    /// the authenticated input. This issues no new machine reservation.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub fn adopt_partial_funding(
        &self,
        received: trust_resource_controller::client::workload::AuthenticatedPartialFunding,
    ) -> io::Result<PartialNativeOriginals> {
        self.validate()?;
        let trust_resource_controller::Cpu::CooperativeShared { ceiling, native_manifest } =
            received.original_cpu()
        else {
            return Err(invalid("partial handoff cannot convert fixed CPU custody"));
        };
        let (device, inode) = self.native_manifest_identity()?;
        if ceiling != self.native.slots().get()
            || ceiling < 2
            || native_manifest.device != device
            || native_manifest.inode != inode
        {
            return Err(invalid("partial funding differs from actual retained native domain"));
        }
        let root_attempt = received.root_attempt();
        let invocation_sha256 = received.invocation_sha256();
        let phase = received.phase();
        let ordinal = received.ordinal();
        let funded_before = received.funded_before();
        let (observations, files) = received.into_originals();
        let total = funded_before
            .checked_add(files.len())
            .ok_or_else(|| invalid("partial funding count overflow"))?;
        if funded_before == 0
            || files.is_empty()
            || total > ceiling as usize
            || self.reserved()? < total as u32
            || files.len() != observations.len()
        {
            return Err(invalid("partial original description set differs"));
        }
        let mut leases = Vec::new();
        leases.try_reserve_exact(files.len()).map_err(io::Error::other)?;
        for (file, observed) in files.into_iter().zip(observations) {
            leases.push(self.native.continue_workload_original(observed.slot, file)?);
        }
        Ok(PartialNativeOriginals {
            root_attempt,
            invocation_sha256,
            phase,
            ordinal,
            funded_before,
            leases,
        })
    }
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    fn adopt_original_workload_set(
        &self,
        context: &trust_resource_controller::Context,
        observations: Vec<trust_resource_controller::workload::host::PrimaryCpu>,
        files: Vec<File>,
    ) -> io::Result<Vec<Lease>> {
        use trust_resource_controller::Cpu;
        self.validate()?;
        let (device, inode) = self.native_manifest_identity()?;
        let Cpu::CooperativeShared { ceiling, native_manifest } = context.cpu else {
            return Err(invalid("workload original root is not cooperative"));
        };
        let width = self.native.slots().get();
        if native_manifest.device != device
            || native_manifest.inode != inode
            || ceiling != width
            || files.len() != width as usize
            || self.reserved()? != width
        {
            return Err(invalid("original workload domain or retained exclusion differs"));
        }
        if observations.len() != files.len() {
            return Err(invalid("original workload set differs"));
        }
        let mut leases = Vec::with_capacity(files.len());
        for (file, observed) in files.into_iter().zip(observations) {
            leases.push(self.native.continue_workload_original(observed.slot, file)?);
        }
        // Closing all originals on failure leaves the host's live set and its
        // durable exclusion intact; it never returns a partial set to startup.
        Ok(leases)
    }
    /// Admit one complete native domain, or nothing, under ONE manifest
    /// transaction. Original private recovery material must already be bound
    /// and durably persisted by the custodian before any publication.
    ///
    /// Existing native work or retained/unknown debt leaves the preparation
    /// unconsumed and returns None. No partial native acquisition is kept while
    /// waiting. Every issued native guard is paired with matching durable
    /// exclusion before any capability is returned to execution. Only an
    /// original held-only continuation may borrow those native guards while
    /// this exclusion exists; ordinary fresh admission remains blocked.
    pub fn try_acquire_all_recoverable(
        &self,
        prepared: &mut PreparedRecovery,
    ) -> io::Result<Option<NativeDomainReservation>> {
        prepared.validate_issuance(self.recovery_domain()?)?;
        let Some(_transaction) = transaction(&self.native)? else { return Ok(None) };
        let domain = self.recovery_domain()?;
        prepared.validate_issuance(domain)?;
        let width = self.native.slots();
        if prepared.width() != width {
            return Err(invalid("all-domain preparation differs from the actual native domain"));
        }
        if self.reserved()? != 0
            || self
                .native
                .snapshot()?
                .iter()
                .any(|slot| !matches!(slot, SlotState::Available { .. }))
        {
            return Ok(None);
        }
        let mut native = Vec::with_capacity(width.get() as usize);
        for _ in 0..width.get() {
            let Some(lease) = self.native.try_acquire_in_transaction(prepared.owner())? else {
                // Nothing has escaped to execution. Closing these unexported
                // original guards rolls back the entire native attempt.
                return Ok(None);
            };
            native.push(lease);
        }
        let mut retained = Vec::with_capacity(width.get() as usize);
        for unit in prepared.take_units()? {
            match self.retained.try_acquire_recoverable(
                prepared.owner(),
                width,
                &domain,
                &prepared.context(),
                &unit,
            ) {
                Ok(Some(lease)) => retained.push(lease),
                result => {
                    // No target or downstream owner received any description.
                    // Conclusively issued prior units can be cancelled; an
                    // uncertain write remains discoverable original debt.
                    let error = result.err().unwrap_or_else(|| {
                        invalid("all-domain exclusion changed inside native transaction")
                    });
                    for lease in retained {
                        lease.settle()?;
                    }
                    return Err(error);
                }
            }
        }
        Ok(Some(NativeDomainReservation { native, retained, domain, context: prepared.context() }))
    }
    /// Observe native slots and retained external slots in one nonblocking
    /// admission transaction, without creating or repairing either domain.
    ///
    /// `None` external state means both activation paths are absent. This is
    /// only a legacy raw observation: callers which already adopted the mixed
    /// protocol must reject that absence, never reinterpret it as zero debt.
    /// Any present or partial sidecar requires a validated retirement. Reported
    /// owners remain diagnostics, not process, grant or settlement authority.
    pub fn observe(
        native: &Pool,
        retirement: Option<&LegacyRetirement>,
    ) -> io::Result<(Vec<SlotState>, Option<Vec<RetainedSlotState>>)> {
        let _transaction =
            transaction(native)?.ok_or_else(|| io::Error::from(io::ErrorKind::WouldBlock))?;
        if let Some(retirement) = retirement {
            retirement.validate()?;
        }
        let present = activation_present(native)?;
        let external = if present {
            let retirement = retirement
                .ok_or_else(|| invalid("external CPU state needs a validated retirement"))?;
            let debt = Self::open(native, retirement)?
                .ok_or_else(|| invalid("external CPU activation disappeared during observation"))?;
            let slots = debt.retained.snapshot()?;
            debt.validate()?;
            Some(slots)
        } else {
            None
        };
        Ok((native.snapshot()?, external))
    }

    /// Create a fresh retained sidecar after the host durably fences old clients.
    /// Partial creation stays unavailable after any error or crash. Activation
    /// never adopts a pre-existing private domain or erases outstanding debt.
    /// This scoped primitive does not establish old execution closure. A
    /// machine host must first require canonical prior-boot/full-custody
    /// quiescence and shared memory readiness, not only permission retirement.
    pub fn activate(native: &Pool, retirement: &LegacyRetirement) -> io::Result<Self> {
        retirement.validate()?;
        let _transaction =
            transaction(native)?.ok_or_else(|| io::Error::from(io::ErrorKind::WouldBlock))?;
        let directory = open_parent(native.path())?;
        let mut anchor = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
            .open(native.path().join(ANCHOR))?;
        check_private(&anchor, false)?;
        anchor.write_all(format!("{VERSION} initializing=1\n").as_bytes())?;
        anchor.sync_all()?;
        directory.sync_all()?;
        let retained = RetainedPool::create_private(&native.path().join(DOMAIN), native.slots())?;
        let manifest = manifest(native)?;
        let root = open_parent(retained.path())?;
        let binding = Binding::new(&manifest, &root, native.slots().get(), retirement)?;
        anchor.seek(SeekFrom::Start(0))?;
        anchor.set_len(0)?;
        anchor.write_all(binding.encode().as_bytes())?;
        anchor.sync_all()?;
        directory.sync_all()?;
        Ok(Self { native: native.clone(), retained, binding, retirement: retirement.clone() })
    }

    /// Open the exact activated sidecar. Only absence of both anchor and domain
    /// before activation means no external-debt protocol. Missing or partial
    /// state after activation refuses admission rather than returning zero.
    pub fn open(native: &Pool, retirement: &LegacyRetirement) -> io::Result<Option<Self>> {
        retirement.validate()?;
        let mut anchor = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
            .open(native.path().join(ANCHOR))
        {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return match std::fs::symlink_metadata(native.path().join(DOMAIN)) {
                    Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
                    _ => Err(invalid("external CPU domain has no readiness anchor")),
                };
            }
            Err(error) => return Err(error),
        };
        check_private(&anchor, false)?;
        let binding = Binding::parse(&read_text(&mut anchor, 512)?)?;
        let retained = RetainedPool::open_existing(&native.path().join(DOMAIN))?
            .ok_or_else(|| invalid("activated external CPU domain is missing"))?;
        let value =
            Self { native: native.clone(), retained, binding, retirement: retirement.clone() };
        value.validate()?;
        Ok(Some(value))
    }

    pub(crate) fn retained_identity(&self) -> (u64, u64) {
        (self.binding.root_dev, self.binding.root_ino)
    }

    /// Count both live holders and crash-retained debt. Call this while holding
    /// the native manifest transaction when using it to admit native work.
    pub fn reserved(&self) -> io::Result<u32> {
        self.validate()?;
        Ok(self
            .retained
            .snapshot()?
            .iter()
            .filter(|slot| !matches!(slot, RetainedSlotState::Available { .. }))
            .count() as u32)
    }

    /// Bound native admission without double-counting external CPU usage
    /// already reflected by the host's live native-worker policy.
    pub fn native_limit(&self, policy_limit: u32) -> io::Result<u32> {
        Ok(policy_limit.min(self.native.slots().get().saturating_sub(self.reserved()?)))
    }

    /// Acquire one native v3 credit under the same transaction as external
    /// reservations. Raw legacy Pool clients are excluded by retirement and
    /// must not participate in the activated v3 domain.
    pub fn try_acquire_native(&self, owner: Owner, policy_limit: u32) -> io::Result<Option<Lease>> {
        self.try_acquire_observed(owner, |_| policy_limit)
    }

    /// Evaluate a bounded cached native policy while holding the shared native
    /// manifest transaction. The callback must not query processes or acquire
    /// the same manifest recursively.
    pub fn try_acquire_observed(
        &self,
        owner: Owner,
        policy_limit: impl FnOnce(u32) -> u32,
    ) -> io::Result<Option<Lease>> {
        let Some(_transaction) = transaction(&self.native)? else { return Ok(None) };
        let held = self
            .native
            .snapshot()?
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count() as u32;
        let limit = self.native_limit(policy_limit(held))?;
        if held >= limit {
            return Ok(None);
        }
        self.native.try_acquire_in_transaction(owner)
    }

    /// Reuse an inherited continuation under the SAME transaction as native
    /// and retained grants. This permits only an already-counted slot or its
    /// serialized replacement, never an unbudgeted exact-OFD assumption.
    /// None preserves the original file for nonblocking busy/policy retries.
    pub fn try_adopt_inherited(
        &self,
        file: &File,
        policy: impl FnOnce(u32) -> u32,
    ) -> io::Result<Option<Lease>> {
        self.adopt_with(file, policy, || {})
    }
    fn adopt_with(
        &self,
        file: &File,
        policy: impl FnOnce(u32) -> u32,
        after_probe: impl FnOnce(),
    ) -> io::Result<Option<Lease>> {
        let Some(_transaction) = transaction(&self.native)? else { return Ok(None) };
        self.validate()?;
        let held = self
            .native
            .snapshot()?
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count() as u32;
        if held > self.native_limit(policy(held))? {
            return Ok(None);
        };
        self.native.adopt_in_transaction_with(file, after_probe).map(Some)
    }

    /// Reserve a complete fixed-width external job, or nothing, under the same
    /// native manifest lock used by native workers. Returned capabilities go
    /// directly to the execution custodian; Drop never settles their debt.
    /// `limit` is a total active-work ceiling, not the native-only policy limit.
    pub fn try_reserve(
        &self,
        owner: Owner,
        width: NonZeroU32,
        limit: u32,
    ) -> io::Result<Option<Vec<RetainedLease>>> {
        let mut prepared = PreparedReservation::new(width)?;
        self.try_reserve_prepared(owner, &mut prepared, limit)
    }

    /// Reserve exactly the nonces already persisted by the actual custodian.
    /// Room/transaction refusal leaves the complete plan unchanged for retry.
    /// After consumption any partial failure is uncertain debt discoverable by
    /// those original nonces; it never authorizes execution or plan reuse.
    pub fn try_reserve_prepared(
        &self,
        owner: Owner,
        prepared: &mut PreparedReservation,
        limit: u32,
    ) -> io::Result<Option<Vec<RetainedLease>>> {
        prepared.nonces()?;
        let width = prepared.width();
        let Some(_transaction) = transaction(&self.native)? else { return Ok(None) };
        self.validate()?;
        let native = self
            .native
            .snapshot()?
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count() as u32;
        let used = native.saturating_add(self.reserved()?);
        let limit = limit.min(self.native.slots().get());
        if width.get() > limit.saturating_sub(used) {
            return Ok(None);
        }
        let mut leases = Vec::with_capacity(width.get() as usize);
        for nonce in prepared.take()? {
            match self.retained.try_acquire_prepared(owner, nonce) {
                Ok(Some(lease)) => leases.push(lease),
                result => {
                    // No execution has received these capabilities, so this
                    // function can conclusively cancel its partial reservation.
                    let error = result.err().unwrap_or_else(|| {
                        invalid("external CPU availability changed inside native transaction")
                    });
                    for lease in leases {
                        lease.settle()?;
                    }
                    return Err(error);
                }
            }
        }
        Ok(Some(leases))
    }

    /// Mint original private recovery material before any CPU publication.
    /// Context must bind the custodian's durable attempt and actual memory epoch.
    pub fn prepare_recoverable(
        &self,
        owner: Owner,
        width: NonZeroU32,
        context: [u8; 32],
    ) -> io::Result<RecoveryMaterial> {
        if width.get() > self.native.slots().get() {
            return Err(invalid("recoverable width exceeds native pool"));
        }
        RecoveryMaterial::mint(self.recovery_domain()?, owner, width, context)
    }

    /// Issue exactly one durably persisted original secret-backed bundle.
    /// A room refusal preserves the unused original preparation. Disk-reopened
    /// material has a different type and cannot enter this method.
    pub fn try_reserve_recoverable(
        &self,
        prepared: &mut PreparedRecovery,
        limit: u32,
    ) -> io::Result<Option<Vec<RetainedLease>>> {
        prepared.validate_issuance(self.recovery_domain()?)?;
        let Some(_transaction) = transaction(&self.native)? else { return Ok(None) };
        let domain = self.recovery_domain()?;
        prepared.validate_issuance(domain)?;
        let native = self
            .native
            .snapshot()?
            .iter()
            .filter(|slot| matches!(slot, SlotState::Held { .. }))
            .count() as u32;
        let used = native.saturating_add(self.reserved()?);
        let width = prepared.width();
        if width.get() > limit.min(self.native.slots().get()).saturating_sub(used) {
            return Ok(None);
        }
        let owner = prepared.owner();
        let context = prepared.context();
        let mut leases = Vec::with_capacity(width.get() as usize);
        for unit in prepared.take_units()? {
            match self.retained.try_acquire_recoverable(owner, width, &domain, &context, &unit) {
                Ok(Some(lease)) => leases.push(lease),
                result => {
                    let error = result.err().unwrap_or_else(|| {
                        invalid("recoverable CPU availability changed inside transaction")
                    });
                    // No unit escaped to execution. Earlier complete capabilities
                    // can be cancelled; uncertain writes remain discoverable debt.
                    for lease in leases {
                        lease.settle()?;
                    }
                    return Err(error);
                }
            }
        }
        Ok(Some(leases))
    }

    /// Restore only the ORIGINAL private secret capability, never a public
    /// identity/nonce or a fresh admission. This establishes no work closure.
    pub fn restore_recovery(&self, parent: &Path, leaf: &str) -> io::Result<RecoveredReservation> {
        let authority = RecoveryAuthority::open(parent, leaf)?;
        let Some(_transaction) = transaction(&self.native)? else {
            return Err(io::ErrorKind::WouldBlock.into());
        };
        if authority.domain() != self.recovery_domain()? {
            return Err(invalid("recovery material belongs to another actual domain"));
        }
        self.retained.restore_original(authority)
    }

    /// Observe current occupied generations in the actual bounded native
    /// domain. These locators confer no rights and may be stale immediately.
    pub fn recovery_candidates(&self) -> io::Result<Vec<crate::RecoveryCandidate>> {
        self.validate()?;
        self.retained.recovery_candidates()
    }

    /// Restore only the actual per-unit private key matching this current
    /// native slot commitment. Locator DATA never creates authority. A stale
    /// observation returns None; unrelated live slots are neither locked nor
    /// inferred closed. Actual scope closure remains the custodian's duty.
    pub fn restore_unit_recovery(
        &self,
        parent: &Path,
        leaf: &str,
        candidate: crate::RecoveryCandidate,
    ) -> io::Result<Option<RecoveredReservation>> {
        let authority = RecoveryAuthority::open(parent, leaf)?;
        let Some(_transaction) = transaction(&self.native)? else {
            return Err(io::ErrorKind::WouldBlock.into());
        };
        if authority.domain() != self.recovery_domain()? {
            return Err(invalid("unit recovery material belongs to another actual domain"));
        }
        self.retained.restore_unit_original(authority, candidate)
    }

    fn recovery_domain(&self) -> io::Result<[u8; 32]> {
        self.validate()?;
        let (dev, ino) = self.retained.manifest_identity()?;
        let mut hash = Sha256::new();
        hash.update(b"trust-build-cpu/external-recovery-domain/v1\0");
        hash.update(self.binding.encode().as_bytes());
        hash.update(dev.to_be_bytes());
        hash.update(ino.to_be_bytes());
        Ok(hash.finalize().into())
    }

    /// Exact private domain location for the custodian's durable recovery data.
    /// A path alone is never a capability to settle a claim.
    pub fn path(&self) -> &Path {
        self.retained.path()
    }

    /// Checked original native manifest device/inode for authenticated host
    /// observations. These numbers grant neither CPU nor settlement authority.
    pub fn native_manifest_identity(&self) -> io::Result<(u64, u64)> {
        self.validate()?;
        Ok((self.binding.native_dev, self.binding.native_ino))
    }

    #[cfg(feature = "jobserver")]
    pub(crate) fn native_pool(&self) -> io::Result<Pool> {
        self.validate()?;
        Ok(self.native.clone())
    }

    fn validate(&self) -> io::Result<()> {
        self.retirement.validate()?;
        let manifest = manifest(&self.native)?;
        if self.retained.slots() != self.native.slots() {
            return Err(invalid("external CPU capacity differs from native pool"));
        }
        let root = open_parent(self.retained.path())?;
        if Binding::new(&manifest, &root, self.native.slots().get(), &self.retirement)?
            != self.binding
        {
            return Err(invalid("external CPU domain or native manifest identity changed"));
        }
        let mut anchor = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
            .open(self.native.path().join(ANCHOR))?;
        check_private(&anchor, false)?;
        if Binding::parse(&read_text(&mut anchor, 512)?)? != self.binding {
            return Err(invalid("external CPU readiness binding changed"));
        }
        Ok(())
    }
}

fn manifest(native: &Pool) -> io::Result<File> {
    // snapshot validates the native pool's retained path/inode identities.
    native.snapshot()?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(native.path().join("pool"))?;
    check_private(&file, false)?;
    Ok(file)
}

fn transaction(native: &Pool) -> io::Result<Option<Probe>> {
    let file = manifest(native)?;
    match file.try_lock() {
        Ok(()) => {
            let guard = Probe(file);
            native.snapshot()?;
            Ok(Some(guard))
        }
        Err(std::fs::TryLockError::WouldBlock) => Ok(None),
        Err(std::fs::TryLockError::Error(error)) => Err(error),
    }
}

impl Binding {
    fn new(
        native: &File,
        root: &File,
        width: u32,
        retirement: &LegacyRetirement,
    ) -> io::Result<Self> {
        let native = native.metadata()?;
        let root = root.metadata()?;
        let (legacy_dev, legacy_ino) = retirement.directory_identity();
        Ok(Self {
            native_dev: native.dev(),
            native_ino: native.ino(),
            root_dev: root.dev(),
            root_ino: root.ino(),
            width,
            legacy_dev,
            legacy_ino,
            legacy_boot: retirement.retired_boot_id().to_owned(),
        })
    }

    fn encode(&self) -> String {
        format!(
            "{VERSION} native-dev={} native-ino={} root-dev={} root-ino={} legacy-dev={} legacy-ino={} legacy-boot={} slots={} ready=1\n",
            self.native_dev,
            self.native_ino,
            self.root_dev,
            self.root_ino,
            self.legacy_dev,
            self.legacy_ino,
            self.legacy_boot,
            self.width
        )
    }

    fn parse(text: &str) -> io::Result<Self> {
        let words: Vec<_> = text.trim_end_matches('\n').split(' ').collect();
        if words.len() != 10 || words[0] != VERSION || words[9] != "ready=1" {
            return Err(invalid("incomplete external CPU readiness binding"));
        }
        let number = |index: usize, prefix: &str| {
            words[index]
                .strip_prefix(prefix)
                .and_then(|number| number.parse::<u64>().ok())
                .ok_or_else(|| invalid("invalid external CPU readiness number"))
        };
        let value = Self {
            native_dev: number(1, "native-dev=")?,
            native_ino: number(2, "native-ino=")?,
            root_dev: number(3, "root-dev=")?,
            root_ino: number(4, "root-ino=")?,
            legacy_dev: number(5, "legacy-dev=")?,
            legacy_ino: number(6, "legacy-ino=")?,
            legacy_boot: words[7]
                .strip_prefix("legacy-boot=")
                .filter(|boot| boot.len() == 36)
                .ok_or_else(|| invalid("invalid retired boot binding"))?
                .to_owned(),
            width: u32::try_from(number(8, "slots=")?)
                .map_err(|_| invalid("invalid external CPU width"))?,
        };
        if value.width == 0 || value.encode() != text {
            return Err(invalid("noncanonical external CPU readiness binding"));
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests;

// Both absent means legacy only. Any partial or foreign activation must prevent
// raw physical acquisition; only the checked debt transaction may admit work.
pub(crate) fn activation_present(native: &Pool) -> io::Result<bool> {
    [ANCHOR, DOMAIN].into_iter().try_fold(false, |present, name| {
        match std::fs::symlink_metadata(native.path().join(name)) {
            Ok(_) => Ok(true),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(present),
            Err(error) => Err(error),
        }
    })
}

/// Actual all-domain native originals and the opaque authenticated receipt.
/// No public constructor from leases, observations or descriptor paths exists.
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub struct NativeJobOriginals {
    leases: Option<Vec<Lease>>,
    // LAST: original leases and control close before this incoming reservation.
    startup: trust_resource_controller::client::native_job::AuthenticatedNativeJobStartup,
}

/// One actual initial pair plus the opaque authenticated original channel.
/// Neither a partial V1 reply nor a scalar ceiling can construct this owner.
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub struct InitialNativeOriginals {
    reply: trust_resource_controller::workload::host::initial::ReadyReply,
    primary: Lease,
    control: trust_resource_controller::client::workload::WorkloadControl,
    keeper: std::sync::Arc<trust_resource_controller::client::workload::AuthenticatedInitialKeeper>,
}
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
impl InitialNativeOriginals {
    /// The ready reply this Initial host delivered, for observation only.
    pub fn observation(&self) -> &trust_resource_controller::workload::host::initial::ReadyReply {
        &self.reply
    }
    /// Consume this owner into its ready reply, primary lease, workload
    /// control and authenticated keeper; the caller takes custody of each.
    pub fn into_originals(
        self,
    ) -> (
        trust_resource_controller::workload::host::initial::ReadyReply,
        Lease,
        trust_resource_controller::client::workload::WorkloadControl,
        std::sync::Arc<trust_resource_controller::client::workload::AuthenticatedInitialKeeper>,
    ) {
        (self.reply, self.primary, self.control, self.keeper)
    }
}

/// Actual same-channel replacement originals for one still-parked Root phase.
/// It cannot be constructed from decoded metadata or cloned from another phase.
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub struct PartialNativeOriginals {
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    phase: [u8; 16],
    ordinal: u64,
    funded_before: usize,
    leases: Vec<Lease>,
}
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
impl PartialNativeOriginals {
    /// Negative consistency check against the same Root's actual held prefix.
    pub fn funded_before(&self) -> usize {
        self.funded_before
    }
    /// Binding observations are restrictions, not standalone grant authority.
    pub fn binding(&self) -> ([u8; 16], [u8; 32], [u8; 16], u64) {
        (self.root_attempt, self.invocation_sha256, self.phase, self.ordinal)
    }
    /// Consume the actual adopted guards; no acquisition or path reopen occurs.
    pub fn into_leases(self) -> Vec<Lease> {
        self.leases
    }
}
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
impl NativeJobOriginals {
    /// The authenticated original Host's ready reply: observation data that
    /// grants no lease, loan or control by itself.
    pub fn observation(&self) -> &trust_resource_controller::native_job::host::ReadyReply {
        self.startup.observation()
    }
    /// Transfer the original authenticated control connection, exactly once;
    /// a second call is refused.
    pub fn take_control(
        &mut self,
    ) -> io::Result<trust_resource_controller::client::workload::WorkloadControl> {
        self.startup.take_control()
    }
    /// A retained native bank takes these exactly once and keeps THIS opaque
    /// receipt after every adopted Lease and all its descendant loans close.
    pub fn take_leases(&mut self) -> io::Result<Vec<Lease>> {
        self.leases.take().ok_or_else(|| invalid("native-job originals already banked"))
    }
}

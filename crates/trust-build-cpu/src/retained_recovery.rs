// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Restoration of original secret-backed ownership, never a new admission.
use super::*;
use crate::recovery_material::{RecoveryAuthority, RecoveryUnit, commitment};

/// Original settlement ownership restored from its private secret capability.
/// This is not evidence that its work ended and cannot issue or launch work.
pub struct RecoveredReservation {
    authority: RecoveryAuthority,
    leases: Vec<RetainedLease>,
}

/// A bounded locator observation, never a claim/recovery/settlement capability.
/// The actual private key and current slot commitment are independently checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecoveryCandidate {
    /// Slot in the actual original retained domain.
    pub slot: u32,
    /// Observed generation, used only to reject stale candidate lookup.
    pub nonce: [u8; 16],
}
impl RecoveredReservation {
    /// Host context originally committed before grant.
    pub fn context(&self) -> [u8; 32] {
        self.authority.context()
    }
    /// Original declared bundle width, not a newly granted width.
    pub fn width(&self) -> NonZeroU32 {
        self.authority.width()
    }
    /// Number of original records still present. A partial publication or
    /// previously settled subset can make this less than the declared width.
    pub fn retained_units(&self) -> usize {
        self.leases.len()
    }
    /// Observe only the exact currently owned durable debt generations.
    pub fn identities(&self) -> io::Result<Vec<RetainedLeaseIdentity>> {
        self.leases.iter().map(RetainedLease::identity).collect()
    }
    /// Exercise the restored ORIGINAL settlement authority once.
    /// The custodian MUST first establish authenticated original memory-cohort
    /// closure or the applicable same-host later-boot closure. Possession of
    /// this capability, a PID, an exit code or these observations is not closure.
    /// A write error may have consumed a unit; never retry a consumed unit.
    pub fn settle(mut self) -> io::Result<()> {
        while let Some(lease) = self.leases.pop() {
            lease.settle()?;
        }
        Ok(())
    }
}
impl RetainedPool {
    pub(crate) fn recovery_candidates(&self) -> io::Result<Vec<RecoveryCandidate>> {
        self.validate()?;
        let mut candidates = Vec::new();
        for slot in 0..self.0.slots.get() {
            let mut file = self.open_slot(slot, false)?;
            if let State::Retained { nonce, .. } = read_record(&mut file, slot)? {
                candidates.push(RecoveryCandidate { slot, nonce });
            }
        }
        self.validate()?;
        Ok(candidates)
    }

    pub(crate) fn restore_unit_original(
        &self,
        authority: RecoveryAuthority,
        observed: RecoveryCandidate,
    ) -> io::Result<Option<RecoveredReservation>> {
        self.validate()?;
        if authority.width().get() != 1
            || authority.units().len() != 1
            || authority.units()[0].nonce != observed.nonce
        {
            return Err(invalid("unit key differs from its observed locator"));
        }
        let mut candidate = Candidate::lock(self.open_slot(observed.slot, true)?)?;
        let (owner, nonce, recovery) = match read_record(candidate.file()?, observed.slot)? {
            State::Retained { owner, nonce, recovery } if nonce == observed.nonce => {
                (owner, nonce, recovery)
            }
            _ => return Ok(None), // Stale lookup; no capability was created.
        };
        let unit = &authority.units()[0];
        let expected = commitment(
            &authority.domain(),
            authority.owner(),
            authority.width(),
            &authority.context(),
            unit,
            observed.slot,
        );
        if owner != authority.owner() || recovery != Some(expected) {
            return Err(invalid("unit private recovery commitment differs"));
        }
        let lease = RetainedLease {
            pool: self.clone(),
            slot: observed.slot,
            owner,
            nonce,
            recovery,
            file: candidate.take()?,
            settlement_attempted: false,
            rekey: None,
        };
        self.validate()?;
        Ok(Some(RecoveredReservation { authority, leases: vec![lease] }))
    }
    pub(crate) fn manifest_identity(&self) -> io::Result<(u64, u64)> {
        self.validate()?;
        Ok((self.0.manifest.dev, self.0.manifest.ino))
    }
    pub(crate) fn try_acquire_recoverable(
        &self,
        owner: Owner,
        width: NonZeroU32,
        domain: &[u8; 32],
        context: &[u8; 32],
        unit: &RecoveryUnit,
    ) -> io::Result<Option<RetainedLease>> {
        self.acquire_with(owner, unit.nonce, |slot| {
            Some(commitment(domain, owner, width, context, unit, slot))
        })
    }
    pub(crate) fn restore_original(
        &self,
        authority: RecoveryAuthority,
    ) -> io::Result<RecoveredReservation> {
        self.validate()?;
        let units = authority
            .units()
            .iter()
            .enumerate()
            .map(|(index, unit)| (unit.nonce, index))
            .collect::<std::collections::BTreeMap<_, _>>();
        if units.len() != authority.units().len() {
            return Err(invalid("duplicate recovery generation"));
        }
        let mut leases = Restoring(Vec::new());
        for slot in 0..self.0.slots.get() {
            let mut candidate = Candidate::lock(self.open_slot(slot, true)?)?;
            match read_record(candidate.file()?, slot)? {
                State::Retained { owner, nonce, recovery: Some(observed) }
                    if units.contains_key(&nonce) =>
                {
                    let unit = &authority.units()[units[&nonce]];
                    let expected = commitment(
                        &authority.domain(),
                        authority.owner(),
                        authority.width(),
                        &authority.context(),
                        unit,
                        slot,
                    );
                    if owner != authority.owner() || expected != observed {
                        return Err(invalid("original recovery commitment differs"));
                    }
                    leases.0.push(RetainedLease {
                        settlement_attempted: false,
                        rekey: None,
                        pool: self.clone(),
                        slot,
                        owner,
                        nonce,
                        recovery: Some(observed),
                        file: candidate.take()?,
                    });
                }
                State::Retained { nonce, recovery: None, .. } if units.contains_key(&nonce) => {
                    return Err(invalid("public nonce cannot restore settlement authority"));
                }
                _ => {}
            }
        }
        self.validate()?;
        if leases.0.len() > authority.width().get() as usize {
            return Err(invalid("recovery bundle exceeds original width"));
        }
        Ok(RecoveredReservation { authority, leases: leases.into_leases() })
    }
}

/// The leases a restoration has validated so far, until it returns them. A
/// later refusal (a busy, unreadable or damaged slot; a record of one of the
/// authority's nonces whose owner or commitment differs, or that has no
/// recovery commitment; a changed pool; an excess width) unlocks each before
/// close, as a refused candidate does: every concurrent spawn holds a copy of
/// each descriptor until its exec, and a slot released only by the final
/// close would read as held work, not as the retained debt it still is, for
/// as long as that copy lives. Records of other generations are skipped, not
/// refused.
struct Restoring(Vec<RetainedLease>);
impl Restoring {
    fn into_leases(mut self) -> Vec<RetainedLease> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for Restoring {
    fn drop(&mut self) {
        for lease in &self.0 {
            // A failed unlock leaves the release to the final close.
            let _ = lease.file.unlock();
        }
    }
}

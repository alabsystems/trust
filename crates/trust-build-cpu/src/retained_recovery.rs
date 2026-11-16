// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Restoration of original secret-backed ownership, never a new admission.
use super::*;
use crate::recovery_material::{RecoveryAuthority, RecoveryUnit, commitment};

/// Original settlement ownership restored from its private secret capability.
/// This is not evidence that its work ended and cannot issue or launch work.
pub struct RecoveredReservation {
    authority: RecoveryAuthority,
    leases: Restored,
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
        self.leases.0.len()
    }
    /// Observe only the exact currently owned durable debt generations.
    pub fn identities(&self) -> io::Result<Vec<RetainedLeaseIdentity>> {
        self.leases.0.iter().map(RetainedLease::identity).collect()
    }
    /// Exercise the restored ORIGINAL settlement authority once.
    /// The custodian MUST first establish authenticated original memory-cohort
    /// closure or the applicable same-host later-boot closure. Possession of
    /// this capability, a PID, an exit code or these observations is not closure.
    /// A write error may have consumed a unit; never retry a consumed unit.
    /// Every slot, settled or not, is unlocked as this returns, before its
    /// close; an error stops at the slot it reached.
    pub fn settle(mut self) -> io::Result<()> {
        for lease in self.leases.0.iter_mut().rev() {
            lease.settle_held()?;
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
        let leases = Restored(vec![RetainedLease {
            pool: self.clone(),
            slot: observed.slot,
            owner,
            nonce,
            recovery,
            file: candidate.take()?,
            settlement_attempted: false,
            rekey: None,
        }]);
        self.validate()?;
        Ok(Some(RecoveredReservation { authority, leases }))
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
        let mut leases = Restored(Vec::new());
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
        Ok(RecoveredReservation { authority, leases })
    }
}

/// Restored leases: those a restoration has validated so far, then its
/// reservation's. Every exit unlocks each before close, as a refused candidate
/// does: a restoration's later refusal (a busy, unreadable or damaged slot; a
/// record of one of the authority's nonces whose owner or commitment differs,
/// or that has no recovery commitment; a changed pool; an excess width), a
/// reservation dropped unsettled, and its settlement, whether it succeeds or
/// refuses or fails part-way. Each description was opened by this restoration
/// and a reservation launches no work, so no child holds one on purpose, but
/// every concurrent spawn holds a copy of each until its exec, and a slot
/// released only by the final close would read as held work for as long as
/// that copy lives, whatever its record holds. Only a successful restoration
/// hands the guard on, to its reservation. Records of other generations are
/// skipped, not refused.
struct Restored(Vec<RetainedLease>);
impl Drop for Restored {
    fn drop(&mut self) {
        for lease in &self.0 {
            // A failed unlock leaves the release to the final close.
            let _ = lease.file.unlock();
        }
    }
}

#[cfg(test)]
mod reservation_tests {
    use std::fs::OpenOptions;

    use super::*;
    use crate::recovery_material::RecoveryMaterial;
    use crate::tests::descriptor_copy::{Unexecuted, relockable};

    fn slot_path(pool: &RetainedPool, slot: u32) -> PathBuf {
        pool.path().join(RETAINED_DIRECTORY_NAME).join(slot_name(slot))
    }

    /// A pool of `width` slots, each holding one original unit of the same
    /// recovery material as an issued bundle leaves it once its lease has
    /// closed, and that material's authority.
    fn restorable(directory: &Path, width: NonZeroU32) -> (RetainedPool, RecoveryAuthority) {
        let pool = RetainedPool::create_private(&directory.join("retained"), width).unwrap();
        let store = directory.join("authority");
        crate::tests::private_dir(&store);
        let store = store.canonicalize().unwrap();
        let material =
            RecoveryMaterial::mint([1; 32], Owner::current(None), width, [2; 32]).unwrap();
        drop(material.persist(&store, "grant").unwrap());
        let authority = RecoveryAuthority::open(&store, "grant").unwrap();
        for unit in authority.units() {
            let issued = pool
                .try_acquire_recoverable(
                    authority.owner(),
                    authority.width(),
                    &authority.domain(),
                    &authority.context(),
                    unit,
                )
                .unwrap()
                .expect("a free slot is claimed");
            drop(issued);
        }
        (pool, authority)
    }

    fn retained(owner: Owner, slots: &[u32]) -> Vec<RetainedSlotState> {
        slots
            .iter()
            .map(|&slot| RetainedSlotState::Retained { slot, reported_owner: owner })
            .collect()
    }

    #[test]
    fn a_dropped_reservation_unlocks_its_slots_while_a_spawn_holds_a_copy() {
        // The copy holds every open description: own the descriptor table.
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let (pool, authority) = restorable(directory.path(), NonZeroU32::new(2).unwrap());
        let owner = authority.owner();
        let reservation = pool.restore_original(authority).unwrap();
        assert_eq!(reservation.retained_units(), 2, "restoration did not restore both slots");
        // A spawn that began while the reservation held both slots.
        let copy = Unexecuted::copy(&fixture);
        drop(reservation);
        let relocked = [0, 1].map(|slot| relockable(&slot_path(&pool, slot)));
        let snapshot = pool.snapshot();
        // Kill and reap the copy before asserting.
        drop(copy);
        drop(fixture);
        assert_eq!(
            relocked, [true; 2],
            "a dropped reservation kept its slots locked through a spawn's copy"
        );
        assert_eq!(
            snapshot.unwrap(),
            retained(owner, &[0, 1]),
            "a dropped reservation's slots read as held work, not as the debt they still are"
        );
    }

    #[test]
    fn a_dropped_unit_reservation_unlocks_its_slot_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let (pool, authority) = restorable(directory.path(), NonZeroU32::MIN);
        let owner = authority.owner();
        let [observed] = pool.recovery_candidates().unwrap()[..] else {
            panic!("the one issued unit is not the one candidate")
        };
        let reservation = pool
            .restore_unit_original(authority, observed)
            .unwrap()
            .expect("the observed unit is current");
        assert_eq!(reservation.retained_units(), 1, "unit restoration did not restore its slot");
        let copy = Unexecuted::copy(&fixture);
        drop(reservation);
        let relocked = relockable(&slot_path(&pool, observed.slot));
        let snapshot = pool.snapshot();
        drop(copy);
        drop(fixture);
        assert!(relocked, "a dropped unit reservation kept its slot locked through a spawn's copy");
        assert_eq!(snapshot.unwrap(), retained(owner, &[observed.slot]));
    }

    #[test]
    fn a_settled_reservation_unlocks_its_slots_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let (pool, authority) = restorable(directory.path(), NonZeroU32::new(2).unwrap());
        let reservation = pool.restore_original(authority).unwrap();
        let copy = Unexecuted::copy(&fixture);
        let settled = reservation.settle();
        let relocked = [0, 1].map(|slot| relockable(&slot_path(&pool, slot)));
        let snapshot = pool.snapshot();
        drop(copy);
        drop(fixture);
        settled.unwrap();
        assert_eq!(
            relocked, [true; 2],
            "a settled reservation kept its slots locked through a spawn's copy"
        );
        assert_eq!(
            snapshot.unwrap(),
            [0, 1].map(|slot| RetainedSlotState::Available { slot }),
            "settled slots read as held work, not as free"
        );
    }

    #[test]
    fn a_failed_settlement_unlocks_every_slot_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let (pool, authority) = restorable(directory.path(), NonZeroU32::new(3).unwrap());
        let owner = authority.owner();
        let reservation = pool.restore_original(authority).unwrap();
        assert_eq!(reservation.retained_units(), 3, "restoration did not restore every slot");
        // After restoration the middle slot's record names another generation,
        // so settlement settles one end slot, refuses the middle one before
        // writing it, and never reaches the other end.
        let mut middle = OpenOptions::new().write(true).open(slot_path(&pool, 1)).unwrap();
        let foreign = State::Retained { owner, nonce: [9; 16], recovery: None };
        write_record(&mut middle, &foreign.encode(1)).unwrap();
        drop(middle);
        let before = [0, 1, 2].map(|slot| std::fs::read(slot_path(&pool, slot)).unwrap());
        // A spawn that began while the reservation held every slot.
        let copy = Unexecuted::copy(&fixture);
        let settled = reservation.settle();
        let relocked = [0, 1, 2].map(|slot| relockable(&slot_path(&pool, slot)));
        let snapshot = pool.snapshot();
        // Kill and reap the copy before asserting.
        drop(copy);
        drop(fixture);
        assert_eq!(settled.err().map(|error| error.kind()), Some(io::ErrorKind::InvalidData));
        let after = [0, 1, 2].map(|slot| std::fs::read(slot_path(&pool, slot)).unwrap());
        let free = |slot: u32| after[slot as usize] == State::Free.encode(slot).into_bytes();
        let (done, untried): (u32, u32) = match (free(0), free(2)) {
            (true, false) => (0, 2),
            (false, true) => (2, 0),
            ends => panic!("settlement did not settle exactly one end slot first: {ends:?}"),
        };
        let at = untried as usize;
        assert_eq!(after[1], before[1], "a refused settlement wrote its slot");
        assert_eq!(after[at], before[at], "settlement went on past its refusal");
        assert!(
            relocked[done as usize],
            "a failed settlement kept a slot it settled locked through a spawn's copy"
        );
        assert!(relocked[1], "a refused settlement kept its slot locked through a spawn's copy");
        assert!(
            relocked[at],
            "a failed settlement kept a slot it never reached locked through a spawn's copy"
        );
        let snapshot = snapshot.unwrap();
        assert_eq!(snapshot[done as usize], RetainedSlotState::Available { slot: done });
        assert_eq!(
            vec![snapshot[1], snapshot[at]],
            retained(owner, &[1, untried]),
            "a failed settlement's unsettled slots read as held work, not as the debt they hold"
        );
    }
}

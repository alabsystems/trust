// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Change recovery custody of the SAME occupied native shadow unit. There is
//! never a Free transition, fresh slot, scalar admission or copied capability.

use super::*;
use crate::recovery_material::{PreparedRecovery, commitment};

pub(super) struct Pending {
    nonce: [u8; 16],
    recovery: [u8; 32],
    context: [u8; 32],
    write_started: bool,
}

impl std::fmt::Debug for Pending {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("PendingRecoveryTransfer")
            .field("write_started", &self.write_started)
            .finish_non_exhaustive()
    }
}

impl RetainedLease {
    /// Bind one original occupied unit to a newly persisted immutable recovery
    /// capability. Caller must establish the new scope before exporting work;
    /// returning a live unit requires real original SDK/cohort exclusion FIRST.
    /// Old recovery keys cannot settle the new nonce. This is not scope closure.
    pub(crate) fn rekey_recoverable(
        &mut self,
        domain: [u8; 32],
        prepared: &mut PreparedRecovery,
    ) -> io::Result<()> {
        self.rekey_with(domain, prepared, write_record)
    }

    fn rekey_with(
        &mut self,
        domain: [u8; 32],
        prepared: &mut PreparedRecovery,
        mut write: impl FnMut(&mut File, &str) -> io::Result<()>,
    ) -> io::Result<()> {
        if self.settlement_attempted || self.recovery.is_none() {
            return Err(invalid("fixed/unrecoverable or settling CPU custody cannot be converted"));
        }
        prepared.validate(domain)?;
        if prepared.width().get() != 1 || prepared.owner() != self.owner {
            return Err(invalid("unit recovery preparation differs from original owner"));
        }
        if let Some(pending) = &self.rekey {
            if prepared.context() != pending.context
                || prepared.nonces()?.as_slice() != [pending.nonce]
            {
                return Err(invalid(
                    "uncertain recovery transfer must retain its exact preparation",
                ));
            }
        } else {
            // Validate original occupied custody BEFORE consuming any new key.
            self.identity()?;
            prepared.validate_issuance(domain)?;
            let unit = prepared
                .take_units()?
                .pop()
                .ok_or_else(|| invalid("unit recovery preparation is missing"))?;
            if unit.nonce == self.nonce {
                return Err(invalid("recovery transfer reused its original nonce"));
            }
            let recovery = commitment(
                &domain,
                self.owner,
                prepared.width(),
                &prepared.context(),
                &unit,
                self.slot,
            );
            self.rekey = Some(Pending {
                nonce: unit.nonce,
                recovery,
                context: prepared.context(),
                write_started: false,
            });
        }
        self.pool.validate()?;
        let current = self.pool.open_slot(self.slot, false)?;
        if Identity::of(&self.file)? != Identity::of(&current)? {
            return Err(invalid("original recovery transfer slot was replaced"));
        }
        check_private(&self.file, false)?;
        let pending =
            self.rekey.as_ref().ok_or_else(|| invalid("original recovery transfer missing"))?;
        let old = State::Retained { owner: self.owner, nonce: self.nonce, recovery: self.recovery };
        let next = State::Retained {
            owner: self.owner,
            nonce: pending.nonce,
            recovery: Some(pending.recovery),
        };
        match read_record(&mut self.file, self.slot) {
            Ok(record) if record == old || record == next => {}
            Err(error) if pending.write_started && error.kind() == io::ErrorKind::InvalidData => {}
            _ => return Err(invalid("original recovery transfer generation differs")),
        }
        self.rekey
            .as_mut()
            .ok_or_else(|| invalid("original recovery transfer missing"))?
            .write_started = true;
        write(&mut self.file, &next.encode(self.slot))?;
        // Publish the new in-memory identity only AFTER durable native write.
        // Every failure above retains the exact old/new transition and lock.
        let completed =
            self.rekey.take().ok_or_else(|| invalid("original recovery transfer missing"))?;
        self.nonce = completed.nonce;
        self.recovery = Some(completed.recovery);
        Ok(())
    }
}

#[cfg(test)]
#[path = "retained_rekey_tests.rs"]
mod tests;

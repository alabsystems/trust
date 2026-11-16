// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! First-pair preparation with no scalar or all-domain reservation fiction.
use super::*;
use crate::{Owner, PreparedRecovery};

/// An unfunded, non-executable preparation over the actual ready domain.
/// It cannot loan, export or publish a CPU. The first actual native/shadow
/// pair must be acquired durably before conversion into a funded bank.
pub struct PreparingNativeCapacityBank {
    debt: super::super::ExternalDebt,
    bank: ScopedNativeCapacityBank,
    owner: Owner,
    nonce: [u8; 16],
    context: [u8; 32],
}

impl super::super::ExternalDebt {
    /// Bind one original persisted idle key before first machine acquisition.
    /// This allocates no capacity and activates no NativeDomain. Scheduling,
    /// original memory and SDK admission remain the caller's obligations.
    pub fn prepare_partial_capacity_bank(
        &self,
        idle: &PreparedRecovery,
    ) -> io::Result<PreparingNativeCapacityBank> {
        let domain = self.recovery_domain()?;
        idle.validate_issuance(domain)?;
        if idle.width().get() != 1 {
            return Err(invalid("partial bank preparation requires one original unit key"));
        }
        let nonce =
            *idle.nonces()?.first().ok_or_else(|| invalid("original idle nonce missing"))?;
        let width = usize::try_from(self.native.slots().get())
            .map_err(|_| invalid("native domain width is not representable"))?;
        let mut native = Vec::new();
        native.try_reserve_exact(width).map_err(io::Error::other)?;
        native.resize_with(width, || None);
        let mut retained = Vec::new();
        retained.try_reserve_exact(width).map_err(io::Error::other)?;
        retained.resize_with(width, || None);
        let mut borrowed_shadows = Vec::new();
        borrowed_shadows.try_reserve_exact(width).map_err(io::Error::other)?;
        borrowed_shadows.resize_with(width, Weak::new);
        let mut slots = Vec::new();
        slots.try_reserve_exact(width).map_err(io::Error::other)?;
        slots.resize(width, None);
        Ok(PreparingNativeCapacityBank {
            debt: self.clone(),
            bank: ScopedNativeCapacityBank::new(NativeCapacityBank {
                native,
                retained,
                borrowed_shadows,
                slots,
                domain,
                idle_context: idle.context(),
                process: std::process::id(),
                original: Arc::new(()),
                next: 0,
                phase: Phase::Running,
            }),
            owner: idle.owner(),
            nonce,
            context: idle.context(),
        })
    }
}

impl PreparingNativeCapacityBank {
    /// The ordinary original scheduler must select this owner first. Busy
    /// keeps the same preparation; uncertain writes keep both actual guards
    /// inside this owner for an exact-key retry, as in later reacquisition.
    pub fn try_fund(&mut self, idle: &mut PreparedRecovery, policy_limit: u32) -> io::Result<bool> {
        idle.validate(self.debt.recovery_domain()?)?;
        if idle.width().get() != 1
            || idle.context() != self.context
            || idle.owner() != self.owner
            || idle.nonces()?.as_slice() != [self.nonce]
        {
            return Err(invalid("first-pair retry replaced its original persisted key"));
        }
        if self.bank.funded_width() != 0 {
            return Ok(true);
        }
        Ok(self.bank.try_reacquire_idle(&self.debt, idle, policy_limit)?.is_some())
    }

    /// Only genuine committed backing can cross into the loan/export API.
    /// On refusal the SAME preparation and uncertain custody are returned,
    /// boxed, since a preparation is large.
    pub fn into_funded(self) -> Result<ScopedNativeCapacityBank, Box<Self>> {
        if self.bank.funded_width() == 0 || self.bank.has_pending_reacquisition() {
            Err(Box::new(self))
        } else {
            Ok(self.bank)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::tests::{setup, unit_plan, width};
    use super::*;

    #[test]
    fn first_pair_is_genuinely_funded_without_requiring_or_inventing_the_whole_domain() {
        let Some((root, native, debt)) = setup() else { return };
        let outside = debt.try_acquire_native(Owner::current(None), 4).unwrap().unwrap();
        let mut idle = unit_plan(root.path(), &debt, "first-pair", [31; 32]);
        let preparing = debt.prepare_partial_capacity_bank(&idle).unwrap();
        let mut preparing = match preparing.into_funded() {
            Err(original) => *original,
            Ok(_) => panic!("an unfunded preparation cannot enter the loan API"),
        };
        assert!(!preparing.try_fund(&mut idle, 0).unwrap());
        assert_eq!(debt.reserved().unwrap(), 0);
        let mut wrong = unit_plan(root.path(), &debt, "wrong-first-pair", [31; 32]);
        assert!(preparing.try_fund(&mut wrong, 4).is_err());
        wrong.validate_issuance(debt.recovery_domain().unwrap()).unwrap();
        assert!(preparing.try_fund(&mut idle, 4).unwrap());
        assert_eq!(debt.reserved().unwrap(), 1);
        assert!(
            preparing.try_fund(&mut idle, 0).unwrap(),
            "same live owner can observe its already captured pair without issuing again"
        );
        assert!(preparing.try_fund(&mut wrong, 4).is_err());
        assert_eq!(debt.reserved().unwrap(), 1);
        let mut bank = match preparing.into_funded() {
            Ok(bank) => bank,
            Err(_) => panic!("actual committed pair remains unavailable"),
        };
        assert_eq!(bank.width(), 4, "the ceiling is not the funded balance");
        assert_eq!(bank.funded_width(), 1);
        assert!(!bank.is_wholly_idle().unwrap(), "unfunded holes cannot start V1");
        let mut next = unit_plan(root.path(), &debt, "next-real-pair", [31; 32]);
        assert!(bank.try_reacquire_idle(&debt, &mut next, 4).unwrap().is_some());
        assert_eq!(bank.funded_width(), 2);
        assert_eq!(debt.reserved().unwrap(), 2);
        assert_eq!(
            native
                .snapshot()
                .unwrap()
                .iter()
                .filter(|slot| matches!(slot, crate::SlotState::Held { .. }))
                .count(),
            3
        );
        assert!(bank.release_idle(width(1)).unwrap().is_some());
        bank.settle_drained().unwrap(); // No descriptions or execution exported.
        assert_eq!(debt.reserved().unwrap(), 0);
        drop(outside);
        assert!(
            native
                .snapshot()
                .unwrap()
                .iter()
                .all(|slot| matches!(slot, crate::SlotState::Available { .. }))
        );
    }
}

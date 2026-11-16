// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Same-owner supplementary FD/GNU custody across an authenticated CPU phase.
use super::*;
use crate::compiler::resource_fifo::ForeignGnuEscrow;
use trust_resource_controller::client::workload::{CommittedPartialPhase, PreparedPartialPhase};
use trust_resource_controller::workload::host::partial::CpuUnit;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Stage {
    Returned,
    Installed,
    Running,
}
enum PreparationOrigin {
    Runtime,
    Initial,
}
pub(super) struct FundingState {
    phase: Attempt,
    ordinal: u64,
    stage: Stage,
}
impl FundingState {
    pub(super) fn keeper_phase(&self, phase: Attempt) -> bool {
        self.phase == phase && matches!(self.stage, Stage::Returned | Stage::Running)
    }
    pub(super) fn running(&self) -> bool {
        self.stage == Stage::Running
    }
}

/// Retains SAME escrow, original bank and authenticated preparation. Drop of
/// an unsettled escrow invokes original Unknown retirement, never token return.
pub(crate) struct RootPartialPhase {
    bank: Arc<RootCreditBank>,
    prepared: PreparedPartialPhase,
    escrow: Option<ForeignGnuEscrow>,
    gnu_backed: usize,
    origin: PreparationOrigin,
}
impl RootCreditBank {
    pub(crate) fn initial_pending(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.initial_phase.is_some())
    }
    pub(crate) fn initial_ready(&self) -> io::Result<Option<(Attempt, CpuUnit)>> {
        let state = self.lock()?;
        state.usable()?;
        let Some(phase) = state.initial_phase else {
            return Ok(None);
        };
        if !state.parked
            || state.funding.is_some()
            || state.originals.len() != 1
            || state.published != 1
        {
            return Err(invalid(
                "initial pair changed before original GNU preparation",
            ));
        }
        if state.slots.iter().any(Option::is_some) {
            if state.slots.iter().all(|slot| {
                matches!(
                    slot,
                    None | Some(Occupancy::Primary { member: None, .. })
                        | Some(Occupancy::Primary {
                            member: Some(Member {
                                purpose: Purpose::Query,
                                ..
                            }),
                            ..
                        })
                )
            }) {
                return Ok(None);
            }
            return Err(invalid("producing work entered the initial parked bank"));
        }
        let primary = &state.originals[0];
        Ok(Some((
            phase,
            CpuUnit {
                slot: primary.lease.slot(),
                backing: primary.backing,
            },
        )))
    }
    pub(crate) fn more_requested(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.funding.is_some()
            && state.demand
            && (self.live_limit)(state.occupied() as u32).min(self.ceiling)
                > state.published as u32)
    }
    /// Park only a still-full cooperative bank for a negative support probe.
    /// A failed/busy probe releases no capacity and can restore full dispatch.
    pub(crate) fn begin_partial_probe(&self) -> io::Result<Option<CpuUnit>> {
        {
            let mut state = self.lock()?;
            state.usable()?;
            if state.parked || state.funding.is_some() {
                return Ok(None);
            }
            state.parked = true;
        }
        match self.partial_ready()? {
            Some(implicit) => Ok(Some(implicit)),
            None => {
                self.cancel_partial_probe()?;
                Ok(None)
            }
        }
    }
    pub(crate) fn cancel_partial_probe(&self) -> io::Result<()> {
        let mut state = self.lock()?;
        state.usable()?;
        if state.funding.is_some()
            || state.originals.len() != self.original_width
            || state.published != self.original_width
        {
            return Err(invalid(
                "cannot cancel a returned or partially funded phase",
            ));
        }
        state.parked = state.restriction.parked();
        Ok(())
    }
    /// Negative preparation only. No guard or GNU token is returned here.
    pub(crate) fn partial_ready(&self) -> io::Result<Option<CpuUnit>> {
        let state = self.lock()?;
        state.usable()?;
        if !state.parked
            || state.funding.is_some()
            || state.originals.len() != self.original_width
            || self.original_width < 2
            || state.local_cancel.is_some()
            || state.slots.iter().skip(1).any(Option::is_some)
            || state
                .originals
                .iter()
                .skip(1)
                .any(|unit| Arc::strong_count(&unit.lease) != 1)
        {
            return Ok(None);
        }
        if let Some(occupancy) = state.slots[0] {
            if !matches!(
                occupancy,
                Occupancy::Primary { member: None, .. }
                    | Occupancy::Primary {
                        member: Some(Member {
                            purpose: Purpose::Compiler,
                            ..
                        }),
                        ..
                    }
            ) {
                return Ok(None);
            }
        }
        let implicit = &state.originals[0];
        Ok(Some(CpuUnit {
            slot: implicit.lease.slot(),
            backing: implicit.backing,
        }))
    }

    /// Close only genuinely idle supplementary originals. Preparation binds
    /// the real original Host; all native guards remain held until this call.
    /// V1 startup stays full-width; only this distinct opaque V2 preparation
    /// can release originals. Fixed banks cannot construct this cooperative
    /// bank or preparation. The surviving implicit/primary0 never moves.
    pub(crate) fn withdraw_supplementary(
        self: &Arc<Self>,
        prepared: PreparedPartialPhase,
        mut escrow: ForeignGnuEscrow,
    ) -> io::Result<RootPartialPhase> {
        let (root, invocation, phase, ordinal) = prepared.binding();
        let initial = self.initial_ready()?;
        let expected = if initial.is_some() {
            initial.map(|(_, cpu)| cpu)
        } else {
            self.partial_ready()?
        };
        if root != self.root_attempt
            || invocation != self.invocation_sha256
            || escrow.ceiling() > self.original_width
            || escrow.backing() != prepared.gnu()
            || expected != Some(prepared.implicit())
            || initial.is_some_and(|(original, _)| original != phase)
        {
            return Err(invalid(
                "partial return differs from original prepared bank/GNU",
            ));
        }
        let mut state = self.lock()?;
        state.usable()?;
        // Parking already excludes new primary/extra/local dispatch. Recheck
        // borrowed descriptors under the SAME lock immediately before close.
        if state.funding.is_some()
            || !state.parked
            || state.local_cancel.is_some()
            || state.originals.len()
                != if initial.is_some() {
                    1
                } else {
                    self.original_width
                }
            || state.published != state.originals.len()
            || state.initial_phase != initial.map(|(phase, _)| phase)
            || state.slots.iter().skip(1).any(Option::is_some)
            || state
                .originals
                .iter()
                .skip(1)
                .any(|unit| Arc::strong_count(&unit.lease) != 1)
        {
            return Err(invalid(
                "partial original bank changed before descriptor return",
            ));
        }
        if let Some(occupancy) = state.slots[0] {
            if !matches!(
                occupancy,
                Occupancy::Primary { member: None, .. }
                    | Occupancy::Primary {
                        member: Some(Member {
                            purpose: Purpose::Compiler,
                            ..
                        }),
                        ..
                    }
            ) {
                return Err(invalid("implicit member changed before descriptor return"));
            }
        }
        // This must precede the first close: loss can no longer return GNU
        // tokens without genuine replacement backing/positive Host completion.
        escrow.offered();
        state.funding = Some(FundingState {
            phase,
            ordinal,
            stage: Stage::Returned,
        });
        state.initial_phase = None;
        state.originals.truncate(1);
        // This SAME original worker owner has excluded dispatch, joined all
        // supplementary loans and captured GNU before this first close.
        // Retain any implicit keeper; only retired supplementary custody goes.
        let implicit_backing = state.originals[0].backing;
        state
            .pending_keepers
            .retain(|owner| owner.observation().native == implicit_backing);
        state.published = 1;
        drop(state);
        Ok(RootPartialPhase {
            bank: self.clone(),
            prepared,
            escrow: Some(escrow),
            gnu_backed: 1,
            origin: if initial.is_some() {
                PreparationOrigin::Initial
            } else {
                PreparationOrigin::Runtime
            },
        })
    }
}
impl RootPartialPhase {
    /// Park actual bank dispatch before recapturing only previously backed
    /// GNU credits. Missing guards keep the same owner/counter and defer.
    pub(crate) fn park_current(&mut self) -> io::Result<bool> {
        self.bank.park()?;
        if !self.bank.current_drained()? {
            return Ok(false);
        }
        let state = self.bank.lock()?;
        state.usable()?;
        if state.funding.as_ref().is_none_or(|funding| {
            funding.phase != self.phase()
                || funding.ordinal != self.prepared.binding().3
                || funding.stage != Stage::Running
        }) || state.published.min(
            self.escrow
                .as_ref()
                .ok_or_else(|| invalid("current GNU owner missing"))?
                .ceiling(),
        ) != self.gnu_backed
        {
            return Err(invalid(
                "current phase differs from actual funded originals",
            ));
        }
        drop(state);
        self.escrow
            .as_mut()
            .ok_or_else(|| invalid("current GNU owner missing"))?
            .try_recapture_backed(
                self.gnu_backed
                    .checked_sub(1)
                    .ok_or_else(|| invalid("implicit funding missing"))?,
            )
    }
    pub(crate) fn current_descriptors(&self) -> io::Result<[std::os::fd::BorrowedFd<'_>; 2]> {
        Ok(self
            .escrow
            .as_ref()
            .ok_or_else(|| invalid("current GNU owner missing"))?
            .descriptors())
    }
    pub(crate) fn current_backing(&self) -> FileIdentity {
        self.prepared.gnu()
    }
    pub(crate) fn resume_current(&mut self) -> io::Result<()> {
        if !self.bank.current_drained()? {
            return Err(invalid("current loan owners have not drained"));
        }
        self.escrow
            .as_mut()
            .ok_or_else(|| invalid("current GNU owner missing"))?
            .return_backed(
                self.gnu_backed
                    .checked_sub(1)
                    .ok_or_else(|| invalid("implicit funding missing"))?,
            )?;
        let mut state = self.bank.lock()?;
        state.usable()?;
        state.parked = false;
        state.restriction = Restriction::Running;
        Ok(())
    }
    pub(crate) fn retire_current(&mut self) -> io::Result<()> {
        if !self.bank.current_drained()? {
            return Err(invalid("final current loan owners have not drained"));
        }
        self.escrow
            .take()
            .ok_or_else(|| invalid("current GNU owner missing"))?
            .retire_drained()
    }
    pub(crate) fn initial_single_installed(&self) -> io::Result<bool> {
        if self.bank.original_width != 1 {
            return Ok(false);
        }
        let mut state = self.bank.lock()?;
        state.usable()?;
        if state.originals.len() != 1
            || state.published != 1
            || state.funding.as_ref().is_none_or(|funding| {
                funding.phase != self.phase()
                    || funding.ordinal != self.prepared.binding().3
                    || funding.stage != Stage::Running
            })
        {
            return Err(invalid("initial singleton lacks actual original funding"));
        }
        state.parked = true;
        state
            .funding
            .as_mut()
            .ok_or_else(|| invalid("initial funding disappeared"))?
            .stage = Stage::Installed;
        Ok(true)
    }
    pub(crate) fn phase(&self) -> Attempt {
        self.prepared.binding().2
    }
    /// Only after positive original Host release. The genuine implicit unit
    /// never left; it may continue without restoring ANY supplementary token.
    pub(crate) fn run_implicit(&self) -> io::Result<()> {
        let mut state = self.bank.lock()?;
        state.usable()?;
        if state.originals.len() != 1
            || state.published != 1
            || state.funding.as_ref().is_none_or(|funding| {
                funding.phase != self.phase()
                    || funding.ordinal != self.prepared.binding().3
                    || funding.stage != Stage::Returned
            })
        {
            return Err(invalid(
                "implicit continuation differs from original returned phase",
            ));
        }
        state.funding = Some(FundingState {
            phase: self.phase(),
            ordinal: self.prepared.binding().3,
            stage: Stage::Running,
        });
        if matches!(self.origin, PreparationOrigin::Initial)
            && matches!(state.restriction, Restriction::InitialOutput)
        {
            state.restriction = Restriction::Running;
        }
        state.parked = state.restriction.parked();
        Ok(())
    }

    /// Consume genuine same-channel adopted guards. A count, echoed CPU set or
    /// decoded reply cannot supply this nonconstructible input owner.
    pub(crate) fn install(
        &mut self,
        originals: trust_build_cpu::PartialNativeOriginals,
    ) -> io::Result<()> {
        if originals.binding() != self.prepared.binding() {
            return Err(invalid(
                "partial replacements belong to another original phase",
            ));
        }
        let funded_before = originals.funded_before();
        let leases = originals.into_leases();
        if leases.is_empty()
            || funded_before
                .checked_add(leases.len())
                .is_none_or(|total| total > self.bank.original_width)
        {
            return Err(invalid(
                "partial replacement width differs from actual original bank",
            ));
        }
        let mut replacement = Vec::new();
        replacement
            .try_reserve_exact(leases.len())
            .map_err(io::Error::other)?;
        let implicit = self.prepared.implicit();
        for lease in leases {
            let meta = std::fs::File::from(lease.as_fd().try_clone_to_owned()?).metadata()?;
            let backing = FileIdentity {
                device: meta.dev(),
                inode: meta.ino(),
            };
            if !meta.is_file()
                || meta.nlink() != 1
                || lease.slot() == implicit.slot
                || backing == implicit.backing
                || replacement.iter().any(|other: &Original| {
                    other.lease.slot() == lease.slot() || other.backing == backing
                })
            {
                return Err(invalid(
                    "partial replacement aliases another actual original",
                ));
            }
            replacement.push(Original {
                lease: Arc::new(lease),
                backing,
            });
        }
        let mut state = self.bank.lock()?;
        state.usable()?;
        if state.originals.len() != funded_before
            || state.published != funded_before
            || state.funding.as_ref().is_none_or(|funding| {
                funding.phase != self.phase()
                    || funding.ordinal != self.prepared.binding().3
                    || !matches!(funding.stage, Stage::Returned | Stage::Running)
            })
        {
            return Err(invalid("partial replacement has no original parked owner"));
        }
        if replacement.iter().any(|new| {
            state
                .originals
                .iter()
                .any(|old| new.lease.slot() == old.lease.slot() || new.backing == old.backing)
        }) {
            return Err(invalid(
                "partial replacement aliases a previously installed original",
            ));
        }
        state
            .originals
            .try_reserve_exact(replacement.len())
            .map_err(io::Error::other)?;
        state.originals.extend(replacement);
        state.funding = Some(FundingState {
            phase: self.phase(),
            ordinal: self.prepared.binding().3,
            stage: Stage::Installed,
        });
        Ok(())
    }

    /// Positive completion must come from the SAME retained original control.
    /// Actual replacement guards are installed BEFORE dispatch or GNU restore.
    pub(crate) fn publish(&mut self, committed: CommittedPartialPhase) -> io::Result<bool> {
        if !committed.matches_original(&self.prepared) {
            return Err(invalid(
                "partial completion differs from original Host owner",
            ));
        }
        let mut state = self.bank.lock()?;
        state.usable()?;
        if state.originals.len() != committed.funded_width()
            || state.originals.len() > self.bank.original_width
            || state.funding.as_ref().is_none_or(|funding| {
                funding.phase != self.phase()
                    || funding.ordinal != self.prepared.binding().3
                    || funding.stage != Stage::Installed
            })
        {
            return Err(invalid(
                "partial resume lacks actual original replacement backing",
            ));
        }
        let actual_funded = state.originals.len();
        actual_funded
            .checked_sub(state.published)
            .ok_or_else(|| invalid("partial actual funding regressed before publication"))?;
        let complete = state.originals.len() == self.bank.original_width;
        state.published = state.originals.len();
        if complete {
            state.funding.take();
        } else {
            state.funding = Some(FundingState {
                phase: self.phase(),
                ordinal: self.prepared.binding().3,
                stage: Stage::Running,
            });
        }
        state.parked = state.restriction.parked();
        drop(state);
        let escrow = self
            .escrow
            .as_mut()
            .ok_or_else(|| invalid("same original GNU escrow missing"))?;
        let gnu_funded = actual_funded.min(escrow.ceiling());
        let newly_backed = gnu_funded
            .checked_sub(self.gnu_backed)
            .ok_or_else(|| invalid("original GNU funded balance regressed"))?;
        escrow.return_backed(newly_backed)?;
        self.gnu_backed = gnu_funded;
        if complete {
            self.escrow
                .take()
                .ok_or_else(|| invalid("same original GNU escrow missing"))?
                .settled();
        }
        Ok(complete)
    }
}

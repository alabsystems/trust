//! Trust (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.7): THE
//! `clean_origin_mir` REACH COUNTER — who in this compilation read a Clean-origin def's
//! `clean_origin_mir` body, by lane.
//!
//! # Why it exists
//!
//! Step 3's exit says `clean_origin_mir` is no longer on F1's production path: F1's codegen, its
//! inventory and the Clean recorder never call it, while the readers that leave later (the
//! verifier's callee model at item V, CTFE at step 9, cross-crate metadata at increment 6) still
//! do. "Never calls it" is a property of every compile, not of a code review, so each compile
//! counts, and F1 prints the count in its report. The step-3 exit requires `codegen`, `inventory`
//! and `recorder` to be zero.
//!
//! # What a count is, precisely
//!
//! A lane is charged in one of two ways, and never both for one read:
//!
//! * an ASK ([`ask`]): a Trust-owned site that demands a Clean-origin def's MIR on purpose (the
//!   recorder's re-earn and its eager demands; the F1 inventory falling back to the MIR walk)
//!   charges its lane once per demand, whether the query system runs the hook or answers from
//!   its cache. A site that asks is counted even when an earlier reader built the body, which is
//!   what makes a zero meaningful: a verify-on compile builds the body for the verifier first, and
//!   a recorder that still asked would otherwise look free;
//! * a BUILD ([`hook_ran`]): every run of the hook itself (the `optimized_mir` and `mir_for_ctfe`
//!   providers building a Clean-origin body) that no ask is in flight for is charged to the lane
//!   whose scope is open ([`within`]: F1 codegen, verification, metadata encoding), to `ctfe` when
//!   the hook serves `mir_for_ctfe`, and to `unattributed` when no scope is open. A demand that
//!   the cache answers inside a scope is NOT counted: a lane's build count is a lower bound, and
//!   only the ask lanes are complete.
//!
//! The scope is thread-local. A demand on another thread (a parallel front end) sees no scope and
//! is charged to `unattributed`, never to a lane it did not come from.
//!
//! # What it never is
//!
//! A gate or an authority: nothing reads it to decide anything. It is disclosure, printed by F1
//! and asserted by the tests that pin the step-3 exit (`tests/run-make/trust-cg-f1-clean-recorder`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::Cell;

/// The reader a `clean_origin_mir` read is charged to (design §5.7's lanes, plus the
/// metadata encoder and `unattributed`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReachLane {
    /// F1's own codegen (`rustc_codegen_trust_cg`'s trust-ir frontend lanes). Must be zero.
    Codegen,
    /// F1's work list: the mono-item collector walking a Clean-origin item's MIR because no
    /// published row could answer its neighbours (`clean_inventory::neighbours`). Must be zero.
    Inventory,
    /// The Clean recorder (`rustc_mir_transform::clean_origin_ir`) and the analysis-seam eager
    /// demands the design lists beside it (`rustc_interface::passes`). Must be zero on F1.
    Recorder,
    /// TrustVerify's callee model (leaves at item V, plan step 5).
    Verification,
    /// Const evaluation (`mir_for_ctfe`; leaves at plan step 9).
    Ctfe,
    /// The metadata encoder carrying a Clean-origin body cross-crate (I7; leaves at increment 6).
    CrossCrate,
}

/// One compilation's reads, by lane. Session state ([`record`], [`snapshot`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CleanOriginMirReached {
    pub codegen: u64,
    pub inventory: u64,
    pub recorder: u64,
    pub verification: u64,
    pub ctfe: u64,
    pub cross_crate: u64,
    /// A build of the hook with no scope open and no ask in flight.
    pub unattributed: u64,
}

impl CleanOriginMirReached {
    fn charge(&mut self, lane: Option<ReachLane>) {
        let slot = match lane {
            Some(ReachLane::Codegen) => &mut self.codegen,
            Some(ReachLane::Inventory) => &mut self.inventory,
            Some(ReachLane::Recorder) => &mut self.recorder,
            Some(ReachLane::Verification) => &mut self.verification,
            Some(ReachLane::Ctfe) => &mut self.ctfe,
            Some(ReachLane::CrossCrate) => &mut self.cross_crate,
            None => &mut self.unattributed,
        };
        *slot = slot.saturating_add(1);
    }

    /// The step-3 exit's three lanes are all zero (design §5.7).
    pub fn f1_path_is_free(&self) -> bool {
        self.codegen == 0 && self.inventory == 0 && self.recorder == 0
    }

    /// The one-line rendering F1 prints. Stable: tests read it.
    pub fn render(&self) -> String {
        format!(
            "`clean_origin_mir` reached: codegen {}, inventory {}, recorder {} (plan step 3: \
             these three are F1's path and must be 0); verification {}, ctfe {}, cross-crate {}, \
             unattributed {} (the readers that leave later: item V, step 9, increment 6)",
            self.codegen,
            self.inventory,
            self.recorder,
            self.verification,
            self.ctfe,
            self.cross_crate,
            self.unattributed
        )
    }
}

/// What is open on this thread: the lane, and whether it was charged already (an ask).
#[derive(Clone, Copy)]
struct Open {
    lane: ReachLane,
    asked: bool,
}

thread_local! {
    static OPEN: Cell<Option<Open>> = const { Cell::new(None) };
}

/// Restores the previous scope when dropped, however the scope is left.
#[must_use = "the scope closes when the guard is dropped"]
pub struct ReachScope {
    previous: Option<Open>,
}

impl Drop for ReachScope {
    fn drop(&mut self) {
        OPEN.with(|open| open.set(self.previous));
    }
}

fn open(lane: ReachLane, asked: bool) -> ReachScope {
    let previous = OPEN.with(|open| open.replace(Some(Open { lane, asked })));
    ReachScope { previous }
}

/// Session state behind [`record`] and [`snapshot`].
#[derive(Default)]
struct SessionReach(CleanOriginMirReached);

fn record(sess: &rustc_session::Session, lane: Option<ReachLane>) {
    sess.with_trust_compiler_state::<SessionReach, _>(|reach| reach.0.charge(lane));
}

/// An ASK: charge `lane` once now, and open its scope so the hook build this demand may cause is
/// not charged a second time. Hold the guard across the demand.
pub fn ask(sess: &rustc_session::Session, lane: ReachLane) -> ReachScope {
    record(sess, Some(lane));
    open(lane, true)
}

/// Open `lane`'s scope without charging it: a build of the hook while the guard lives is charged
/// to `lane` ([`hook_ran`]).
pub fn within(lane: ReachLane) -> ReachScope {
    open(lane, false)
}

/// Called by the hook on every build of a Clean-origin body (`ctfe`: it serves `mir_for_ctfe`).
pub fn hook_ran(sess: &rustc_session::Session, ctfe: bool) {
    if ctfe {
        record(sess, Some(ReachLane::Ctfe));
        return;
    }
    match OPEN.with(Cell::get) {
        Some(Open { asked: true, .. }) => {}
        Some(Open { lane, asked: false }) => record(sess, Some(lane)),
        None => record(sess, None),
    }
}

/// This compilation's reads so far.
pub fn snapshot(sess: &rustc_session::Session) -> CleanOriginMirReached {
    sess.with_trust_compiler_state::<SessionReach, _>(|reach| reach.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn charged(f: impl FnOnce(&mut CleanOriginMirReached)) -> CleanOriginMirReached {
        let mut reach = CleanOriginMirReached::default();
        f(&mut reach);
        reach
    }

    #[test]
    fn each_lane_has_its_own_slot_and_no_scope_is_unattributed() {
        let lanes = [
            ReachLane::Codegen,
            ReachLane::Inventory,
            ReachLane::Recorder,
            ReachLane::Verification,
            ReachLane::Ctfe,
            ReachLane::CrossCrate,
        ];
        let reach = charged(|r| {
            for (n, lane) in lanes.iter().enumerate() {
                for _ in 0..=n {
                    r.charge(Some(*lane));
                }
            }
            r.charge(None);
        });
        assert_eq!(
            reach,
            CleanOriginMirReached {
                codegen: 1,
                inventory: 2,
                recorder: 3,
                verification: 4,
                ctfe: 5,
                cross_crate: 6,
                unattributed: 1,
            }
        );
        assert!(!reach.f1_path_is_free());
        assert!(
            charged(|r| {
                r.charge(Some(ReachLane::Verification));
                r.charge(Some(ReachLane::Ctfe));
                r.charge(Some(ReachLane::CrossCrate));
                r.charge(None);
            })
            .f1_path_is_free()
        );
        for lane in [ReachLane::Codegen, ReachLane::Inventory, ReachLane::Recorder] {
            assert!(!charged(|r| r.charge(Some(lane))).f1_path_is_free(), "{lane:?}");
        }
    }

    #[test]
    fn scopes_nest_and_restore_the_outer_one_when_dropped() {
        assert!(OPEN.with(Cell::get).is_none());
        {
            let _codegen = within(ReachLane::Codegen);
            {
                let _verification = within(ReachLane::Verification);
                assert!(matches!(
                    OPEN.with(Cell::get),
                    Some(Open { lane: ReachLane::Verification, asked: false })
                ));
            }
            assert!(matches!(
                OPEN.with(Cell::get),
                Some(Open { lane: ReachLane::Codegen, asked: false })
            ));
            {
                let _ask = open(ReachLane::Inventory, true);
                assert!(matches!(
                    OPEN.with(Cell::get),
                    Some(Open { lane: ReachLane::Inventory, asked: true })
                ));
            }
        }
        assert!(OPEN.with(Cell::get).is_none());
    }

    #[test]
    fn the_rendering_names_every_lane_and_the_three_that_must_be_zero() {
        let text =
            CleanOriginMirReached { recorder: 2, cross_crate: 1, ..Default::default() }.render();
        assert!(text.starts_with("`clean_origin_mir` reached: codegen 0, inventory 0, recorder 2"));
        for field in ["verification 0", "ctfe 0", "cross-crate 1", "unattributed 0"] {
            assert!(text.contains(field), "{field}: {text}");
        }
    }
}

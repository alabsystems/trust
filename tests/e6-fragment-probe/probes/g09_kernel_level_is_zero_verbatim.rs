//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: CENSUS PROBE, not an isolation probe -- `&self` receiver, match on a user
//@ probe-note: enum, Arc edges and self-recursion all at once. Isolations are
//@ probe-note: g05/g06/g07.
//@ probe-note: This is clean-kernel `Level::is_zero` VERBATIM
//@ probe-note: (crates/clean-kernel/src/level/mod.rs:544-551). It is the DESIGNATED
//@ probe-note: crystal target -- the body whose five-link chain closed link 4 on
//@ probe-note: 2026-08-26. If the fused route cannot state a clause about this body, it
//@ probe-note: cannot be compared against the crystal route on the crystal's own target.
//@ probe-note: First measured `unproved` at c4e667ca51; current 4c8a1e19da reports
//@ probe-note: `ClauseOutsideFragment`. Both refuse before defeq; the current explicit
//@ probe-note: classification is the fail-closed verdict pinned by this header.
clean { def tt_isl : Bool := true }
use std::sync::Arc;
pub enum Level { Zero, Succ(Arc<Level>), Param(u64), Max(Arc<Level>, Arc<Level>), IMax(Arc<Level>, Arc<Level>) }
impl Level {
    pub fn is_zero(&self) -> bool
        ensures result == tt_isl
    {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }
}

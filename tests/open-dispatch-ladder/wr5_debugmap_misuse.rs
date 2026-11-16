//@ trust-ladder: refuses
//@ trust-ladder-row: <dyn core::fmt::Debug as core::fmt::Debug>::fmt
//! D1 increment 1 (2026-09-25) RAIL, the G-MEMBER case (F2). `DebugMap::key`
//! twice panics in core's own `assert!`, which mints no row (docs/TCB.md "A
//! bundled member's `Assert` mints NO obligation"). Must stay refused. Measured
//! BEFORE on the stage-1 snapshot `4e9fe36bf`: refuses, needle present.
use core::fmt;
pub struct M;
impl fmt::Debug for M {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.debug_map().key(&1u32).key(&2u32).finish() }
}

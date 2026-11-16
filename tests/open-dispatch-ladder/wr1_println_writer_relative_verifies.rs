//@ trust-ladder: verifies
//@ trust-ladder-row: panic-free relative to its
//@ trust-ladder-crate-type: bin
//! D1 increment 1 (2026-09-25): the program `pf5` used to carry, recorded as the
//! deliberate flip it now is. `Good` passes the absolute bar; `Bad` touches only
//! its own `Formatter`'s writer, so it is panic-free RELATIVE TO that writer — a
//! CONDITIONAL verdict — and `println!` is a std sink that supplies the writer.
//! Measured BEFORE on the stage-1 snapshot `4e9fe36bf`: refuses ("formatted
//! through a user"). The needle is the writer-relative disclosure on `Bad`'s
//! advisory, so a green for any other reason diverges.
use core::fmt;
pub struct Good;
impl fmt::Debug for Good { fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) } }
pub struct Bad(pub u32);
impl fmt::Debug for Bad {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("Bad") }
}
fn main() { println!("{:?} {:?}", Good, Bad(1)); }

//@ trust-ladder: refuses
//@ trust-ladder-row: error transparency
//@ trust-ladder-crate-type: bin
//! D1 increment 1 (2026-09-25) RAIL. `E` is writer-relative but returns `Err`
//! after a successful write, so it is NOT error-transparent, and `println!` of it
//! panics in std ("a formatting trait implementation returned an error when the
//! underlying stream did not"). Must stay refused on error transparency.
//! Measured BEFORE on the stage-1 snapshot `4e9fe36bf`: refuses.
use core::fmt;
pub struct E;
impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("e")?; Err(fmt::Error) }
}
fn main() { println!("{}", E); }

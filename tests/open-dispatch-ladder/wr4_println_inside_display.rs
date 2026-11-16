//@ trust-ladder: refuses
//@ trust-ladder-row: formatted through a user
//@ trust-ladder-crate-type: bin
//! D1 increment 1 (2026-09-25) RAIL. A `println!` inside `Display::fmt` is a
//! non-writer `_print` call (it does not crash — stdout's lock is reentrant —
//! but its panic path is std's, not the writer's). The
//! writer-relative bar excuses ONLY writer edges (zero vanilla rows), so the
//! impl's `_print` row keeps it unvouched and `main` stays refused. Measured
//! BEFORE on the stage-1 snapshot `4e9fe36bf`: refuses.
use core::fmt;
pub struct P;
impl fmt::Display for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { println!("inner"); f.write_str("p") }
}
fn main() { println!("{}", P); }

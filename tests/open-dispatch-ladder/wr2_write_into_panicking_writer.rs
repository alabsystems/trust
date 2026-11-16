//@ trust-ladder: refuses
//@ trust-ladder-row: panic-free only relative to its
//@ trust-ladder-crate-type: bin
//! D1 increment 1 (2026-09-25) RAIL. `S` is writer-relative (conditional), and
//! `write!(Boom, "{:?}", S)` hands it a LOCAL writer that panics: not a std sink,
//! so the writer premise is not discharged and `main` must stay refused. The
//! needle is the note naming exactly that. (`Boom::write_str` is refused on its
//! own panic too; the needle pins `main`'s reason.) Measured BEFORE on the
//! stage-1 snapshot `4e9fe36bf`: refuses.
use core::fmt::{self, Write};
pub struct S;
impl fmt::Debug for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("S") }
}
pub struct Boom(pub u32);
impl Write for Boom {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.len() == 1 { panic!("boom writer") }
        self.0 = self.0.wrapping_add(1);
        Ok(())
    }
}
fn main() { let mut b = Boom(0); let _ = write!(b, "{:?}", S); }

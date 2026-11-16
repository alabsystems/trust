//@ trust-ladder: refuses
//@ trust-ladder-row: formatted through a user
//@ trust-ladder-crate-type: bin
//! D1 increment 2 (2026-09-25) RAIL. `Inner` writes and then returns `Err`:
//! writer-relative, NOT error-transparent. The derived `Outer` is itself
//! writer-relative (a conditional pass), but `println!` of it panics in std —
//! error transparency (version 2) recurses into the local nested target and
//! refuses `main`. Runtime truth (verification off): exit 101, "a formatting
//! trait implementation returned an error when the underlying stream did not".
//! Measured BEFORE on the stage-1 snapshot `43b8fe6ab`: refuses, needle present.
use core::fmt;
pub struct Inner;
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("i")?; Err(fmt::Error) }
}
#[derive(Debug)]
pub struct Outer(pub Inner);
fn main() { println!("{:?}", Outer(Inner)); }

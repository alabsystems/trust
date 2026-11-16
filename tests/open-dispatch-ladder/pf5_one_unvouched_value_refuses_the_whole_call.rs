//@ trust-ladder: refuses
//@ trust-ladder-row: formatted through a user
//@ trust-ladder-crate-type: bin
//! GUARD RAIL for the shape of the fix. `println!` packs one `Argument` per
//! formatted value, so the caller-side gate must require EVERY packer's type to
//! be vouched, not any. `Good`'s impl is established panic-free; `Bad`'s touches
//! its `Formatter` and is not. `main` must stay refused on `Bad` alone.
//! If this row ever goes green, the loop became an `any` where it must be an
//! `all`, and a panicking `Debug` rides in beside a provable one.
//!
//! EDITED 2026-09-25 (D1 increment 1). `Bad` used to be `f.write_str("Bad")`
//! alone. Increment 1 vouches for exactly that impl at a std sink (panic-free
//! RELATIVE TO its writer, which `println!` supplies), so the old program now
//! verifies by design — that flip is recorded as
//! `wr1_println_writer_relative_verifies.rs`. To keep THIS row testing
//! all-versus-any, `Bad` now also panics on one input, so it is unvouched on
//! every bar: absolute (it can panic) and writer-relative (a diverging call in
//! the body refuses the class). Measured BEFORE on the stage-1 snapshot
//! `4e9fe36bf`: refuses, needle present.
use core::fmt;
pub struct Good;
impl fmt::Debug for Good { fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) } }
pub struct Bad(pub u32);
impl fmt::Debug for Bad {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 7 { panic!("seven") }
        f.write_str("Bad")
    }
}
fn main() { println!("{:?} {:?}", Good, Bad(1)); }

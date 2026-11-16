//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! THIS ROW CORRECTS THE HEADLINE. `p4` in the realistic corpus — a `dyn Shape`
//! sum — was filed as blocked on the SAME ruling as `#[derive(Debug)]`. It is
//! not. Its trait is LOCAL, so with `#[trust::panic_free]` on the trait method
//! and a whole-program artifact, the `dyn` dispatch DISCHARGES and the function
//! verifies. Measured: this file is rc=0.
//!
//! So "open dispatch" is two populations, not one:
//!   * a USER trait — dischargeable TODAY, with one attribute, no ruling needed;
//!   * `core::fmt`'s traits (`derive(Debug)`) — blocked by the `is_local()`
//!     locality gate, which is the ruling.
//!
//! p4's actual residual, once Phi is applied, is `main`'s `vec![]` lowering
//! ("native typed-TrustIr lowering did not complete") — a different item
//! entirely. Swapping the `vec![]` for an array, as here, removes it.
#![feature(register_tool)]
#![register_tool(trust)]
pub trait Shape { #[trust::panic_free] fn area(&self) -> u64; }
pub struct Rect { pub w: u32, pub h: u32 }
impl Shape for Rect { fn area(&self) -> u64 { self.w as u64 * self.h as u64 } }
pub fn total(shapes: &[&dyn Shape]) -> u64 {
    let mut t = 0u64;
    for s in shapes { t = t.saturating_add(s.area()); }
    t
}
fn main() { let r = Rect { w: 2, h: 3 }; let a: [&dyn Shape; 1] = [&r]; let _ = total(&a); }

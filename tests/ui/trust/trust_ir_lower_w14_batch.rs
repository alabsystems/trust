//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-14 batch): four residue lanes in one landing.
//! * TR3/R1 — the wave-DB double-borrow slot's content is statically known
//!   (one Store of a ledgered pointer, immutable slot), so `*slot` FORWARDS
//!   that pointer — which lets derive(Debug)'s `&&self.last_field -> &dyn
//!   Debug` unsize chain flow.
//! * TL — a thread-local address is a fresh symbolic pointer per occurrence
//!   (the oracle's ratified no-TLS-identity model), body SYMBOLIC.
//! * AW/W1 — `a.b = v` on an UNPROMOTED SSA struct local: InsertField value
//!   surgery with the chain arm's leaf postures.
//! * R2 — `Ty::Array` joins the Deref pointee list (Load/Store parity).

use std::cell::Cell;

#[derive(Debug)]
struct Two {
    a: u32,
    b: u16,
}

thread_local! {
    static COUNTER: Cell<u32> = Cell::new(0);
}

struct P {
    x: u64,
    y: u64,
}

fn assign_ssa_local(v: u64) -> u64 {
    let mut p = P { x: 1, y: 2 };
    p.x = v; // never borrowed: stays SSA, InsertField surgery
    p.x + p.y
}

fn array_through_ref(r: &[u8; 4]) -> u8 {
    let a = *r; // R2: array pointee Load
    a[0]
}

fn main() {
    let t = Two { a: 7, b: 9 };
    assert_eq!(format!("{t:?}"), "Two { a: 7, b: 9 }");
    COUNTER.with(|c| c.set(c.get() + 1));
    assert_eq!(assign_ssa_local(40), 42);
    assert_eq!(array_through_ref(&[5, 6, 7, 8]), 5);
}

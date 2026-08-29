//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-NB): borrows and writes of a SINGLE-LEVEL scalar field of a
//! struct LOCAL lower through a whole-lifetime aggregate slot.
//!
//! Before this wave a struct local lived only as an SSA value, so `&a.b`,
//! `&mut a.b`, and `a.b = v` all failed closed (`Borrow(non-local place)` /
//! `Borrow(&mut non-local place)` / `Assign(non-local place)`) — there was no
//! address to derive a field pointer from. The pre-pass now collects the base
//! local of every field borrow/assign into `promoted`; the `let`/param
//! admission allocates a real `Alloca` slot for pure-value aggregates (the
//! `snapshotable_aggregate_pointee` set — registered all-scalar structs,
//! tuples of scalars, first-class enums); and the field address is a flat-I8
//! `GEP` off that slot, gated per access on the wave-SG layout-agreement
//! predicate. One shared emission site (`lower_field_of_local_addr`) serves
//! the shared-Borrow, mut-Borrow, and Assign arms so no gate can drift.
//!
//! Coherence is by construction: a promoted local is never `set_local`'d, so
//! every read (`s.a` after `s.b = 9`, the whole `s` after a write through
//! `&mut s.b`) is a fresh `Load` from the same slot the `Store` hit.

struct P {
    a: u64,
    b: u64,
}

// `&s.f` — shared field borrow, read back through the reference.
fn shared_field(x: u64) -> u64 {
    let s = P { a: x, b: 7 };
    let r = &s.a;
    *r + s.b
}

// `&mut s.f` — mut field borrow, write through it, observe via a direct read.
fn mut_field(x: u64) -> u64 {
    let mut s = P { a: 1, b: x };
    let r = &mut s.a;
    *r = 40;
    s.a + s.b
}

// `s.f = v` — direct field write, no borrow anywhere.
fn field_write(x: u64) -> u64 {
    let mut s = P { a: 0, b: 3 };
    s.a = x;
    s.a * s.b
}

fn main() {
    assert_eq!(shared_field(5), 12);
    assert_eq!(mut_field(2), 42);
    assert_eq!(field_write(7), 21);
}

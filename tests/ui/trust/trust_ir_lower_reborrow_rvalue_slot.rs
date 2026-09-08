//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-RWR): the reborrow-wrapped mutable rvalue temp slot.
//!
//! THIR wraps a `&mut <rvalue>` call argument as
//! `Borrow{Mut, Deref{Borrow{Mut, <rvalue>}}}`, and the shipped temp-slot lane
//! peels only `Scope`/`Use` — so it was handed the un-peeled operand, saw an
//! `ExprKind::Deref`, and declined every rvalue it exists to serve.
//!
//! This collapses the wrapper and DELEGATES; it adds no admission of its own.
//! It is inert on un-wrapped shapes by construction (the `Deref` is required,
//! and the delegate already ran on operands lacking one), and the inner
//! `BorrowKind::Mut` is CHECKED rather than assumed, because this runs inside
//! `mir_built` before borrowck — that conjunct is what keeps a shared-only
//! inner from being laundered into a write channel.

fn bump(v: &mut [u8; 4]) {
    v[0] = v[0].wrapping_add(1);
}

fn take(x: &mut u8) -> u8 {
    *x += 3;
    *x
}

pub fn reborrowed_array_rvalue() -> u8 {
    let mut n = 0u8;
    bump(&mut [1, 2, 3, 4]);
    n += 1;
    n
}

pub fn reborrowed_literal_rvalue() -> u8 {
    take(&mut 4)
}

fn main() {
    assert_eq!(reborrowed_array_rvalue(), 1);
    assert_eq!(reborrowed_literal_rvalue(), 7);
}

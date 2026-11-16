//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aunused_assignments
//! Trust (wave-UAS): `let mut z: () = ...; z = x = 11;` — a UNIT local assigned
//! the value of a nested assignment.
//!
//! `()` is not a value in this IR, so the nested `x = 11` correctly emits its
//! store and returns `None` WITHOUT a tag; there is then nothing to rebind and
//! nothing lost. The `let` sibling already does exactly this (`if let Some(v) =
//! lower_expr(init)`, no else, no tag), as do `try_lower_unit_arg` and the
//! wave-UF tuple-element arm at their own positions. A unit local is a
//! SINGLETON: any read of it can only observe `()`.
//!
//! Two gates are load-bearing. The RHS shape allow-list admits exactly the
//! literal `()`, an `Assign` and an `AssignOp` — a unit-returning CALL also
//! returns `None` with no tag, so without it this arm would silently swallow
//! one; `call_rhs_declines` fences that. And the local must be UNBOUND: a `()`
//! PARAMETER is bound by the param loop, and `param_lhs_declines` fences that.
//!
//! `run-pass` checks the nested stores by VALUE — the whole point is that the
//! effects still happen.

pub fn test_assign() -> i32 {
    let mut x = 0;
    let mut z: () = ();
    z = x = 11;
    let _ = z;
    x
}

pub fn test_assign_op() -> i32 {
    let mut x = 1;
    let mut z: () = ();
    z = x += 4;
    let _ = z;
    x
}

fn noop() {}

/// The fence: a unit-returning CALL must NOT be swallowed.
pub fn call_rhs_declines() -> i32 {
    let mut x = 5;
    let mut z: () = ();
    z = noop();
    let _ = z;
    x += 1;
    x
}

/// The fence: a `()` PARAMETER is already bound, so the lane must decline.
pub fn param_lhs_declines(mut z: (), x: &mut i32) -> i32 {
    z = *x = 7;
    let _ = z;
    *x
}

fn main() {
    assert_eq!(test_assign(), 11);
    assert_eq!(test_assign_op(), 5);
    assert_eq!(call_rhs_declines(), 6);
    let mut n = 0;
    assert_eq!(param_lhs_declines((), &mut n), 7);
    assert_eq!(n, 7);
}

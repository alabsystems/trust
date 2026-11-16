//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aunused_assignments
//! Trust (wave-PCW): compound assignment to a precisely-captured projected
//! place inside a closure.
//!
//! `rmw_through_precise_capture` is the corpus shape: `t.0.0 += v` where
//! `t.0: &mut (i32, i32)`. RFC 2229 capture analysis captures EXACTLY the leaf
//! place by `&mut`, so the closure env holds a `&mut i32` and the intermediate
//! tuple never exists inside the body. The field-RMW arms used to refuse it as
//! `AssignOp((*p).field non-struct pointee)` — the tag names a shape the env
//! does not even carry.
//!
//! `run-pass` is the point: the RMW goes through real execution, so a lane that
//! extracted the WRONG env field, skipped the `Load`, or stored through a stale
//! pointer fails here as a wrong VALUE, not as a changed count.
//!
//! The refusal cases pin the fence:
//!   * `ancestor_capture_declines` uses the aggregate elsewhere in the closure,
//!     so the capture TRUNCATES to the whole `&mut (i32, i32)` — no capture
//!     spells the leaf place, the equality gate fails, and the body keeps its
//!     old tag (the lane must never invent the intermediate aggregate);
//!   * `by_value_env_declines` is a `move` FnOnce closure consuming the pair —
//!     P4 (`&mut {closure}` env) refuses it.
//! Both still COMPUTE correctly (they take the shipped refusal paths); their
//! assertions hold whatever the producer reports.

/// The corpus shape: precise capture of `t.0.0` by `&mut` through the ref in
/// slot 0. The env is `(&mut i32,)`; the `+=` is Load/add/Store through it.
pub fn rmw_through_precise_capture(p: &mut (i32, i32)) -> i32 {
    let t1: (&mut (i32, i32), i32) = (p, 3);
    let mut c = || {
        t1.0.0 += 10;
    };
    c();
    t1.0.0 + t1.1
}

/// The fence: the closure also reads the WHOLE pair, so capture analysis
/// truncates to `t1.0` and no capture equals the leaf spelling. The lane must
/// decline (fail the P6 equality) and leave the old refusal untouched.
pub fn ancestor_capture_declines(p: &mut (i32, i32)) -> i32 {
    let t1: (&mut (i32, i32), i32) = (p, 3);
    let mut c = || {
        t1.0.0 += 10;
        t1.0.1 += 1;
    };
    c();
    t1.0.0 + t1.0.1
}

/// The fence: a by-value FnOnce env — P4 refuses before any capture question.
pub fn by_value_env_declines(a: (i32, i32)) -> i32 {
    let mut t = a;
    let c = move || {
        let mut u = t;
        u.0 += 10;
        u.0 + u.1
    };
    t.1 = 0;
    c()
}

fn main() {
    let mut pair = (1, 2);
    assert_eq!(rmw_through_precise_capture(&mut pair), 14);
    assert_eq!(pair.0, 11);
    let mut pair2 = (5, 6);
    assert_eq!(ancestor_capture_declines(&mut pair2), 22);
    assert_eq!(by_value_env_declines((1, 2)), 13);
}

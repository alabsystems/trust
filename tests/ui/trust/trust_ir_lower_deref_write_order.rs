//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-DRW): the `*r = v` deref-write arm evaluates the RHS FIRST, and
//! a `&mut Scalar` field of the registered `&mut self` receiver is a writable
//! channel (the adjudicated Drop::drop idiom).
//!
//! `rhs_reassigns_ptr` is the WITNESS of a live wrong-value bug this wave
//! fixes: rustc builds `Assign` right-to-left (RHS before the LHS place), but
//! the arm lowered the POINTER first, so the producer stored through the STALE
//! pointer while the real program stores through the reassigned one — measured
//! `clean=true` with `mode=MirOracle, equal=false` on this shape's minimal
//! probe. `run-pass` checks the values against real execution.

/// The witness: the RHS block reassigns the pointer the LHS derefs.
pub fn rhs_reassigns_ptr() -> (i32, i32) {
    let mut a = 1;
    let mut b = 2;
    let mut p: &mut i32 = &mut a;
    *p = {
        p = &mut b;
        9
    };
    (a, b)
}

/// The adjudication shape: `*self.N = <scalar>` in Drop, through a `&mut bool`
/// field of the `&mut self` receiver.
pub struct Flag<'a>(pub &'a mut bool);
impl<'a> Drop for Flag<'a> {
    fn drop(&mut self) {
        *self.0 = false;
    }
}

/// The order pin for the adjudicated shape: the inner store precedes the outer.
pub struct Two<'a>(pub &'a mut u32, pub &'a mut u32);
impl<'a> Drop for Two<'a> {
    fn drop(&mut self) {
        *self.0 = {
            *self.1 = 9;
            5
        };
    }
}

fn main() {
    assert_eq!(rhs_reassigns_ptr(), (1, 9));
    let mut f = true;
    {
        let _g = Flag(&mut f);
    }
    assert!(!f);
    let (mut x, mut y) = (0u32, 0u32);
    {
        let _t = Two(&mut x, &mut y);
    }
    assert_eq!((x, y), (5, 9));
}

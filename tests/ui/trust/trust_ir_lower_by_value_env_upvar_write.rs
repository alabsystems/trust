//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-UVW): the by-VALUE-env sibling of wave-CX's upvar write.
//!
//! `|| *x += 1` where the closure is `FnOnce` takes its env BY VALUE
//! (`ty::Closure`, not `&mut {closure}`), while the capture is still
//! by-ref-mut. The READ arm already forked on that; the WRITE helper never did,
//! so the identical source text was clean under `FnMut` and dirty under
//! `FnOnce`.
//!
//! The by-value variant carries no env-tuple lanes at all, which makes the
//! env write-back branch — the one that would emit a wrong value here —
//! unrepresentable rather than merely unreached: the store goes straight
//! through the captured `&mut Scalar`, and a by-VALUE capture is refused.

fn call_fn_once<F: FnOnce()>(f: F) {
    f()
}

fn call_fn_mut<F: FnMut()>(mut f: F) {
    f()
}

/// The subject: the closure's kind is inferred FnOnce from the callee bound, so
/// its env param is the closure BY VALUE while the capture is still by-ref-mut.
pub fn write_it() -> usize {
    let mut x: usize = 1;
    let y: usize = 2;
    call_fn_once(|| x += y);
    x
}

/// The FnMut control that was always clean, kept so the fork cannot narrow it —
/// byte-identical closure text, a `&mut {closure}` env.
pub fn write_it_mut() -> usize {
    let mut x: usize = 1;
    let y: usize = 2;
    call_fn_mut(|| x += y);
    x
}

fn main() {
    assert_eq!(write_it(), 3);
    assert_eq!(write_it_mut(), 3);
}

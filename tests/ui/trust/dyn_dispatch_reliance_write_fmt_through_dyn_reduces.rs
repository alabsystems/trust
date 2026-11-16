//@ revisions: ok panicking_write_str runtime_arg two_impls_one_panics overrides_write_fmt
//@ revisions: ok_codegen
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[ok] check-fail
//@[ok_codegen] compile-flags: -Ztrust-policy=advisory
//@[ok_codegen] build-pass
//@[panicking_write_str] check-fail
//@[runtime_arg] check-fail
//@[two_impls_one_panics] check-fail
//@[overrides_write_fmt] check-fail
//@ dont-check-compiler-stderr
//@[panicking_write_str] dont-require-annotations: ERROR
//@[runtime_arg] dont-require-annotations: ERROR
//@[two_impls_one_panics] dont-require-annotations: ERROR
//@[overrides_write_fmt] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[panicking_write_str] forbid-output: this function has no obligation of its own
//@[runtime_arg] forbid-output: this function has no obligation of its own
//@[two_impls_one_panics] forbid-output: this function has no obligation of its own
//@[overrides_write_fmt] forbid-output: this function has no obligation of its own
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): `ok` is now check-fail. `main` still
//! DISCHARGES both writes through the reduction (zero obligations; the pinned NOTE),
//! but the reduction is in no authenticated registry, so `main` publishes an `unknown`
//! row and is refused. The four check-fail revisions remain the gates: each FORBIDS
//! the zero-row note, so each must still refuse for its own reason, and the
//! differential with `ok` (note present vs forbidden) is kept. LOST: `ok` was
//! `build-pass`; codegen of this shape is no longer exercised here (recorded in the
//! DECISION_QUEUE entry) under a fail-closed policy; `ok_codegen` builds the same
//! `main` under `-Ztrust-policy=advisory` (`build-pass`), so the verifier still runs
//! over it and codegen and linking of the shape stay covered.
//!
//! **`write!(w, "lit")` through `&mut dyn Write` must discharge exactly when the
//! same call at the concrete type does.**
//!
//! One type `Buf` that inherits core's default `write_fmt`. Before the fix, ONE
//! compilation printed, adjacent, under `TRUST_DYN_RELIANCE_PROBE`:
//!
//!   write_fmt site=<Buf as core::fmt::Write>::write_fmt => DISCHARGED
//!       (every site reduces to its own proved `write_str`)
//!   C-FLOW declined: target std::fmt::Write::write_fmt is not local to this
//!       crate, so it has no independent verdict here
//!
//! Both entries resolve to the IDENTICAL monomorphic instance —
//! `Item(core::fmt::Write::write_fmt)` at `[Buf]` — so the tree credited a body
//! through one entry and refused the very same body through the other, on
//! `is_local()` alone. C-FLOW enumerated `Buf`, resolved the vtable slot to the
//! trait default, and asked the ordinary bar, which declines every foreign body.
//! The `static_str_write_fmt` reduction certifies precisely that body: on a
//! `from_str`-backed `Arguments` it performs one `<Self as Write>::write_str`
//! and returns its result. The dyn site was never offered to it, because the
//! `Virtual` arm files the site before the `else if` that offers a call.
//!
//! The fix asks the reduction PER ENUMERATED `Self` inside C-FLOW's loop, with
//! every one of its gates re-run — none bypassed. The four `check-fail`
//! revisions are those gates, one each, and each must keep refusing:
//!
//!   panicking_write_str  gate 4  the transferred-to body fails the shared bar
//!   runtime_arg          gate 3  `Arguments::new`, not `from_str`-backed
//!   two_impls_one_panics gate 4  C-FLOW's all-members conjunction
//!   overrides_write_fmt  gate 1  an override resolves to its OWN impl item,
//!                                never to the certified default body
//!
//! Note `write!(w, "{}", 1u32)` is NOT a gate-3 rail: rustc const-folds it to
//! `from_str_nonconst("1")`, which declines only because that wrapper carries no
//! diagnostic item — a rail on an accident. A genuine runtime argument
//! (`let x = b.0; write!(w, "{}", x)`) lowers to `Arguments::new::<2, 1>` and is
//! the real one.

use std::fmt::{self, Write};

#[cfg(any(ok, ok_codegen, runtime_arg))]
pub struct Buf(pub u32);
#[cfg(any(ok, ok_codegen, runtime_arg))]
impl Write for Buf {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        Ok(())
    }
}

#[cfg(any(ok, ok_codegen))]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[ok]~vv ERROR Trust strict verification failed for `dyn_dispatch_reliance_write_fmt_through_dyn_reduces::main`
//[ok]~v NOTE this function has no obligation of its own
fn main() {
    let mut b = Buf(0);
    // The concrete entry, which always discharged through the reduction.
    let _ = write!(b, "lit");
    let w: &mut dyn Write = &mut b;
    // A direct `write_str` through the trait object always discharged via C-FLOW.
    let _ = w.write_str("a");
    // The case: the SAME default body, entered through the vtable.
    let _ = write!(w, "lit");
}

// RAIL, gate 4: the body the obligation transfers to must itself pass the bar.
#[cfg(panicking_write_str)]
pub struct Bomb(pub u32);
#[cfg(panicking_write_str)]
impl Write for Bomb {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        panic!("boom")
    }
}
#[cfg(panicking_write_str)]
fn main() {
    let mut b = Bomb(0);
    let w: &mut dyn Write = &mut b;
    let _ = write!(w, "lit");
}

// RAIL, gate 3: a genuine runtime argument is `Arguments::new`, and the raw
// template loop with its `Argument::fmt` fn-pointer dispatch is then reachable.
#[cfg(runtime_arg)]
fn main() {
    let mut b = Buf(7);
    let x = b.0;
    let w: &mut dyn Write = &mut b;
    let _ = write!(w, "{}", x);
}

// RAIL, gate 4 across the enumerated set: every coerced `Self` must pass.
#[cfg(two_impls_one_panics)]
pub struct Good(pub u32);
#[cfg(two_impls_one_panics)]
impl Write for Good {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        Ok(())
    }
}
#[cfg(two_impls_one_panics)]
pub struct Bad(pub u32);
#[cfg(two_impls_one_panics)]
impl Write for Bad {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        panic!("boom")
    }
}
#[cfg(two_impls_one_panics)]
fn main() {
    let mut g = Good(0);
    let mut d = Bad(0);
    let wg: &mut dyn Write = &mut g;
    let _ = write!(wg, "lit");
    let wd: &mut dyn Write = &mut d;
    let _ = write!(wd, "lit");
}

// RAIL, gate 1: an impl that OVERRIDES `write_fmt` resolves to its own item, so
// the reduction's certificate — which is about core's DEFAULT body — does not
// apply, and the override must be judged on its own (here, refused).
#[cfg(overrides_write_fmt)]
pub struct Override(pub u32);
#[cfg(overrides_write_fmt)]
impl Write for Override {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        Ok(())
    }
    fn write_fmt(&mut self, _args: fmt::Arguments<'_>) -> fmt::Result {
        panic!("boom")
    }
}
#[cfg(overrides_write_fmt)]
fn main() {
    let mut o = Override(0);
    let w: &mut dyn Write = &mut o;
    let _ = write!(w, "lit");
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.

//@ needs-trust-verify
//@ revisions: println_err format_err to_string_err termination_err
//@ revisions: termination_nested_err branch_err mutated_err helper_err et_true_but_panics
//@ revisions: ok_println ok_format_to_string ok_termination u32_control
//@ revisions: termination_local_foreign_field termination_nested_foreign_outer
//@ revisions: termination_ref_local eprintln_debug_err ok_termination_foreign_field
//@ compile-flags: -Ztrust-verify=on
//@[println_err] compile-flags: -Copt-level=0
//@[format_err] compile-flags: -Copt-level=0
//@[to_string_err] compile-flags: -Copt-level=0
//@[termination_err] compile-flags: -Copt-level=0
//@[termination_nested_err] compile-flags: -Copt-level=0
//@[branch_err] compile-flags: -Copt-level=0
//@[mutated_err] compile-flags: -Copt-level=0
//@[helper_err] compile-flags: -Copt-level=0
//@[et_true_but_panics] compile-flags: -Copt-level=0
//@[ok_println] compile-flags: -Copt-level=0
//@[ok_format_to_string] compile-flags: -Copt-level=0
//@[ok_termination] compile-flags: -Copt-level=0
//@[u32_control] compile-flags: -Copt-level=0
//@[termination_local_foreign_field] compile-flags: -Copt-level=0
//@[termination_nested_foreign_outer] compile-flags: -Copt-level=0
//@[termination_ref_local] compile-flags: -Copt-level=0
//@[eprintln_debug_err] compile-flags: -Copt-level=0
//@[ok_termination_foreign_field] compile-flags: -Copt-level=0
//@[println_err] check-fail
//@[format_err] check-fail
//@[to_string_err] check-fail
//@[termination_err] check-fail
//@[termination_nested_err] check-fail
//@[branch_err] check-fail
//@[mutated_err] check-fail
//@[helper_err] check-fail
//@[et_true_but_panics] check-fail
//@[ok_println] build-pass
//@[ok_format_to_string] build-pass
//@[ok_termination] build-pass
//@[u32_control] build-pass
//@[termination_local_foreign_field] check-fail
//@[termination_nested_foreign_outer] check-fail
//@[termination_ref_local] check-fail
//@[eprintln_debug_err] check-fail
//@[ok_termination_foreign_field] build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 increment 0 (2026-09-23): ERROR TRANSPARENCY at the formatting sinks that
//! panic on `Err`.
//!
//! THE DEFECT (F1, measured on stage-1 `de437e35d`). A user `Display`/`Debug`
//! that is PANIC-FREE but returns `Err(fmt::Error)` without its writer failing
//! passed the shared panic-freedom bar that the packer gate's verified-impl
//! fallback (`618a1910e7`) and the `to_string` arm read, so each program below
//! built rc=0 on the default lane and exited 101 at runtime:
//!   * `println!("{}", E)`  -> `std/src/io/mod.rs:636` "a formatting trait
//!     implementation returned an error when the underlying stream did not";
//!   * `format!("{}", E)`   -> `alloc/src/fmt.rs:655`;
//!   * `E.to_string()`      -> `alloc/src/string.rs:2943`;
//!   * `fn main() -> Result<(), E> { Err(E) }` -> `io/mod.rs:636` through
//!     `Termination::report`, a call that is in `lang_start`, not in `main` —
//!     at `-Copt-level=0` AND `-Copt-level=2`, with no row and no warning at all.
//! The three sink runs carried an advisory saying the `_print` panic "can
//! dispatch into no user code", which was false for them.
//!
//! THE FIX. Error transparency (ET) is a REFUSAL-ONLY conjunct on the packer /
//! `to_string` fallback and a standalone refusal at `main`'s `Termination`
//! sink; recognizer version 0 accepts only an impl every one of whose return
//! values is `Ok(())`. The `*_err` revisions and the rails must be refused; the
//! `ok_*` controls must still build (they are the positive control that the
//! recognizer can say YES — pinned independently by the open-dispatch ladder's
//! `pf1`/`g4`).
//!
//! RAILS (each must stay refused):
//!   * `branch_err`      — `Ok` on one arm, `Err` on the other;
//!   * `mutated_err`     — `Ok(())` stored, then overwritten through `&mut`;
//!   * `helper_err`      — the return value is a call result (a helper returning
//!                         `Err`), never recognized under version 0;
//!   * `et_true_but_panics` — returns only `Ok(())` but can PANIC: ET must never
//!                         excuse a panic, the shared bar still refuses it;
//!   * `termination_nested_err` — `Result<Result<(), E>, u32>`: the inner `E` is
//!                         reached through `Result<T, _>: Termination`'s `T`.
//!   * `termination_local_foreign_field` — `struct E(io::Error)` whose `Debug`
//!                         returns `Err`: the type REACHES foreign code, but its
//!                         `Debug` is this crate's, so the entry row's "foreign or
//!                         dynamic type" statement does not cover it (review,
//!                         2026-09-23: before, rc=0 with a tolerated row, exit 101;
//!                         a whole-return-type deferral kept it that way);
//!   * `termination_nested_foreign_outer` — `Result<Result<(), E>, io::Error>`:
//!                         the OUTER error reaches foreign code, the INNER local `E`
//!                         must still be checked (before: X2 ICE; with X2 fixed and
//!                         a whole-type deferral, rc=0 and exit 101);
//!   * `termination_ref_local` — `Result<(), &'static E>`: core's `&T` forwarding
//!                         impl is not local, so it is refused (before: rc=0, NO
//!                         warning, exit 101);
//!   * `eprintln_debug_err` — the `new_debug` packer arm (the other `*_err`
//!                         packer revisions exercise `new_display`).
//! POSITIVE CONTROL `ok_termination_foreign_field` — `struct K(io::Error)` whose
//! `Debug` returns `Ok(())`: the per-error-type check says yes, and the entry row
//! (the type reaches foreign code) keeps it a reported conditional pass.
use std::fmt;

#[cfg(any(println_err, format_err, to_string_err))]
struct E;
#[cfg(any(println_err, format_err, to_string_err))]
impl fmt::Display for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

#[cfg(println_err)]
fn main() {
    //[println_err]~^ ERROR verification failed for
    //[println_err]~| NOTE error transparency
    println!("{}", E);
}

#[cfg(format_err)]
fn main() {
    //[format_err]~^ ERROR verification failed for
    let s = format!("{}", E);
    let _ = s.len();
}

#[cfg(to_string_err)]
fn main() {
    //[to_string_err]~^ ERROR verification failed for
    let s = E.to_string();
    let _ = s.len();
}

#[cfg(any(termination_err, termination_nested_err))]
struct D;
#[cfg(any(termination_err, termination_nested_err))]
impl fmt::Debug for D {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

#[cfg(termination_err)]
fn main() -> Result<(), D> {
    //[termination_err]~^ ERROR verification failed for
    //[termination_err]~| NOTE error transparency
    Err(D)
}

#[cfg(termination_nested_err)]
fn main() -> Result<Result<(), D>, u32> {
    //[termination_nested_err]~^ ERROR verification failed for
    Ok(Err(D))
}

#[cfg(branch_err)]
struct B(u32);
#[cfg(branch_err)]
impl fmt::Display for B {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 > 3 { Ok(()) } else { Err(fmt::Error) }
    }
}
#[cfg(branch_err)]
fn main() {
    //[branch_err]~^ ERROR verification failed for
    let n = std::env::args().count() as u32;
    println!("{}", B(n));
}

#[cfg(mutated_err)]
struct M;
#[cfg(mutated_err)]
impl fmt::Display for M {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut r = Ok(());
        let p = &mut r;
        *p = Err(fmt::Error);
        r
    }
}
#[cfg(mutated_err)]
fn main() {
    //[mutated_err]~^ ERROR verification failed for
    println!("{}", M);
}

#[cfg(helper_err)]
fn helper() -> fmt::Result {
    Err(fmt::Error)
}
#[cfg(helper_err)]
struct H;
#[cfg(helper_err)]
impl fmt::Display for H {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        helper()
    }
}
#[cfg(helper_err)]
fn main() {
    //[helper_err]~^ ERROR verification failed for
    println!("{}", H);
}

#[cfg(et_true_but_panics)]
struct P(usize);
#[cfg(et_true_but_panics)]
impl fmt::Display for P {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let table = [1u8, 2, 3];
        let _ = table[self.0];
        Ok(())
    }
}
#[cfg(et_true_but_panics)]
fn main() {
    //[et_true_but_panics]~^ ERROR verification failed for
    let n = std::env::args().count() + 5;
    println!("{}", P(n));
}

#[cfg(any(ok_println, ok_format_to_string, ok_termination))]
struct K;
#[cfg(any(ok_println, ok_format_to_string))]
impl fmt::Display for K {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
#[cfg(ok_termination)]
impl fmt::Debug for K {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[cfg(ok_println)]
fn main() {
    println!("{}", K);
}

#[cfg(ok_format_to_string)]
fn main() {
    let s = format!("{}", K);
    let _ = s.len();
    let t = K.to_string();
    let _ = t.len();
}

#[cfg(ok_termination)]
fn main() -> Result<(), K> {
    if std::env::args().count() == 7 { Err(K) } else { Ok(()) }
}

#[cfg(u32_control)]
fn main() -> Result<(), u32> {
    println!("{}", 5u32);
    let s = format!("{}", 7u32);
    let _ = s.len();
    Ok(())
}

#[cfg(any(termination_local_foreign_field, ok_termination_foreign_field))]
struct F(std::io::Error);
#[cfg(termination_local_foreign_field)]
impl fmt::Debug for F {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}
#[cfg(ok_termination_foreign_field)]
impl fmt::Debug for F {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[cfg(termination_local_foreign_field)]
fn main() -> Result<(), F> {
    //[termination_local_foreign_field]~^ ERROR verification failed for
    Err(F(std::io::Error::other("x")))
}

#[cfg(ok_termination_foreign_field)]
fn main() -> Result<(), F> {
    if std::env::args().count() == 7 { Err(F(std::io::Error::other("x"))) } else { Ok(()) }
}

#[cfg(any(termination_nested_foreign_outer, termination_ref_local, eprintln_debug_err))]
struct G;
#[cfg(any(termination_nested_foreign_outer, termination_ref_local, eprintln_debug_err))]
impl fmt::Debug for G {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

#[cfg(termination_nested_foreign_outer)]
fn main() -> Result<Result<(), G>, std::io::Error> {
    //[termination_nested_foreign_outer]~^ ERROR verification failed for
    Ok(Err(G))
}

#[cfg(termination_ref_local)]
static GG: G = G;
#[cfg(termination_ref_local)]
fn main() -> Result<(), &'static G> {
    //[termination_ref_local]~^ ERROR verification failed for
    Err(&GG)
}

#[cfg(eprintln_debug_err)]
fn main() {
    //[eprintln_debug_err]~^ ERROR verification failed for
    eprintln!("{:?}", G);
}

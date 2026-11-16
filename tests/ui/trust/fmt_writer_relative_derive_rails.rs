//@ needs-trust-verify
//@ edition: 2021
//@ revisions: nested_panicking_field nested_err_field_println nested_println_field
//@ revisions: vec_user_field dyn_field generic_derive_println boom_writer_derive
//@ revisions: six_named_fields constant_foreign_writer drop_glue_panics
//@ revisions: runtime_align_is_aligned_to
//@ revisions: mixed_fixed_direct_nary
//@ compile-flags: -Ztrust-verify=on
//@[nested_panicking_field] compile-flags: --crate-type lib -Copt-level=0
//@[nested_err_field_println] compile-flags: -Copt-level=0
//@[nested_println_field] compile-flags: --crate-type lib -Copt-level=0
//@[vec_user_field] compile-flags: --crate-type lib -Copt-level=0
//@[dyn_field] compile-flags: --crate-type lib -Copt-level=0
//@[generic_derive_println] compile-flags: -Copt-level=0
//@[boom_writer_derive] compile-flags: -Copt-level=0
//@[six_named_fields] compile-flags: --crate-type lib -Copt-level=0
//@[constant_foreign_writer] compile-flags: --crate-type lib -Copt-level=0
//@[drop_glue_panics] compile-flags: --crate-type lib -Copt-level=0
//@[runtime_align_is_aligned_to] compile-flags: --crate-type lib -Copt-level=0
//@[mixed_fixed_direct_nary] compile-flags: --crate-type lib -Copt-level=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D1 increment 2 (2026-09-25): RAILS for `#[derive(Debug)]` in the
//! writer-relative (WR) class. Every revision MUST STAY REFUSED; a green one is a
//! possible false proof until shown otherwise (memo risk 1). Each pin names the
//! function whose refusal is the point, so a revision refused for another reason
//! (a compile error in the fixture) does not satisfy it.
//!
//! * `nested_panicking_field`: a field whose hand-written `Debug` panics on one
//!   value. The nested-formatter target (`<&Inner as Debug>` peeled to the local
//!   `Inner::fmt`) passes neither bar, so the site is refused and so is `Outer`.
//!   Runtime truth (verification off): `format!("{:?}", Outer(Inner(7)))` exits
//!   101.
//! * `nested_err_field_println`: a field whose `Debug` writes and then returns
//!   `Err(fmt::Error)` — writer-relative, but NOT error-transparent. `Outer`
//!   compiles as a conditional pass; `println!` of it must be refused (error
//!   transparency version 2 recurses into the local nested target). Runtime
//!   truth: exit 101 in std ("a formatting trait implementation returned an
//!   error when the underlying stream did not").
//! * `nested_println_field`: a field whose `Debug` calls `println!` — its `_print`
//!   row is no writer edge, so it fails the writer-relative bar (zero vanilla
//!   rows) and cannot serve as a nested target. Refused at `Outer`.
//! * `vec_user_field`: `Vec<Inner>` — core peels `&Vec<Inner>` to alloc's
//!   `<Vec<Inner> as Debug>::fmt`, a sysroot impl at a NON-foundational type (it
//!   dispatches on into user code this rule does not follow). A documented
//!   residual, not a hole. Refused at `V`.
//! * `dyn_field`: `&'static dyn Debug` — the root's own `&self` carries a
//!   `dyn Debug`, which poisons the trait, so the target set cannot be
//!   enumerated. Refused at `D`.
//! * `generic_derive_println`: `#[derive(Debug)] struct G<T>(T)` — a generic
//!   impl is not a formatting-impl root (non-generic only), so `println!` of
//!   `G(1u32)` has no verdict to rest on. Refused at `main`.
//! * `boom_writer_derive`: a derived WR impl written into a LOCAL panicking
//!   `fmt::Write` (`write!(Boom, "{:?}", P(1))`) — not a std sink, so the writer
//!   premise is not discharged. Refused at `main`.
//! * `six_named_fields`: above five named fields the derive calls core's
//!   `debug_struct_fields_finish` directly, outside the authenticated fixed
//!   wrapper's argument-forwarding premise. A disclosed completeness cost.
//!   Refused at `Six`.
//! * `mixed_fixed_direct_nary`: a valid fixed-wrapper path and a direct n-ary
//!   path reach the same core helper. The invalid entry must win; a qualifying
//!   neighbor cannot authorize the direct call.
//! * `runtime_align_is_aligned_to` (96a18b, P-SPLIT): the names-split
//!   exemption does not count `is_aligned_to`'s body as an unrowed panic site,
//!   discharged ONLY by a constant power-of-two alignment at every walked
//!   call (or a call inside a UB-check member). This impl passes a RUNTIME
//!   alignment: the evidence fails, the exemption is void, and the writer row
//!   stays unexcused. Genuine, not just complete: `format!("{:?}", A(3))`
//!   panics ("align is not a power-of-two") before any writer is reached, so
//!   the impl is not panic-free relative to its writer. Refused at the impl
//!   (`TRUST_DYN_RELIANCE_PROBE`: "names-split evidence FAILED:
//!   `is_aligned_to` called from `<A as Debug>::fmt`").
//! * `constant_foreign_writer`: a user CONSTANT carrying `dyn fmt::Write`
//!   (`Option<&mut dyn Write>`) — the constant-poison relaxation covers ONLY
//!   core's `PadAdapter` slot, so this constant keeps its poison and the class is
//!   refused. Refused at the impl (it isolates that relaxation: the impl has no
//!   other refusing row — its writer edge alone is the i10 shape).
//!
//! * `drop_glue_panics` (added 2026-09-25 with the live increment): G-MEMBER no
//!   longer counts a `Drop` whose type has NO drop glue (`drop_runs_no_code` —
//!   the generic builders' `drop(value_fmt)` of a reference-capturing closure).
//!   A local whose type HAS drop glue — here a guard whose `Drop` asserts, which
//!   compiles on its own as a runtime-checked advisory — must still be counted:
//!   `format!("{}", G(7))` panics in the guard's destructor. Refused at the impl
//!   (`TRUST_DYN_RELIANCE_PROBE`: "G-MEMBER: unrowed panic site in `<G as
//!   Display>::fmt` at bb1: drop(_3)").
//! * `constant_foreign_writer` after the constant relaxation gained its value
//!   conjunct (2026-09-25): refused on BOTH conjuncts — the type is not
//!   `PadAdapter`-only, and the named constant reaches the walk UNEVALUATED, so
//!   `constant_value_holds_no_pointer` answers false too (measured, probe: "value
//!   holds no pointer: false").
//!
//! BEFORE (stage-1 snapshot `43b8fe6ab`): every revision rc=1; see the pins.
//! LIVE (stage-1 `d1i2-live`, 2026-09-25): every revision still rc=1.
#![cfg_attr(runtime_align_is_aligned_to, feature(pointer_is_aligned_to))]
#![cfg_attr(mixed_fixed_direct_nary, feature(fmt_helpers_for_derive))]
use std::fmt;
#[cfg(boom_writer_derive)]
use std::fmt::Write as _;

#[cfg(nested_panicking_field)]
pub struct Inner(pub u32);
#[cfg(nested_panicking_field)]
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 7 {
            panic!("seven")
        }
        f.write_str("i")
    }
}
#[cfg(nested_panicking_field)]
#[derive(Debug)]
//[nested_panicking_field]~^ ERROR Trust strict verification failed
pub struct Outer(pub Inner);

#[cfg(nested_err_field_println)]
pub struct Inner;
#[cfg(nested_err_field_println)]
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("i")?;
        Err(fmt::Error)
    }
}
#[cfg(nested_err_field_println)]
#[derive(Debug)]
pub struct Outer(pub Inner);
#[cfg(nested_err_field_println)]
fn main() { //[nested_err_field_println]~ ERROR Trust full verification failed
    println!("{:?}", Outer(Inner));
}

#[cfg(nested_println_field)]
pub struct Inner;
#[cfg(nested_println_field)]
impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        println!("inner");
        f.write_str("i")
    }
}
#[cfg(nested_println_field)]
#[derive(Debug)]
//[nested_println_field]~^ ERROR Trust strict verification failed
pub struct Outer(pub Inner);

#[cfg(vec_user_field)]
#[derive(Debug)]
pub struct Inner(pub u32);
#[cfg(vec_user_field)]
#[derive(Debug)]
//[vec_user_field]~^ ERROR Trust strict verification failed
pub struct V(pub Vec<Inner>);

#[cfg(dyn_field)]
#[derive(Debug)]
//[dyn_field]~^ ERROR Trust strict verification failed
pub struct D(pub &'static dyn fmt::Debug);

#[cfg(generic_derive_println)]
#[derive(Debug)]
pub struct G<T>(pub T);
#[cfg(generic_derive_println)]
fn main() { //[generic_derive_println]~ ERROR Trust full verification failed
    println!("{:?}", G(std::hint::black_box(1u32)));
}

#[cfg(boom_writer_derive)]
#[derive(Debug)]
pub struct P(pub u32);
#[cfg(boom_writer_derive)]
pub struct Boom(pub u32);
#[cfg(boom_writer_derive)]
impl fmt::Write for Boom {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.len() == 1 {
            panic!("boom writer")
        }
        self.0 = self.0.wrapping_add(1);
        Ok(())
    }
}
#[cfg(boom_writer_derive)]
fn main() { //[boom_writer_derive]~ ERROR verification failed for
    let mut b = Boom(0);
    let _ = write!(b, "{:?}", P(1));
}

#[cfg(six_named_fields)]
#[derive(Debug)]
//[six_named_fields]~^ ERROR Trust strict verification failed
pub struct Six {
    pub a: u8,
    pub b: u8,
    pub c: u8,
    pub d: u8,
    pub e: u8,
    pub f: u8,
}

#[cfg(mixed_fixed_direct_nary)]
pub struct Mixed(pub bool);
#[cfg(mixed_fixed_direct_nary)]
impl fmt::Debug for Mixed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[mixed_fixed_direct_nary]~^ ERROR Trust strict verification failed
        if self.0 {
            f.debug_struct_field2_finish("Mixed first second", &1u8, &2u8)
        } else {
            f.debug_struct_fields_finish("Mixed first second", &[&1u8, &2u8])
        }
    }
}

#[cfg(constant_foreign_writer)]
const NO_WRITER: Option<&'static mut dyn fmt::Write> = None;
#[cfg(constant_foreign_writer)]
pub struct C;
#[cfg(constant_foreign_writer)]
impl fmt::Display for C {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[constant_foreign_writer]~^ ERROR Trust strict verification failed
        if let Some(w) = NO_WRITER {
            w.write_char('c')?;
        }
        f.write_str("c")
    }
}

#[cfg(drop_glue_panics)]
pub struct Guard(pub u32);
#[cfg(drop_glue_panics)]
impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 != 7);
    }
}
#[cfg(drop_glue_panics)]
pub struct G(pub u32);
#[cfg(drop_glue_panics)]
impl fmt::Display for G {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[drop_glue_panics]~^ ERROR Trust strict verification failed
        let _guard = Guard(self.0);
        f.write_str("g")
    }
}

#[cfg(runtime_align_is_aligned_to)]
pub struct A(pub usize);
#[cfg(runtime_align_is_aligned_to)]
impl fmt::Debug for A {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //[runtime_align_is_aligned_to]~^ ERROR Trust strict verification failed
        let p = self as *const Self;
        if !p.is_aligned_to(self.0) {
            return f.write_str("unaligned");
        }
        f.write_str("aligned")
    }
}

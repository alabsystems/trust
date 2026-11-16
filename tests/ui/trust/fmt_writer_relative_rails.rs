//@ needs-trust-verify
//@ edition: 2021
//@ revisions: debugmap_misuse boom_sink err_after_write
//@ revisions: println_inside_display local_dyn_write_coercion
//@ revisions: unsafe_body skip_attr requires_on_fmt generic_impl panic_in_display
//@ revisions: write_macro_literal helper_direct_call
//@ compile-flags: -Ztrust-verify=on
//@[debugmap_misuse] compile-flags: --crate-type lib -Copt-level=0
//@[boom_sink] compile-flags: -Copt-level=0
//@[err_after_write] compile-flags: -Copt-level=0
//@[println_inside_display] compile-flags: -Copt-level=0
//@[local_dyn_write_coercion] compile-flags: --crate-type lib -Copt-level=0
//@[unsafe_body] compile-flags: --crate-type lib -Copt-level=0
//@[skip_attr] compile-flags: -Copt-level=0
//@[requires_on_fmt] compile-flags: -Copt-level=0
//@[generic_impl] compile-flags: -Copt-level=0
//@[panic_in_display] compile-flags: --crate-type lib -Copt-level=0
//@[write_macro_literal] compile-flags: --crate-type lib -Copt-level=0
//@[helper_direct_call] compile-flags: --crate-type lib -Copt-level=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 increment 1 (2026-09-25): RAILS for the writer-relative (WR) class. Every
//! revision here MUST STAY REFUSED; a green one is a possible false proof until
//! shown otherwise (memo risk 1). Each pin names the refusal it expects, so a
//! revision that fails for some other reason does not satisfy it.
//!
//! * `debugmap_misuse` (F2, the G-MEMBER rail): `DebugMap::key` twice panics in
//!   core's own `assert!` (unverified run: exit 101, `core/src/fmt/builders.rs`),
//!   and that `assert!` mints no row. Refused at the impl.
//! * `boom_sink`: a WR impl written into a LOCAL panicking `fmt::Write`
//!   (`write!(Boom, "{}", S)`): not a std sink, so the writer premise is not
//!   discharged. Refused at `main`, with the WR sink note.
//! * `err_after_write{,_o2}`: `f.write_str("x")?; Err(fmt::Error)` — WR (it
//!   compiles, conditional) but NOT error-transparent: `println!` of it panics in
//!   std. Refused at `main` with the error-transparency note.
//! * `println_inside_display{,_o2}`: a `println!` inside `Display::fmt` is a
//!   non-writer `_print` call (no crash: stdout's lock is reentrant). The impl keeps a
//!   `_print` row, and the WR bar excuses ONLY writer edges (zero vanilla rows).
//!   Refused at `main`.
//! * `local_dyn_write_coercion`: `let w: &mut dyn fmt::Write = f;` — a coercion to
//!   `dyn fmt::Write` inside the bundle refuses the class. Refused at the impl.
//! * `unsafe_body`, `skip_attr`, `requires_on_fmt`, `generic_impl`: the root
//!   predicate refuses `unsafe`, `#[trust::skip]`, an authored clause, and a
//!   generic impl; the sink is refused at `main` (the impl-side refusals are not
//!   pinned where they may carry other errors).
//! * `panic_in_display`: a diverging call (`panic!`) in the root — G-MEMBER.
//!   Refused at the impl (a `main` here would fail its own lowering first).
//! * `write_macro_literal`: `write!(f, "lit")` goes through `Formatter::write_fmt`
//!   and `core::fmt::write`, which are NOT writer edges (increment 3). Refused at
//!   the impl.
//! * `helper_direct_call`: memo risk 5's control — a local NON-formatting-impl
//!   function that calls a WR impl directly with a `Formatter` it was handed is
//!   not a WR root (increment 3 would make it one), so the impl's writer edge,
//!   charged in its bundle, stays fatal. Refused at the helper.
//!
//! BEFORE (stage-1 snapshot `4e9fe36bf`): every revision rc=1 — see the per-pin
//! notes; the writer-forwarding impls were refused on their own writer rows.
#![cfg_attr(skip_attr, feature(register_tool))]
#![cfg_attr(skip_attr, register_tool(trust))]
use std::fmt;
#[cfg(boom_sink)]
use std::fmt::Write as _;

#[cfg(debugmap_misuse)]
pub struct M;
#[cfg(debugmap_misuse)]
impl fmt::Debug for M {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[debugmap_misuse]~^ ERROR Trust strict verification failed
        f.debug_map().key(&1u32).key(&2u32).finish()
    }
}

#[cfg(any(boom_sink, err_after_write))]
pub struct S;
#[cfg(boom_sink)]
impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("s")
    }
}
#[cfg(boom_sink)]
pub struct Boom(pub u32);
#[cfg(boom_sink)]
impl fmt::Write for Boom {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if s.len() == 1 {
            panic!("boom writer");
        }
        self.0 = self.0.wrapping_add(1);
        Ok(())
    }
}
#[cfg(boom_sink)]
fn main() {
    //[boom_sink]~^ ERROR verification failed for
    //[boom_sink]~| NOTE panic-free only relative to its `Formatter`'s writer
    let mut b = Boom(0);
    let _ = write!(b, "{}", S);
}

#[cfg(err_after_write)]
impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("x")?;
        Err(fmt::Error)
    }
}
#[cfg(err_after_write)]
fn main() {
    //[err_after_write]~^ ERROR verification failed for
    //[err_after_write]~| NOTE error transparency
    println!("{}", S);
}

#[cfg(println_inside_display)]
pub struct P;
#[cfg(println_inside_display)]
impl fmt::Display for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        println!("inner");
        f.write_str("p")
    }
}
#[cfg(println_inside_display)]
fn main() {
    //[println_inside_display]~^ ERROR verification failed for
    println!("{}", P);
}

#[cfg(local_dyn_write_coercion)]
pub struct L;
#[cfg(local_dyn_write_coercion)]
impl fmt::Display for L {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[local_dyn_write_coercion]~^ ERROR Trust strict verification failed
        let w: &mut dyn fmt::Write = f;
        w.write_str("l")
    }
}

#[cfg(unsafe_body)]
pub struct U(pub u32);
#[cfg(unsafe_body)]
impl fmt::Display for U {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[unsafe_body]~^ ERROR verification failed for
        let p = &self.0 as *const u32;
        let v = unsafe { *p };
        if v == 7 { f.write_str("seven") } else { f.write_str("other") }
    }
}

#[cfg(skip_attr)]
pub struct K;
#[cfg(skip_attr)]
impl fmt::Display for K {
    #[trust::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("k")
    }
}
#[cfg(skip_attr)]
fn main() {
    //[skip_attr]~^ ERROR verification failed for
    println!("{}", K);
}

#[cfg(requires_on_fmt)]
pub struct R(pub u32);
#[cfg(requires_on_fmt)]
impl fmt::Display for R {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
        ensures result == result
    {
        f.write_str("r")
    }
}
#[cfg(requires_on_fmt)]
fn main() {
    //[requires_on_fmt]~^ ERROR verification failed for
    println!("{}", R(1));
}

#[cfg(generic_impl)]
pub struct W<T>(pub T);
#[cfg(generic_impl)]
impl<T: fmt::Display> fmt::Display for W<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("w")
    }
}
#[cfg(generic_impl)]
fn main() {
    //[generic_impl]~^ ERROR verification failed for
    println!("{}", W(1u32));
}

#[cfg(panic_in_display)]
pub struct Z(pub u32);
#[cfg(panic_in_display)]
impl fmt::Display for Z {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[panic_in_display]~^ ERROR Trust strict verification failed
        if self.0 == 3 {
            panic!("three");
        }
        f.write_str("z")
    }
}

#[cfg(write_macro_literal)]
pub struct Lit;
#[cfg(write_macro_literal)]
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[write_macro_literal]~^ ERROR verification failed for
        write!(f, "lit")
    }
}

#[cfg(helper_direct_call)]
pub struct H;
#[cfg(helper_direct_call)]
impl fmt::Display for H {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("h")
    }
}
#[cfg(helper_direct_call)]
pub fn show(h: &H, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //[helper_direct_call]~^ ERROR Trust strict verification failed
    fmt::Display::fmt(h, f)
}

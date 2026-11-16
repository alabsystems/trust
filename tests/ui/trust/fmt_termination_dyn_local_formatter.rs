//@ needs-trust-verify
//@ revisions: box_new_err qmark_err into_err dyn_debug_err send_sync_err
//@ revisions: generic_helper_err from_fn_closure_err helper_result_err skip_attr_debug
//@ revisions: display_err_only io_error_other_err
//@ revisions: option_wrap_err fn_item_static_err closure_static_err
//@ revisions: ok_box_new ok_qmark parse_int_control string_control ok_only_control
//@ revisions: visible_row
//@ compile-flags: -Ztrust-verify=on
//@[box_new_err] compile-flags: -Copt-level=0
//@[qmark_err] compile-flags: -Copt-level=0
//@[into_err] compile-flags: -Copt-level=0
//@[dyn_debug_err] compile-flags: -Copt-level=0
//@[send_sync_err] compile-flags: -Copt-level=0
//@[generic_helper_err] compile-flags: -Copt-level=0
//@[from_fn_closure_err] compile-flags: -Copt-level=0
//@[helper_result_err] compile-flags: -Copt-level=0
//@[skip_attr_debug] compile-flags: -Copt-level=0
//@[display_err_only] compile-flags: -Copt-level=0
//@[io_error_other_err] compile-flags: -Copt-level=0
//@[option_wrap_err] compile-flags: -Copt-level=0
//@[fn_item_static_err] compile-flags: -Copt-level=0
//@[closure_static_err] compile-flags: -Copt-level=0
//@[ok_box_new] compile-flags: -Copt-level=0
//@[ok_qmark] compile-flags: -Copt-level=0
//@[parse_int_control] compile-flags: -Copt-level=0
//@[string_control] compile-flags: -Copt-level=0
//@[ok_only_control] compile-flags: -Copt-level=0
//@[visible_row] compile-flags: -Copt-level=0
//@[box_new_err] check-fail
//@[qmark_err] check-fail
//@[into_err] check-fail
//@[dyn_debug_err] check-fail
//@[send_sync_err] check-fail
//@[generic_helper_err] check-fail
//@[from_fn_closure_err] check-fail
//@[helper_result_err] check-fail
//@[skip_attr_debug] check-fail
//@[display_err_only] check-fail
//@[io_error_other_err] check-fail
//@[option_wrap_err] check-fail
//@[fn_item_static_err] check-fail
//@[closure_static_err] check-fail
//@[ok_box_new] build-pass
//@[ok_qmark] build-pass
//@[parse_int_control] build-pass
//@[string_control] build-pass
//@[ok_only_control] build-pass
//@[visible_row] build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// -O parity (2026-09-25): each `_o2` revision states `-Zmir-opt-level=2`, the only
// verifying session that still runs the MIR inliner/GVN; a plain `-Copt-level=2` now
// runs the `-O0` MIR pipeline, which the `-Copt-level=0` twin already pins.
//! D1 residual (2026-09-24): `main`'s `Termination` sink over a FOREIGN or
//! DYNAMIC error, and the LOCAL formatting code that error can dispatch into.
//!
//! THE DEFECT, measured on stage-1 with wave 0 landed (`a8c853de6f`). Wave 0's
//! `Termination` check defers an error type that reaches foreign/dynamic code and
//! names no local definition (`Box<dyn Error>`, `io::Error`) to the policy-B entry
//! row, whose statement is "dispatches the `Debug`/`Drop` of a foreign or dynamic
//! type this compilation does not verify". For a LOCAL `E` boxed into that type
//! the statement is false — the `Debug` that runs is this crate's — and:
//!   * `box_new_err`, `box_new_err_o2`, `dyn_debug_err`, `send_sync_err`,
//!     `from_fn_closure_err`: built rc=0 with ZERO warnings, exited 101
//!     ("a formatting trait implementation returned an error when the underlying
//!     stream did not");
//!   * `qmark_err`, `into_err`, `generic_helper_err`: built rc=0 (only unrelated
//!     advisory warnings), exited 101 — the coercion to `dyn Error` is inside
//!     alloc's `From` impl or a local POLYMORPHIC helper, so no enumeration of this
//!     crate's own coercion sites would have seen `E` at all;
//!   * `from_fn_closure_err`: the code that returns `Err` is a CLOSURE handed to
//!     `fmt::from_fn`, not an impl of any type.
//!
//! THE FIX (`trust_verify/fmt_termination_dyn.rs`). When `main` returns a deferred
//! layer, every local formatting body (a local fn, method or closure taking a
//! `fmt::Formatter` and returning a `Result`) must pass the same sink bar the
//! packer arm reads: verified panic-free AND error-transparent (version 0: it
//! returns only `Ok(())`). Foreign code keeps the policy-B row; `visible_row`
//! pins that the row is now a visible warning on bare `trustc`.
//!
//! MUST STAY REFUSED (rails): every `*_err` revision, `skip_attr_debug` (a
//! `#[trust::skip]` formatter is unverified, whatever it returns), and
//! `io_error_other_err` (already refused before this change on its own rows; kept
//! so a change there cannot silently open this path).
//!
//! `display_err_only` is a DOCUMENTED OVER-REFUSAL: `E`'s `Debug` returns `Ok(())`
//! and only its `Display` returns `Err`, which `Box<dyn Error>`'s `Debug` never
//! calls. It is refused because the candidate set is every local formatting body
//! (a `Display` IS reachable from a deferred error through, e.g., a `'static`
//! `fmt::Arguments` in a `Box<dyn Debug>`). Such a `Display` is refused at every
//! other std sink (`println!`/`format!`/`to_string`) anyway. Flipping this
//! revision needs a reachability argument, not a relaxed bar.
//!
//! The controls must BUILD: `ok_box_new`/`ok_qmark` (local `E` whose formatters
//! return only `Ok(())`), `parse_int_control`/`string_control` (std error types
//! boxed through `?`, with an unrelated Ok-only local formatter present), and
//! `ok_only_control`.
#![cfg_attr(skip_attr_debug, feature(register_tool))]
#![cfg_attr(skip_attr_debug, register_tool(trust))]

use std::error::Error;
use std::fmt;

pub struct E;

#[cfg(any(
    box_new_err,
    qmark_err,
    into_err,
    dyn_debug_err,
    send_sync_err,
    generic_helper_err,
    io_error_other_err,
    option_wrap_err
))]
impl fmt::Debug for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

#[cfg(helper_result_err)]
fn helper() -> fmt::Result {
    Err(fmt::Error)
}

#[cfg(helper_result_err)]
impl fmt::Debug for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        helper()
    }
}

#[cfg(skip_attr_debug)]
impl fmt::Debug for E {
    #[trust::skip]
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[cfg(not(
    any(
        box_new_err,
        qmark_err,
        into_err,
        dyn_debug_err,
        send_sync_err,
        generic_helper_err,
        io_error_other_err,
        option_wrap_err,
        helper_result_err,
        skip_attr_debug
    )
))]
impl fmt::Debug for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[cfg(display_err_only)]
impl fmt::Display for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

#[cfg(not(display_err_only))]
impl fmt::Display for E {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Error for E {}

#[cfg(any(box_new_err, helper_result_err, skip_attr_debug, display_err_only, ok_box_new))]
fn main() -> Result<(), Box<dyn Error>> {
    //[box_new_err,helper_result_err,skip_attr_debug,display_err_only]~^ ERROR verification failed for
    Err(Box::new(E))
}

#[cfg(any(qmark_err, ok_qmark))]
fn main() -> Result<(), Box<dyn Error>> {
    //[qmark_err]~^ ERROR verification failed for
    Err(E)?;
    Ok(())
}

#[cfg(into_err)]
fn main() -> Result<(), Box<dyn Error>> {
    //[into_err]~^ ERROR verification failed for
    Err(E.into())
}

#[cfg(dyn_debug_err)]
fn main() -> Result<(), Box<dyn fmt::Debug>> {
    //[dyn_debug_err]~^ ERROR verification failed for
    Err(Box::new(E))
}

#[cfg(send_sync_err)]
fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    //[send_sync_err]~^ ERROR verification failed for
    Err(Box::new(E))
}

#[cfg(generic_helper_err)]
fn boxit<T: Error + 'static>(t: T) -> Box<dyn Error> {
    Box::new(t)
}

#[cfg(generic_helper_err)]
fn main() -> Result<(), Box<dyn Error>> {
    //[generic_helper_err]~^ ERROR verification failed for
    Err(boxit(E))
}

#[cfg(from_fn_closure_err)]
fn main() -> Result<(), Box<dyn fmt::Debug>> {
    //[from_fn_closure_err]~^ ERROR verification failed for
    Err(Box::new(fmt::from_fn(|_f| Err(fmt::Error))))
}

#[cfg(io_error_other_err)]
fn main() -> std::io::Result<()> {
    //[io_error_other_err]~^ ERROR verification failed for
    Err(std::io::Error::other(E))
}

#[cfg(parse_int_control)]
fn main() -> Result<(), Box<dyn Error>> {
    let x: u32 = "7".parse()?;
    let _ = x;
    Ok(())
}

#[cfg(string_control)]
fn main() -> Result<(), Box<dyn Error>> {
    Err(String::from("bad"))?;
    Ok(())
}

#[cfg(ok_only_control)]
fn main() -> Result<(), Box<dyn Error>> {
    Ok(())
}

#[cfg(visible_row)]
fn main() -> std::io::Result<()> {
    //[visible_row]~^ WARN is dispatched by `lang_start`
    Ok(())
}

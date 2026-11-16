//~ NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `<T as core::convert::AsRef<format_args_body_controls_not_admitted::Vb>>::as_ref`
//~| NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `<W as core::fmt::Write>::write_fmt`
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 T-D (2026-10-12) controls for `format_args_body_admitted.rs`: the `format_args!`
//! desugaring's own `Arguments::new` call no longer refuses a generic body by itself, but
//! nothing else is relaxed. Each control keeps its open dispatch as a class (c) `failed`
//! absent-callee row and mints no instance hypothesis:
//! * `fmt_and_user_unsafe`: a formatting body that also calls an `unsafe fn` from a user
//!   `unsafe` block — that call is not the desugaring's `Arguments::new`, so the census's
//!   unsafe-call arm (and the user-`unsafe` fences) still refuse the body;
//! * `write_into_generic`: `w.write_fmt(format_args!(..))` on a generic writer — the body
//!   is admitted, but the site's by-value `fmt::Arguments` argument holds `NonNull`s, so
//!   `decide_arg` still refuses that site.

pub struct Vb(pub u32);

/// # Safety
/// None needed; an `unsafe fn` only so that calling it is an unsafe-signature call.
pub unsafe fn user_unsafe_ident(x: u32) -> u32 {
    x
}

pub fn fmt_and_user_unsafe<T: AsRef<Vb>>(vb: &T, x: u32) -> Result<u32, String> {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::fmt_and_user_unsafe`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::fmt_and_user_unsafe`
    //[strict]~^^^ ERROR Trust strict verification failed for `format_args_body_controls_not_admitted::fmt_and_user_unsafe`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::fmt_and_user_unsafe`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `format_args_body_controls_not_admitted::fmt_and_user_unsafe`
    let vb = vb.as_ref();
    // `user_unsafe_ident` has no precondition. Deliberately not a SAFETY comment, which
    // would declare this block (SAFETY-ASSUME-1) and add a `certify` refusal.
    let b = unsafe { user_unsafe_ident(x) };
    if b == 0 {
        return Err(format!("bad b={b}"));
    }
    Ok(vb.0.wrapping_add(b))
}

pub fn write_into_generic<W: core::fmt::Write>(w: &mut W, n: u32) -> core::fmt::Result {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::write_into_generic`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::write_into_generic`
    //[strict]~^^^ ERROR Trust strict verification failed for `format_args_body_controls_not_admitted::write_into_generic`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `format_args_body_controls_not_admitted::write_into_generic`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `format_args_body_controls_not_admitted::write_into_generic`
    w.write_fmt(format_args!("n={n}"))
}

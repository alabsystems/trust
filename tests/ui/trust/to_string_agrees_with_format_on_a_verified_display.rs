//@ revisions: ok panicking
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[ok] build-pass
//@[panicking] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **`d.to_string()` must agree with `format!("{}", d)`.**
//!
//! The hidden-packer hole exists because `x.to_string()` is
//! `<T as ToString>::to_string(&x)`, whose `new_display::<T>` packer lives inside
//! the alloc blanket impl body, out of this function's MIR -- so the packer scan
//! never sees `T`, and the gate reads `T` off the dispatch call instead. Its own
//! comment says the point is that `d.to_string()` behaves "exactly like
//! `format!(\"{}\", d)`".
//!
//! It stopped doing that. On 2026-09-19 the packer arm gained a fallback to the
//! formatting impl's OWN verdict (`fmt_target_is_verified_panic_free`) and this
//! arm did not, so a user `Display` that this compilation proves panic-free
//! formatted fine through `format!` and refused through `to_string`.
//!
//! The impl body is `Ok(())` deliberately. A body calling `f.write_str(..)` is
//! NOT provable today -- `write_str` is an undischarged absent callee, so the
//! impl carries an unproved row of its own and the fallback correctly declines
//! for it. That is a different, still-open boundary (the C-FLOW / write_fmt
//! reduction), and conflating the two would make this fixture pass or fail for
//! the wrong reason. What is pinned here is only: GIVEN a Display impl this
//! compilation proves, `to_string` and `format!` must agree.
//!
//! Note the fallback could NOT be wired by reusing the packer entry point: it
//! derives the formatting trait from the packer's own bound, and handed
//! `ToString::to_string` it finds `Self: ToString`, which has no `fmt` item -- so
//! the check would have answered `false` always and the change would have been
//! INERT. The `to_string` route names `Display` directly.

#[cfg(ok)]
pub struct D;
#[cfg(ok)]
impl std::fmt::Display for D {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Ok(()) }
}

/// The case at issue.
#[cfg(ok)]
pub fn via_to_string() -> String { D.to_string() }

/// The sibling it must agree with, which already compiled.
#[cfg(ok)]
pub fn via_format() -> String { format!("{}", D) }

/// A foundational `Self` still passes, as it always did.
#[cfg(ok)]
pub fn foundational_to_string() -> String { 41i32.to_string() }

// RAIL: a `Display` impl that can panic is not proved, so it must still refuse --
// the fallback consults a verdict, it does not grant one.
#[cfg(panicking)]
pub struct B;
#[cfg(panicking)]
impl std::fmt::Display for B {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { panic!("boom") }
}
#[cfg(panicking)]
pub fn panicking_to_string() -> String { B.to_string() }

fn main() {}

//@ needs-trust-verify
//@ edition: 2021
//@ revisions: gmember_from_digit vanilla_after_writer
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D1 increment 1: rails that ISOLATE two load-bearing guards of the
//! writer-relative (WR) bar. Found by its adversarial review (2026-09-25): the
//! existing rails are refused by OTHER rows before these guards run.
//!
//! * `gmember_from_digit` isolates G-MEMBER (no bundled member may carry a
//!   diverging site). `char::from_digit(n, 40)` panics inside a BUNDLED core
//!   member whose `panic_fmt` mints no row of its own; the impl's only other rows
//!   are writer edges. Runtime truth (verification off): exit 101.
//! * `vanilla_after_writer` isolates "every folded site is a writer edge". The
//!   writer edge comes FIRST, so the whole-function aggregate is NAMED after it;
//!   `copy_from_slice` (a ruled policy-B vanilla conditional pass that panics on a
//!   length mismatch) is only a co-folded site. Runtime truth: exit 101.
//!
//! Both must stay refused at `main`.
//!
//! CORRECTION (D1 increment 2, 2026-09-25): before increment 2,
//! `gmember_from_digit` did NOT isolate G-MEMBER. Measured on the stage-1
//! snapshot `43b8fe6ab`: `TRUST_MASK_TRACE` names `<Formatter<'_> as
//! Write>::write_char(..)` as a masked fail-closed source in `D::fmt`, which
//! withheld the writer-relative excuse before G-MEMBER was ever consulted.
//! Increment 2 stops counting exactly that call in a writer-relative root
//! (`fmt_writer_relative::writer_relative_body_has_masked_source`); from then on
//! the impl's refusal rests on G-MEMBER alone (`char::from_digit` and
//! `core::panicking::panic_fmt` are walked into the bundle — `TRUST_VANILLA_DEBUG`
//! `[VANILLA_BUNDLE]` — and `from_digit`'s radix `panic!` is a diverging call with
//! no row). Predicted still refused at both pins; the lead's run records it.
use std::fmt;

#[cfg(gmember_from_digit)]
mod m {
    use std::fmt;
    use std::fmt::Write as _;
    pub struct D(pub u32, pub u32);
    impl fmt::Display for D {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[gmember_from_digit]~^ ERROR Trust strict verification failed
            f.write_char(char::from_digit(self.0, self.1).unwrap_or('?'))
        }
    }
}

#[cfg(gmember_from_digit)]
fn main() { //[gmember_from_digit]~ ERROR Trust full verification failed
    let r = std::hint::black_box(40u32);
    println!("{}", m::D(3, r));
}

#[cfg(vanilla_after_writer)]
pub struct C<'a>(pub &'a [u8]);

#[cfg(vanilla_after_writer)]
impl<'a> fmt::Display for C<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("c")?;
        let mut dst = [0u8; 4];
        dst.copy_from_slice(self.0);
        Ok(())
    }
}

#[cfg(vanilla_after_writer)]
fn main() { //[vanilla_after_writer]~ ERROR Trust full verification failed
    let s: &[u8] = std::hint::black_box(&[1u8, 2, 3]);
    println!("{}", C(s));
}

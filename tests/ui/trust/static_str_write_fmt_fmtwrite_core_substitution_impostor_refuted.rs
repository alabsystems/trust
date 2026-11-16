//@ needs-trust-verify
//@ edition: 2021
//@ revisions: impostor resident
//@[impostor] aux-crate: core=fmtwrite_impostor/core.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[impostor] check-fail
//@[resident] check-fail
//@[impostor] forbid-output: => DISCHARGED (every site reduces to its own proved
//@[impostor] forbid-output: via the write_fmt reduction
//[resident]~? RAW write_fmt site=<static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::W as core::fmt::Write>::write_fmt (1 site(s)) => DISCHARGED (every site reduces to its own proved
//[resident]~? RAW C-FLOW admitted W via the write_fmt reduction
//! THE PLANTED REFUTATION for the static-str `write_fmt` reduction
//! (`trust_verify/static_str_write_fmt.rs`, and its `dyn` twin, the C-FLOW arm in
//! `dyn_dispatch_reliance.rs`) identifying core's default `fmt::Write::write_fmt`
//! from SOURCE-DECLARABLE anchors only: the `FmtWrite` and
//! `FmtArgumentsFromStr` diagnostic items.
//!
//! The reduction is a GRANT: for `w.write_fmt(Arguments::from_str(lit))` it reads
//! core's default `write_fmt` body (module docs) and discharges the call's
//! absent-callee row when the receiver's own `write_str` is verified. That
//! reading is about the real `core` only.
//!
//! `impostor`: `core` is a whole-`core` substitute
//! (`auxiliary/fmtwrite_impostor/core.rs`, crate name `core`, verify-off,
//! `--extern core=`) whose `write_fmt` default PANICS on every call. Both lanes
//! took it for core's: `write_fmt site=… => DISCHARGED (every site reduces to its
//! own proved `write_str`)` for `concrete`, and `C-FLOW admitted W via the
//! write_fmt reduction` for the `dyn` call in `through_dyn`. No false
//! proof followed, because the bridge's own residency check kept each row
//! (`1 runtime-checked`, refused under `certify`), but the compiler-side grant
//! was made for a body it never read. The fix anchors every identity of the
//! reduction on AUTHENTIC core (`crate_is_authentic_core`: owner of `Sized` AND
//! resident in this compiler's own sysroot).
//!
//! `resident`: the HONEST CONTROL. The same calls on this compiler's own `core`
//! (through `write!`, which expands to `Arguments::from_str` for a literal) are
//! still discharged by both lanes and build under `certify`.
//!
//! MEASURED: see the commit that adds this file. Fix the compiler, not this file.
#![no_std]

use core::fmt::Write;

pub struct W;

impl Write for W {
    fn write_str(&mut self, _s: &str) -> core::fmt::Result {
        core::result::Result::Ok(())
    }
    fn write_char(&mut self, _c: char) -> core::fmt::Result {
        core::result::Result::Ok(())
    }
}

#[cfg(impostor)]
pub fn concrete(w: &mut W) -> core::fmt::Result {
    //[impostor]~^ ERROR Trust strict verification failed for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::concrete`
    //[impostor]~| ERROR Trust Level 0 safety verification incomplete for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::concrete`
    w.write_fmt(core::fmt::Arguments::from_str("x"))
}

#[cfg(resident)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[resident]~vv ERROR Trust strict verification failed for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::concrete`
//[resident]~v NOTE this function has no obligation of its own
pub fn concrete(w: &mut W) -> core::fmt::Result {
    write!(w, "x")
}

#[cfg(impostor)]
pub fn through_dyn() -> core::fmt::Result {
    //[impostor]~^ ERROR Trust strict verification failed for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::through_dyn`
    //[impostor]~| ERROR Trust Level 0 safety verification incomplete for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::through_dyn`
    let mut w = W;
    let d: &mut dyn Write = &mut w;
    d.write_fmt(core::fmt::Arguments::from_str("x"))
}

#[cfg(resident)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[resident]~vv ERROR Trust strict verification failed for `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted::through_dyn`
//[resident]~v NOTE this function has no obligation of its own
pub fn through_dyn() -> core::fmt::Result {
    let mut w = W;
    let d: &mut dyn Write = &mut w;
    write!(d, "x")
}

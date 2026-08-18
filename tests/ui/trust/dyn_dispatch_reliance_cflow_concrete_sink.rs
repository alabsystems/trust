//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! C-FLOW: a `dyn` call whose receiver's vtable provenance is COMPLETE inside the
//! bundle discharges by CASE SPLIT over the enumerated `Self` types.
//!
//! `write!(sink, …)` reaches `<dyn core::fmt::Write>::write_str` through three
//! core bodies (`Write::write_fmt` → `spec_write_fmt` → `core::fmt::write` →
//! `Formatter::write_str`), all of which the B-lane bundles. The ONLY `Unsize`
//! coercion to `&mut dyn Write` anywhere in that bundle is the one
//! `spec_write_fmt` performs on `&mut Sink`, so the reachable target set is
//! exactly `{Sink}` and the site's obligation is discharged against
//! `<Sink as Write>::write_str`, which is proved panic-free in this same crate.
//!
//! Before this rule the same file reported:
//!
//! ```text
//! error: an unproven panic-freedom obligation for a call to an absent callee
//!        (a std/extern function whose body is not in the lowered bundle) ...
//! error: Trust strict verification failed for `render`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! `Tag`/`Display` deliberately does NOT appear here: a `Display::fmt` verified on
//! its OWN has a caller-chosen sink and must fail, which is
//! `dyn_dispatch_reliance_open_sink_stays_closed.rs`. Mixing the two shapes into one
//! `check-pass` file would hide that distinction, which is the whole point.
//!
//! Nothing here is a totality model: `write_str` is NOT on any allowlist and NOT
//! in `total_no_panic_call_summary`. The discharge is the impl's own proof,
//! reached through a provenance argument. `dyn_dispatch_reliance_panicking_sink.rs`
//! is the same shape with a panicking impl and must still FAIL.
//!
//! ## `--crate-type lib` IS THE ASSERTION — DO NOT "FIX" THIS FILE BY CHANGING IT
//!
//! C-FLOW must work from an RLIB. That is the entire reason it exists alongside
//! C-UNIVERSAL, which refuses an rlib on the whole-program condition
//! (`dyn_dispatch_reliance_contract_rlib_stays_closed.rs` pins that refusal), and it is
//! why every leaf crate in a real workspace — all rlibs — can be served at all.
//! C-FLOW quantifies over the VALUE FLOW into one receiver, which the bundle
//! bounds on its own, so it needs no seal and no closed world.
//!
//! If this file ever starts needing an executable/staticlib crate type to pass,
//! C-FLOW has silently degenerated into C-UNIVERSAL and the rlib case is
//! unserved. Fix the rule, not the crate type.
#![no_std]
#![allow(dead_code)]

use core::fmt;

pub struct Sink {
    written: u32,
}

impl fmt::Write for Sink {
    // Provably panic-free: `wrapping_add` cannot overflow-panic and the cast is
    // a truncation, so this body has no panic-capable construct at all.
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written = self.written.wrapping_add(s.len() as u32);
        Ok(())
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
}

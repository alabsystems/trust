//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The `write_fmt` reduction must not DONATE a discharge to a `dyn` site it never
//! looked at, through the aliased callee key of a site it did.
//!
//! This is the sibling of `dyn_dispatch_reliance_key_alias_site_stays_closed.rs`
//! and the one that pins the interaction the `write_fmt` reduction CREATES. There
//! the aliased pair was provable without the reduction at all. Here the first
//! block's `S::tick` is provable ONLY through it: its body's
//! `write!(w, "x")` call names core's default `fmt::Write::write_fmt`, an absent
//! callee, so without the reduction `<S as Tick>::tick` keeps a fail-closed
//! obligation, its case split declines, and NOTHING is inserted for either block.
//!
//! With the reduction, `<S as Tick>::tick` becomes provable, its case split
//! admits — and the second block's `panic!()` target, which renders the SAME
//! `<dyn drive::Tick as drive::Tick>::tick` key (def paths omit `DefPathData`
//! disambiguators; `direct_call_def_path` disambiguates only duplicate CRATE
//! names), collects that discharge without ever passing a gate.
//!
//! MEASURED, three states, on three real compilers:
//!
//! * unpatched: `EXIT=1` — the `write_fmt` row keeps `<S as Tick>::tick` unproved;
//! * `write_fmt` reduction landed, `dyn` lane still inserting PER SITE: `EXIT=0`,
//!   probe `site=<dyn …drive::Tick…>::tick … => DISCHARGED` then `… => kept`, and
//!   the `Trust strict verification failed for … drive` error GONE. A proof of a
//!   program whose second block panics unconditionally;
//! * repaired: `EXIT=1`, probe `(2 site(s))` on both lines plus
//!   `=> kept (not every site under this callee key discharges)`.
//!
//! Both fixtures are needed. Reverting the group decision alone reopens this one
//! AND its sibling; reverting the `write_fmt` reduction alone leaves this one red
//! for an unrelated reason, which is why the sibling — provable with no reduction
//! in sight — is the load-bearing guard for the grouping itself.
//!
//! # THE ALIAS THIS FILE WAS MINTED FOR IS NOW CLOSED AT THE RENDERING SEAM
//!
//! `trust_mir_extract::safe_def_path_str` renders under
//! `with_def_path_disambiguators`, so the DONEE block's `trait Tick`/`struct S`
//! render `…drive::Tick#1` / `…drive::S#1` and its site NO LONGER SHARES the
//! donor's key. MEASURED on this tree: this file's exit code and every diagnostic
//! KIND are unchanged and the only stderr delta is the `#1` spelling — the second
//! block's `S::tick` is `panic!()`, which is its own fail-closed reason.
//!
//! COVERAGE CONSEQUENCE, stated so nobody mistakes this for a live guard: with an
//! narrowed key there is no donation to make, so this file no longer grades the
//! group decision. It stays a valid end-to-end fail-closed fixture and the
//! historical record of the cross-lane exploit; the group decision's live coverage
//! is now the residual the seam cannot reach — two impls that instantiate to one
//! `<self_ty as trait_ref>` under one parent (specialization), and a GENERIC call
//! whose key is spelled like a generic DEFINITION's path, a MEASURED still-open
//! false proof. Both are enumerated on `direct_call_def_path`. The key is
//! narrowed, NOT injective.
#![no_std]
#![allow(dead_code)]

use core::fmt::{self, Write as _};

pub fn drive() -> u32 {
    let a = {
        trait Tick {
            fn tick(&self) -> u32;
        }
        struct S;
        impl Tick for S {
            fn tick(&self) -> u32 {
                // Provable ONLY with the `write_fmt` reduction: without it this
                // body keeps a fail-closed absent-callee obligation.
                struct Sink {
                    n: u32,
                }
                impl fmt::Write for Sink {
                    fn write_str(&mut self, s: &str) -> fmt::Result {
                        self.n = self.n.wrapping_add(s.len() as u32);
                        Ok(())
                    }
                }
                let mut w = Sink { n: 0 };
                let _ = write!(w, "x");
                w.n
            }
        }
        let s = S;
        let t: &dyn Tick = &s;
        t.tick()
    };
    let b = {
        // The DONEE: a different trait whose site renders the same callee key and
        // whose target panics unconditionally.
        trait Tick {
            fn tick(&self) -> u32;
        }
        struct S;
        impl Tick for S {
            fn tick(&self) -> u32 {
                panic!()
            }
        }
        let s = S;
        let t: &dyn Tick = &s;
        t.tick()
    };
    a.wrapping_add(b)
}

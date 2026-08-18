//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The `dyn` reliance rule's discharge channel is a callee STRING, and that
//! string is MANY-TO-ONE inside one crate. Two virtual sites that share a key
//! must BOTH discharge, or neither is discharged.
//!
//! `trust_mir_extract::func_operand_name` renders `def_path_str_with_args`, and a
//! def path omits `DefPathData` disambiguators; `direct_call_def_path`
//! disambiguates only duplicate CRATE names. So the two block-scoped `trait Tick`
//! below — genuinely different traits, with genuinely different vtables and
//! genuinely different `tick` bodies — render ONE callee key:
//!
//! ```text
//! <dyn dyn_dispatch_reliance_key_alias_site_stays_closed::drive::Tick
//!     as dyn_dispatch_reliance_key_alias_site_stays_closed::drive::Tick>::tick
//! ```
//!
//! The first block's `S::tick` is provably panic-free (`wrapping_add`), so its
//! C-FLOW case split admits. The second block's `S::tick` is `panic!()`, so its
//! case split correctly DECLINES. The rule must therefore insert NEITHER: the
//! bridge discharges an absent-callee row by testing
//! `dyn_contract_total_callees.contains(callee)` against the string alone, so one
//! key inserted for the first site also discharges the second.
//!
//! MEASURED, and this is the planted violation this file exists for. Against the
//! revision that did `out.insert(site.call_key.clone())` PER SITE, this exact
//! program compiled CLEAN (`EXIT=0`) with the probe printing
//! `site=<dyn …drive::Tick as …drive::Tick>::tick … => DISCHARGED` for the first
//! block and `=> kept` for the second — the declined site discharged anyway, by a
//! string its neighbour inserted. Group-wide all-or-nothing turns that back into
//! the honest fail-closed absent-callee obligation, which is the `Trust` error
//! this fixture requires, and the probe then prints `(2 site(s))` on both lines —
//! the count is what makes the alias visible at all.
//!
//! This hole PREDATES the `write_fmt` reduction: the same program is `EXIT=0` on
//! an unpatched compiler too. `dyn_dispatch_reliance_key_alias_write_fmt_donor_stays_closed.rs`
//! is the variant that needs the reduction to donate the discharge, and only that
//! one pins the cross-lane interaction.
//!
//! # THE ALIAS THIS FILE WAS MINTED FOR IS NOW CLOSED AT THE RENDERING SEAM
//!
//! `trust_mir_extract::safe_def_path_str` renders under
//! `with_def_path_disambiguators`, so the two block-scoped `trait Tick`/`struct S`
//! below now render `…drive::Tick` / `…drive::Tick#1` and NO LONGER SHARE A KEY.
//! MEASURED on this tree: this file's exit code and every diagnostic KIND are
//! unchanged and the only stderr delta is the `#1` spelling — the second block's
//! `S::tick` is `panic!()`, which is its own fail-closed reason.
//!
//! COVERAGE CONSEQUENCE, stated so nobody mistakes this for a live guard: with an
//! narrowed key this file no longer grades the `CallKeyLedger` group decision.
//! Deleting that ledger would not turn it red. It stays a valid end-to-end
//! fail-closed fixture and the historical record of the exploit; what still needs
//! the ledger is the residual the seam cannot reach — two impls that instantiate
//! to one `<self_ty as trait_ref>` under one parent (specialization), and a
//! GENERIC call whose key is spelled like a generic DEFINITION's path, which is a
//! MEASURED, still-open false proof. Both are enumerated on
//! `direct_call_def_path`. The key is narrowed, NOT injective.
#![no_std]
#![allow(dead_code)]

pub fn drive() -> u32 {
    let a = {
        // Provably panic-free: this block's case split admits.
        trait Tick {
            fn tick(&self) -> u32;
        }
        struct S {
            n: u32,
        }
        impl Tick for S {
            fn tick(&self) -> u32 {
                self.n.wrapping_add(1)
            }
        }
        let s = S { n: 0 };
        let t: &dyn Tick = &s;
        t.tick()
    };
    let b = {
        // A DIFFERENT trait, with a DIFFERENT vtable, whose site renders the SAME
        // callee key and whose target panics unconditionally. Its call must keep
        // the absent-callee obligation — and so must its aliased neighbour above.
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

//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The `write_fmt` reduction's discharge channel is a callee STRING, and that
//! string is MANY-TO-ONE inside one crate. Two receivers that share a key must
//! BOTH pass every gate, or neither is discharged.
//!
//! `trust_mir_extract::func_operand_name` renders `def_path_str_with_args`, and a
//! def path omits `DefPathData` disambiguators; `direct_call_def_path`
//! disambiguates only duplicate CRATE names. So the two block-scoped `struct S`
//! below — genuinely different types, with genuinely different
//! `<S as fmt::Write>::write_str` bodies — render ONE callee key:
//!
//! ```text
//! <static_str_write_fmt_key_alias_site_stays_closed::render::S as core::fmt::Write>::write_fmt
//! ```
//!
//! The first `S::write_str` is provably panic-free (`wrapping_add`). The second
//! is `panic!()`. `trust_verify::static_str_write_fmt` must therefore discharge
//! NEITHER: inserting that one key would discharge the panicking call too,
//! because the bridge tests `dyn_contract_total_callees.contains(callee)` against
//! the string alone.
//!
//! MEASURED, and this is the planted violation this file exists for. Against the
//! revision that resolved its reduction-target gate with `let site = sites[0]`,
//! this exact program compiled CLEAN — `write_fmt … => DISCHARGED (reduces to
//! proved <render::S as core::fmt::Write>::write_str)`, `render` reported no
//! obligation, exit 0 — and the same source, given a `main`, panicked at runtime
//! in the second `S::write_str`. A proof of a program that panics. Per-site
//! gates turn that back into the honest fail-closed absent-callee obligation,
//! which is the `Trust` error this fixture requires.
//!
//! Ordering is not the mechanism: swapping the two blocks (so the PANICKING `S`
//! is `sites[0]`) is closed by the same per-site rule, and was measured closed
//! on the same build. Nor is `write!` the only shape — a macro that mints a
//! local sink type per expansion aliases identically.
//!
//! # THE ALIAS THIS FILE WAS MINTED FOR IS NOW CLOSED AT THE RENDERING SEAM
//!
//! `trust_mir_extract::safe_def_path_str` renders under
//! `with_def_path_disambiguators`, so the two block-scoped `struct S` below now
//! render `…render::S` / `…render::S#1` and NO LONGER SHARE A KEY. MEASURED on
//! this tree: this file's exit code and every diagnostic KIND are unchanged and
//! the only stderr delta is the `#1` spelling — the second `S::write_str` is
//! `panic!()`, which is its own fail-closed reason.
//!
//! COVERAGE CONSEQUENCE, stated so nobody mistakes this for a live guard: with a
//! narrowed key this file no longer grades the all-sites group decision.
//! Reverting that grouping would not turn it red. It stays a valid end-to-end
//! fail-closed fixture and the historical record of the exploit; what still needs
//! the grouping is the residual the seam cannot reach — two impls that instantiate
//! to one `<self_ty as trait_ref>` under one parent (specialization), and a
//! GENERIC call whose key is spelled like a generic DEFINITION's path, a
//! MEASURED still-open false proof. Both are enumerated on
//! `direct_call_def_path`. The key is narrowed, NOT injective.
#![no_std]
#![allow(dead_code)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    {
        // Provably panic-free: gate 4 passes for THIS receiver.
        struct S {
            n: u32,
        }
        impl fmt::Write for S {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                self.n = self.n.wrapping_add(s.len() as u32);
                Ok(())
            }
        }
        let mut a = S { n: 0 };
        write!(a, "x")?;
    }
    {
        // A DIFFERENT type that renders the SAME callee key, whose `write_str`
        // panics unconditionally. Its call must keep the absent-callee
        // obligation, and so must its aliased neighbour above.
        struct S;
        impl fmt::Write for S {
            fn write_str(&mut self, _s: &str) -> fmt::Result {
                panic!()
            }
        }
        let mut b = S;
        write!(b, "y")?;
    }
    Ok(())
}

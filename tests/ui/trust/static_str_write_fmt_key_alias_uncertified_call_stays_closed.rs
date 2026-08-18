//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTANT: a callee key the `write_fmt` reduction certifies must not carry its
//! discharge to a call the reduction never looked at.
//!
//! `trust_mir_extract::func_operand_name` is MANY-TO-ONE inside one crate (def
//! paths omit `DefPathData` disambiguators; `direct_call_def_path` disambiguates
//! only duplicate CRATE names), and the discharge channel the bridge reads is a
//! set of those STRINGS. So it is not enough for every certified SITE under a key
//! to pass every gate — no OTHER bundled call may render to that key either.
//!
//! Here the second `S` OVERRIDES `write_fmt`, so its call declines at gate 1 and
//! is not a site of this rule at all; `#[trust::skip]` then keeps its body out of
//! the bundle, so the call rides the fail-closed absent-callee arm. Its
//! devirtualized name is `<render::S as core::fmt::Write>::write_fmt` — the very
//! string the FIRST `S`'s certified `write!` site would discharge. Gate 0 refuses
//! that key outright:
//!
//! ```text
//! write_fmt site=<…::render::S as core::fmt::Write>::write_fmt (1 site(s))
//!     => kept (callee key ALIASES a bundled call this rule did not certify)
//! ```
//!
//! MEASURED, both states, one build apart. With gate 0 disabled the probe prints
//! `=> DISCHARGED (every site reduces to its own proved write_str)` and the
//! `Trust strict verification failed for … render` error below DISAPPEARS — the
//! skipped, `panic!()`-bodied `write_fmt` was credited with the OTHER `S`'s
//! `write_str` proof. That error's absence is what this fixture grades: the
//! `skipped` error stays either way, so the exit code alone does not witness this
//! gate.
//!
//! Note the arithmetic of the group: only ONE site is certified here, and it
//! passes every per-site gate. Per-site gates 2/3/4 are therefore NOT what closes
//! this file — gate 0 is the only thing holding it.
//!
//! # THE ALIAS THIS FILE WAS MINTED FOR IS NOW CLOSED AT THE RENDERING SEAM
//!
//! `trust_mir_extract::safe_def_path_str` renders under
//! `with_def_path_disambiguators`, so the second `struct S` renders
//! `…render::S#1` and its `write_fmt` OVERRIDE NO LONGER SHARES the first `S`'s
//! key. MEASURED on this tree: the graded `Trust strict verification failed` and
//! `Trust full verification skipped` errors are both still emitted, with identical
//! counts; the only stderr delta is the `#1` spelling. The `#[trust::skip]`
//! `panic!()` body is its own fail-closed reason.
//!
//! COVERAGE CONSEQUENCE, stated so nobody mistakes this for a live guard: gate 0
//! is no longer what holds this file. Disabling it would not make the
//! `strict verification failed` error disappear any more, because the certified
//! key no longer names the skipped call. It stays the historical record of the
//! exploit; gate 0's live coverage is now the residual the seam cannot reach —
//! two impls that instantiate to one `<self_ty as trait_ref>` under one parent
//! (specialization), and a GENERIC call whose key is spelled like a generic
//! DEFINITION's path, a MEASURED still-open false proof. Both are enumerated on
//! `direct_call_def_path`. The key is narrowed, NOT injective.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    //~^ ERROR Trust strict verification failed
    {
        // Certified site: `Arguments::from_str`-backed, and its own `write_str`
        // is provably panic-free.
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
        // A DIFFERENT `S` whose `write_fmt` OVERRIDE renders to the SAME key and
        // is never certified by this rule.
        struct S;
        impl fmt::Write for S {
            fn write_str(&mut self, _s: &str) -> fmt::Result {
                Ok(())
            }
            #[trust::skip]
            fn write_fmt(&mut self, _a: fmt::Arguments<'_>) -> fmt::Result {
                //~^ ERROR Trust full verification skipped
                panic!()
            }
        }
        let mut b = S;
        write!(b, "y")?;
    }
    Ok(())
}

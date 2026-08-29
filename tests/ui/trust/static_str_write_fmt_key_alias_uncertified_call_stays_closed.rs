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
//!
//! # THE 2026-08-24 MOVE: A NEIGHBOUR ROW DISCHARGED, THE GUARDED ROW UNTOUCHED
//!
//! `render`'s Level 0 line dropped from ERROR "2 obligation(s) were not proved"
//! to WARN with 1, and the ERROR pin minted for it on 2026-08-23 is gone. A
//! refusal getting quieter is exactly the shape of a LOST REFUSAL, so it was
//! graded on the rows and not the colour — `-Ztrust-verify-output=json`, stage2
//! built from `8d592268f3`:
//!
//! ```text
//! render — out of 2 obligation(s):
//!   vc:…__render:assertion:0                 typed_kind=Unreachable
//!     outcome=proved  solver=clean-kernel-certified
//!     (assurance=Certified, validation=KernelRechecked, axiom_closure=Empty)
//!   vc:…__render:assertion:panic-freedom:0   Assertion
//!     "[trust-expected-absent-callee-assumption] call to absent callee
//!      `<…render::S#1 as core::fmt::Write>::write_fmt` (body not in the
//!      lowered bundle) may panic"
//!     outcome=runtime_checked  solver=trust-full-verifier
//!     proof_evidence suite=trust-mc status=UNSUPPORTED
//! ```
//!
//! The row that moved is the `?`-desugar's `Unreachable`, which this file does
//! not guard. THE ROW THIS FILE GUARDS — panic-freedom for the uncertified,
//! `#[trust::skip]`-bodied `write_fmt` — is still charged, still unproved, and
//! still names the disambiguated `S#1` callee, so the uncertified call STAYS
//! CLOSED: both pinned errors still fire and the exit code is still 1. The
//! reduction machinery itself did not move at all —
//! `git diff d740d28560 HEAD -- trust_verify/static_str_write_fmt.rs
//! trust_verify/dyn_dispatch_reliance.rs` is empty across the change.
//!
//! The NOTE annotation on `render` below pins the census line for the same
//! reason the sibling `assumed_total_key_alias_write_fmt_recovery.rs` does. The
//! two `strict verification failed` / `full verification skipped` pins witness
//! that a refusal FIRED; neither would notice the guarded row ceasing to be
//! CHARGED, because a `#[trust::skip]` body keeps the second error alive on its
//! own. If that row is ever dropped the census reads `out of 1 obligation(s)`
//! and this file goes red.
//!
//! (The annotation sigil is deliberately not spelled anywhere in this prose:
//! compiletest's expectation regex matches it ANYWHERE on a line, comment or
//! not, so quoting it in a doc comment mints a phantom expectation — and the
//! follow-form does not merely fail, it PANICS the harness with "encountered
//! without preceding" before any test runs.)
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    //~^ ERROR Trust strict verification failed
    //~| NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
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

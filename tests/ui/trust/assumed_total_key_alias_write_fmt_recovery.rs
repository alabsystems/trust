//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! THE COMPLETENESS HALF of the key-narrowing repair. Read it with
//! `assumed_total_key_alias_donation_stays_closed.rs`: that file pins that a
//! neighbour's audit no longer discharges this call, and this one pins that
//! closing the alias did not COST a sound discharge. A repair that silently
//! loses recoveries is its own defect.
//!
//! This is the reviewer's original reproducer, verbatim. Two block-scoped
//! `struct S` in one function; the second overrides `write_fmt` under
//! `#[trust::assume_total]`. On a many-to-one key both `write!`s render
//! `<…render::S as core::fmt::Write>::write_fmt`.
//!
//! MEASURED, both states, on two real compilers built from this tree, with
//! `TRUST_DYN_RELIANCE_PROBE=1`:
//!
//! * aliased key (pristine): `EXIT=0`, but for the WRONG REASON. The
//!   `write_fmt` reduction REFUSED the first block —
//!   `write_fmt site=<…render::S as core::fmt::Write>::write_fmt (1 site(s))
//!   => kept (callee key ALIASES a bundled call this rule did not certify)` —
//!   and the first call was nevertheless discharged, by the ASSUMPTION filed for
//!   the second block. One lane refused the key and a second lane donated
//!   through it. The single assumption row named
//!   `<…render::S as core::fmt::Write>::write_fmt`, a string denoting TWO
//!   functions.
//! * narrowed key: `EXIT=0` for the RIGHT reason.
//!   `=> DISCHARGED (every site reduces to its own proved `write_str`)` — the
//!   first block's key now names only the first block's call, which that lane
//!   certified on its own evidence, and the assumption row names
//!   `<…render::S#1 as core::fmt::Write>::write_fmt`: the audited definition
//!   ALONE.
//!
//! So the exit code cannot grade this pair; the DISCHARGE SOURCE is what moved,
//! and the aliasing `CallKeyLedger` refusal that the fix removes was a pure
//! artifact of the collision. That is also why this file is `check-pass` and not
//! `check-fail`: after the repair the program verifies soundly, and pinning it
//! red would pin an over-decline.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    {
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
        struct S;
        impl fmt::Write for S {
            fn write_str(&mut self, _s: &str) -> fmt::Result {
                Ok(())
            }
            #[trust::assume_total]
            fn write_fmt(&mut self, _a: fmt::Arguments<'_>) -> fmt::Result {
                panic!()
            }
        }
        let mut b = S;
        write!(b, "y")?;
    }
    Ok(())
}

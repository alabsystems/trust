//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **FIXED 2026-09-26 — this row now passes, and it is the regression test for the repair.**
//! Filed as `docs/issues/2026-09-26-assume-total-discharges-the-whole-function-aggregate.md`.
//! The repair this file originally described (narrowing the rendered key) landed and works —
//! the assumption row names the audited definition alone — and the donation crossed anyway,
//! so THE KEY WAS NEVER THE MECHANISM. The real mechanism was the whole-function
//! panic-freedom AGGREGATE: `extern_call_description` labelled it with the audited site's
//! marker whenever no fatally-prefixed row existed, and the marker then discharged every
//! panic source the aggregate folds — including a BUNDLED callee body's own `Inst::Assert`s,
//! which raise no marker row at all. Fixed by requiring the fold to be the audited site(s)
//! ALONE (`panic_freedom_fold_is_audited_assumed_total_exclusive`), the same condition r09's
//! `gap_class` attestation already applies to this same aggregate.
//!
//! `-Ztrust-policy=certify` IS REQUIRED IN THE FLAGS ABOVE and is not decoration: under the
//! default policy the honest state is "reported rather than failed", so BOTH the donated and
//! the repaired state exit 0 and this fixture could not grade the repair at all. Measured:
//!
//! | crate | certify exit |
//! |---|---|
//! | the donee block alone | 1 |
//! | TWO donee blocks, no audit anywhere | 1 |
//! | an audit on a wholly unrelated `fn` | 1 |
//! | donee + the donor below, donor's type RENAMED `S` -> `T` | **0** |
//!
//! Renaming the donor changes nothing, so this is not key aliasing. The audit is spent
//! on the SYNTHESIZED WHOLE-FUNCTION panic-freedom row, which folds every panic source
//! in `render`; nothing requires the audit to cover every site the fold contains. The
//! donee's row is not refuted or deferred — it is absorbed. The r09 `gap_class`
//! attestation already has the missing rule in the right shape ("the fold is the one
//! attested site alone"); see the issue file.
//!
//! A `#[trust::assume_total]` audit must discharge the call it was written for
//! and NOTHING ELSE. The channel is a callee STRING, so that holds only if the
//! string DISTINGUISHES the two callees. The seam does NOT make the key
//! injective in general — it separates THIS pair, and `direct_call_def_path`
//! lists what still aliases, including one MEASURED open false proof.
//!
//! `collect_expected_absent_callees` files the attribute under
//! `trust_mir_extract::func_operand_name` of the call and the bridge spends it as
//! `ctx.assumed_total_callees.contains(callee)`. That string used to omit
//! `DefPathData` disambiguators, so the two block-scoped `struct S` below —
//! genuinely different types with genuinely different `write_char` targets —
//! rendered ONE key:
//!
//! ```text
//! <assumed_total_key_alias_donation_stays_closed::render::S as core::fmt::Write>::write_char
//! ```
//!
//! The SECOND block's `write_char` is an override the user audited. The FIRST
//! block's `write_char` call has no override at all: it targets core's DEFAULT
//! `fmt::Write::write_char` body, an absent callee, and — unlike `write_fmt` —
//! there is no reduction lane that can discharge it. So the first call's
//! panic-freedom obligation can only come from somewhere else, and on a
//! many-to-one key it came from the second block's audit.
//!
//! MEASURED, both states, on two real compilers built from this tree:
//!
//! * aliased key (pristine): `EXIT=0`, ONE obligation, reported as
//!   `[assert] runtime-checked: solver trust-assumed-total reported Proved
//!   without exact kernel/native proof authority`, and ONE assumption row naming
//!   `<…render::S as core::fmt::Write>::write_char` — a string that denotes TWO
//!   functions. The audit of block two discharged the call in block one.
//! * narrowed key (`with_def_path_disambiguators` at
//!   `trust_mir_extract::safe_def_path_str`): `EXIT=1`. The assumption row now
//!   names `<…render::S#1 as core::fmt::Write>::write_char` — only the audited
//!   definition — the first call's row becomes `compiler retained the existing
//!   assertion because the proof is not yet static`, and the honest
//!   `Trust strict verification failed for … render` error below appears.
//!
//! WHY THE KEY AND NOT A GATE: four sibling sets are filed in this same walk
//! (`expected_absent`, `abi_total_panic_free`, `type_total_std`,
//! `compiler_total`), and two of them are copied verbatim into crate-scoped
//! `Session` state (`register_abi_nonunwind_total_callee` /
//! `register_type_total_std_callee`) and spent name-keyed as an interprocedural
//! panic-freedom discharge for EVERY function in the crate. A per-bundle ledger
//! cannot contain that, which is why the repair is at the one rendering seam.
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    //~^ ERROR Trust strict verification failed
    {
        // THE DONEE. `S` does not override `write_char`, so this call targets
        // core's default body — an absent callee with no reduction lane. Its
        // fail-closed obligation must survive.
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
        a.write_char('x')?;
    }
    {
        // THE DONOR. A DIFFERENT `S` whose `write_char` OVERRIDE carries the
        // user's audit. Its own call is legitimately covered by that audit; the
        // neighbour above must not be.
        struct S;
        impl fmt::Write for S {
            fn write_str(&mut self, _s: &str) -> fmt::Result {
                Ok(())
            }
            #[trust::assume_total]
            fn write_char(&mut self, _c: char) -> fmt::Result {
                panic!()
            }
        }
        let mut b = S;
        b.write_char('y')?;
    }
    Ok(())
}

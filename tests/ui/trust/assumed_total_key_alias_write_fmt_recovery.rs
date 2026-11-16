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
//! artifact of the collision.
//!
//! STILL `check-pass` AS OF 2026-08-23, BUT IT BRIEFLY WAS NOT, AND THE ROUND
//! TRIP IS THE INTERESTING PART. Two independent fixes landed that day and
//! moved this file in opposite directions:
//!
//! * `has_runtime_fallback` stopped answering `true` for `VcKind::Unreachable`.
//!   That flag is a POSITIVE SAFETY CLAIM and it was false here: `render`'s only
//!   `unreachable` is the `otherwise` arm of the `?` desugar's discriminant
//!   switch, which rustc lowers to a bare `llvm.unreachable` with NO check
//!   emitted. So the row stopped being downgraded from `Unknown` to
//!   `RuntimeChecked` against a monitor that does not exist, and this file went
//!   RED — correctly. Its green had been resting on that claim.
//! * then the trust-ir fat-`Borrow` typing fix (`Inst::Borrow` over a fat
//!   pointer is typed at the FAT type, not `ptr`) let the `fmt` chain's module
//!   validate instead of being refused, and the obligation DISCHARGED on its
//!   own evidence. Green again, now for a reason that survives inspection.
//!
//! So the exit code here has meant three different things in one day, which is
//! exactly why this file's grading rule is the DISCHARGE SOURCE and not the
//! colour. Re-measured on the compiler carrying both fixes, with
//! `TRUST_DYN_RELIANCE_PROBE=1`:
//! `write_fmt site=<…render::S as core::fmt::Write>::write_fmt (1 site(s))
//! => DISCHARGED (every site reduces to its own proved `write_str`)` — the
//! narrowed-key state above, unchanged throughout. A future repair that costs
//! the discharge shows up as that probe line reverting to
//! `kept (callee key ALIASES …)`, never as a colour change here.
//!
//! # THE ROW EVIDENCE FOR THE 2026-08-24 GREEN — GAINED DISCHARGE, NOT DROPPED CHARGE
//!
//! A fixture that stops refusing has two causes and the colour separates
//! neither: the verifier may have gained a discharge, or it may have stopped
//! CHARGING the obligation — a silent false negative. Graded on the rows,
//! `-Ztrust-verify-output=json`, stage2 built from `8d592268f3`:
//!
//! ```text
//! render — out of 2 obligation(s):
//!   vc:…__render:assertion:0   typed_kind=Unreachable  "unreachable code reached"
//!     outcome=proved  solver=clean-kernel-certified
//!     proof_evidence suite=trust-certify backend=clean-kernel
//!       proof_id=clean-cic:v2:1fd69854476a6a49a8b998b1360a572560857722d…
//!       strength={reasoning=Constructive, assurance=Certified}
//!       grade={validation=KernelRechecked, axiom_closure=Empty, coverage=Unbounded}
//!   assumption:assumed-total-callee `<…render::S#1 …>::write_fmt`
//!     outcome=skipped  solver=trust-bridge   (disclosed, never credited)
//! ```
//!
//! BOTH rows are still charged — the census is 2, the same 2 it was while this
//! file was red. What moved is the `?`-desugar's `Unreachable` row, discharged
//! by `promote_kernel_certifiable` -> `trust_certify::certify_vc`: that lane
//! returns `Some` only when the Clean kernel re-checks a CIC term refuting the
//! obligation's violation formula, and it is monotone — it upgrades an
//! inconclusive verdict and can neither override nor mint one. The term is
//! `certify_path_disjunction_membership`'s `Or.rec`/`And.left`/`And.right`
//! resolution over the `trust_path_*` indicators, i.e. a real refutation of the
//! path-condition set reaching the `otherwise` arm, and per `docs/TCB.md`
//! `KernelCertified` is the class that earns `Certified` rather than `Trusted`.
//!
//! The 2026-08-23 flag fix is intact and is what makes that green mean
//! something: `VcKind::Unreachable` still answers `false` to
//! `has_runtime_fallback` (`crates/trust-types/src/formula/vc_kind.rs`), so this
//! row CANNOT be laundered into `RuntimeChecked` — it is Proved or it is red.
//!
//! PROVENANCE, recorded because the re-pin ran ahead of it: `07fe06430c` moved
//! this file back to `check-pass` citing the fat-pointer reborrow fix, but
//! `git log -S 'Trust (fat reborrow)' -- crates/trust-ir-bridge/src/lower.rs`
//! names exactly one commit, `8d592268f3`, which is NOT an ancestor of that
//! re-pin. On `origin/main` alone the bless preceded its own mechanism.
//!
//! THE PIN THIS FILE WAS MISSING. `check-pass` catches the row losing its PROOF
//! — that is precisely what went red on 2026-08-23. Nothing caught the row
//! losing its CHARGE, the direction that reads as success. The NOTE annotation
//! on `render` below pins the census line, so a dropped obligation now reads
//! `out of 1 obligation(s)` and fails this test instead of passing it.
//!
//! (2026-09-30: the census line counts the rows the function PUBLISHES, so the
//! `assumption:assumed-total-callee` row is "1 skipped" there, as it is in the JSON
//! above; the line used to call it "1 runtime-checked", its VC-level category.)
//!
//! (The annotation sigil is deliberately not spelled anywhere in this prose:
//! compiletest's expectation regex matches it ANYWHERE on a line, comment or
//! not, so quoting it in a doc comment mints a phantom expectation that can
//! never be found — and the follow-form does not fail, it PANICS the harness.)
#![no_std]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(trust)]

use core::fmt::{self, Write as _};

pub fn render() -> fmt::Result {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2 obligation(s)
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

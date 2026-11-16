//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ edition: 2021
//@ dont-check-compiler-stderr
#![crate_type = "lib"]
//! **The close negative twin of `json_output_contract_only_no_ice.rs`.**
//!
//! Same flags, same crate shape, same function — one token of the contract is
//! different (`result > a` where the positive file says `result <= a`), and the
//! body cannot satisfy it (`min2(0, 0) == 0`, and `0 > 0` is false). It must stay
//! REJECTED: a normal refusal, exit 1, with the strict-verification error.
//!
//! What this pins, and why it sits next to the ICE regression:
//!
//!   * The fix over there removes a teardown panic on the JSON wire. It must not
//!     — and structurally cannot — touch a verdict: `-Ztrust-verify-output=json`
//!     selects where ROWS are written, never whether an unproved obligation is
//!     enforced (`TrustOutputMode::emit_json` gates reporting only; the strict
//!     failure is an `error:` in every output mode). This file is the measured
//!     form of that sentence: the JSON wire with a human `--error-format` is a
//!     lane in which a false contract still fails the build.
//!   * Exit status discipline on that wire. There is no pass directive here, so
//!     compiletest requires exit 1 exactly: an ICE (101) fails this test just as
//!     it fails the positive one. A consumer of the wire must be able to tell
//!     "refused" (1) from "the compiler died" (101) from "proved" (0).
//!
//! This file is fix-INSENSITIVE by construction — the strict `error:` satisfies
//! `must_produce_diag` on its own — so it is the soundness control for the JSON
//! wire, not a second regression test for the ICE.
//!
//! The refusal is reported as UNPROVED coverage, not as a refutation with a
//! counterexample: the wire rows are `unknown`, not `failed`, although the
//! native-verifier detail notes say the trust-mc PDR runner refuted two of the
//! obligations and refused to emit proof evidence. MEASURED on THIS file with
//! exactly the header flags above, on stage2 `9b4c6b3ab` (the parent of the fix)
//! and on the pack `d75f13f97`: exit 1, no panic, `0 proved, 0 failed, 3 unknown`.
//! That is the honest verdict today, and this test deliberately does not pin
//! `unknown` versus `failed`: it pins the REASON the build does not go green (the
//! named function's obligations are not fully verified) and that the JSON wire
//! reported zero proved for it.
//!
//! stderr is otherwise unchecked for the same reason as in the positive file: the
//! `TRUST_JSON` function rows and the native-verifier detail notes carry absolute
//! paths and digests. The pins are RAW annotations rather than `error-pattern`
//! directives, for the reason the positive file gives — which also says why the
//! annotation sigil must not be written in this prose.

pub fn min2(a: u64, b: u64) -> u64
    ensures result > a
{
    if a < b { a } else { b }
}

//~? RAW Trust strict verification failed for `json_output_contract_only_unproved_stays_rejected::min2`: 3 obligation(s) were not fully verified
//~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"json_output_contract_only_unproved_stays_rejected","functions_analyzed":1,"functions_verified":0,"total_proved":0

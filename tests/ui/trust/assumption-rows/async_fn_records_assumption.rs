// Trust (assumption ledger, Stage 1): an async fn lowers to a coroutine, which
// the supportability classifier cannot lower yet. Under the nonfatal lame policy this must
// be a recorded, machine-readable assumption — the build continues and the
// human surface names the capability gap — never a hard abort (that is
// the crate-under-check strict lane's job) and never a silent skip.
//
// RE-PINNED 2026-08-22 for D2 (0e9090f03b), which closed a false Certified PROVE on the
// coroutine resume premise. The premise is published as an ASSUMPTION row again, not as
// the `CONTRACT [coroutine-resume-state]` row that `ca53846043` had substituted in every
// lane. MEASURED on stage2 ec4783d80 with this file's own flags — the raw row and the
// warning are pinned below; the `note:` summary is quoted here, not pinned:
//
//     Trust: ASSUMPTION [coroutine] `async_fn_records_assumption::tick::{closure#0}`:
//         coroutine resume-state executor protocol is assumed valid; supported user
//         data-safety obligations were still verified — recorded as an unverified
//         assumption (NOT proved)
//     note: Trust verification: 1 conditionally discharged (NOT proved), 2 failed,
//         0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
//     warning: Trust Level 0 safety verification incomplete for
//         `async_fn_records_assumption::tick::{closure#0}`: 3 obligation(s) were not proved
//
// The warning is the disclosure this file guards: no row for this body reports "proved",
// and the advisory lane still compiles (exit 0). Why the unproved rows must not be
// "recovered" by crediting the solver is argued, with its runtime exhibit, in the sibling
// `async_exhibit_does_not_certify.rs`; the strict arm is `refutation_not_swallowed_strict.rs`.
// (Do not spell an annotation sequence inside a comment here — compiletest parses it as a
// real expectation.)
//
// RE-MEASURED 2026-08-30 on stage1 at fb48832dc9. The guard holds: exit 0, the ASSUMPTION
// row is still published (raw pin below), and the disclosure warning still fires — but its
// count is now 1, because the two sentinel-family rows that measured FAILED on ec4783d80
// decide UNSAT under the exactly-grounded resume-state entry premise and report as
// CONDITIONALLY DISCHARGED (NOT proved): "3 conditionally discharged (NOT proved),
// 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5". Root cause:
// trust-vcgen's 2026-08-28 assert-refutation grounding family (e7a2860143 and siblings).
// Still no row reports an unconditional proof; the conditional rows carry
// `conditional-on-exported-precondition` and no proof credit.
//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
pub async fn tick(x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `async_fn_records_assumption::tick::{closure#0}`: 1 obligation(s) were not proved
    x
}
fn main() {}
//~? RAW Trust: ASSUMPTION [coroutine] `async_fn_records_assumption::tick::{closure#0}`

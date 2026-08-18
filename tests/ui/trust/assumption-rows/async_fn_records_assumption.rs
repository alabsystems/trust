// Trust (assumption ledger, Stage 1): an async fn lowers to a coroutine, which
// the supportability classifier cannot lower yet. Under the nonfatal lame policy this must
// be a recorded, machine-readable assumption — the build continues and the
// human surface names the capability gap — never a hard abort (that is
// the crate-under-check strict lane's job) and never a silent skip.
//
// RE-PINNED 2026-08-15 for upstream 983bc1a3b6 (merged here as f1182b2285), which
// REMOVED the whole-function panic-freedom subsumption as a false proof. UPSTREAM
// CAUSED THIS: that commit's own message records the stage2/ui measurement as "NOT
// MEASURED", and the file is byte-identical on both merge parents. The coroutine
// body's `assertion:panic-freedom:0` aggregate is this item's SOLE result row, so the
// subsumption's supporting conjunction was empty and its discharge was vacuous — it
// was the only authority that ever let the row report as proved (the opaque
// `panic_reachable:` formula earns no kernel cert, and the native trust-mc run leaves
// it Unsupported). Without it the row keeps its authority-less `trust-assert-refute`
// label and reports runtime-checked, i.e. NOT proved, hence the new warning.
// STRONGER-OR-EQUAL: one obligation moved proved -> not-proved; the ASSUMPTION row
// this test exists to guard is still emitted, and no verdict was downgraded. Do NOT
// "recover" it by crediting the CHC: the bundle prunes the sentinel with an entry
// `Assume(resume_state == 0)` (measured via -Ztrust-dump=native-bundle), so a native
// proof would just relaunder the executor-protocol premise this ledger records.
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
//~? RAW Trust: ASSUMPTION [coroutine]

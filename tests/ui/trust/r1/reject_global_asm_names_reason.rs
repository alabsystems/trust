//@ needs-trust-verify
//@ needs-asm-support
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
// A `global_asm!` item makes every function in the crate reachable from assembly by its
// mangled symbol — an UNCOUNTABLE caller no MIR scan can enumerate — so the crate-wide R1
// caller scan is poisoned and no verdict may be flipped. `scaled`'s div-by-zero therefore
// stays a failure even though its sole in-crate caller passes 4. Compare
// `flip_private_reachable.rs`: the same private-helper/`#[inline] pub`-caller shape with no
// asm item, which build-PASSES because R1 discharges that division from its one caller (the
// `#[inline]` is load-bearing there — it puts `scaled` in `reachable_set`, the set the
// oracle deliberately does not fold in — so it is kept here for a faithful control).
//
// This test pins BOTH halves of the scan-poison contract:
//  * the ERROR half pins the fail-closed rejection itself: if the poison ever stops
//    blocking flips (through whatever channel carries it), `scaled` flips, the error
//    disappears, and this check-fail test fails;
//  * the WARN half pins the crate-level REASON. Before it existed, the poison's cause was
//    stated NOWHERE: the pure core's coverage-gap classification is dropped unread at its
//    only compiler consumer (`try_harvest_flip` tests Total/not-Total and discards the gap
//    list — so its `ExternallyReachable` classification, false as it was for an asm item,
//    never reached anyone). The defect was that SILENCE: a user saw only an unexplained
//    "Level 0 safety verification incomplete". The crate-level warning is that missing
//    statement, and it names the offending item by span.
// The warning is GATED on a verdict actually being withheld (true here: `scaled` keeps its
// failure), so ordinary fully-proved source containing `global_asm!` compiles without it —
// a raw dcx warning cannot be suppressed by `-Awarnings`, so it must not fire on clean
// builds. It must stay a WARNING, not an error: the poison only ever KEEPS an honest
// verdict, so promoting it would fail builds that are perfectly sound.
use std::arch::global_asm;

global_asm!("");

fn scaled(x: u32, divisor: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

//~? WARN Trust R1 whole-program caller coverage is disabled for this crate

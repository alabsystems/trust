//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
// R1 REGRESSION PIN: the crate-wide caller scan must survive a `clean {}` island.
//
// An island shares `DefKind::GlobalAsm` with real `global_asm!` (the def-kind
// mapping has no island variant; its HIR kind is `ItemKind::CleanIsland`). When
// the scan poisoned on the DefKind alone, R1 was silently disabled for every
// island-carrying crate — found when the reason-channel warning fired on eleven
// e2/e6/e9 ui tests at once. An island is kernel-bound Lean: it emits no machine
// code, so it can neither call nor address-take nor symbol-name a function at
// runtime, and skipping it is sound. Real assembly still poisons.
//
// This test discriminates exactly that: `scaled` builds only because R1 flips
// its `x / divisor` obligation via caller coverage (`api` establishes
// `divisor = 4 != 0`), so on a compiler where the island still poisons the
// scan, R1 is disabled and this build FAILS.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

// The poison trigger: mere PRESENCE of an island in the crate. Its content is
// a self-contained Lean definition citing nothing.
clean {
    def island_ident (x : UInt64) : UInt64 := x
}

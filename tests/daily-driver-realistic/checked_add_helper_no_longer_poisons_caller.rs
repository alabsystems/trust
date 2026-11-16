// WAS a false refutation; CLOSED 2026-09-19. `checked_add` returns `Option` and
// cannot panic, so this program is total — yet calling `g` from `f` used to be a
// build error while `g` alone was fine.
//
// The cause was never `checked_add`. The vanilla-sysroot tolerance ledger was
// built from the ROOT body's call sites, so `core::num::<impl i32>::checked_add`
// — reached from `f` only through the bundled `g` — had NO ledger entry, and
// "a callee absent from the ledger is not tolerated" failed it closed:
//
//   [VANILLA_ROW] tolerated=false NOT-IN-LEDGER callee=`...::checked_add`
//
// The bundle walk now records its own verdicts. It took four attempts, because
// THREE mechanisms were root-scoped and are consistent only together — the
// ledger, the family panic recognisers, and the intrinsic rule. See
// reports/2026-09-19-the-fourth-attempt-widened-all-three.md.
pub fn g(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}
pub fn f(a: i32, b: i32) -> Option<i32> {
    g(a, b)
}

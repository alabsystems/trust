// FOREST-CHECK increment 1 negative: a root with a CLOSURE typeck-child body.
// `nested_bodies_within(g)` yields `_c` with def_kind == Closure (not InlineConst),
// so forest_const_walk_set returns None and warm replay is a clean MISS — byte-
// identical to a no-flag build, no ICE. Closures need upvar/capture round-tripping
// (a later increment), so increment 1 correctly excludes them (fail-safe).
//
// The closure is capture-less, bound to a local, and never returned or called, so
// no opaque return type and no `Fn::call` pick perturb mintable — the forest
// predicate is the SOLE reason for the MISS.
pub fn g() -> i32 {
    let _c = |x: i32| x + 1;
    7
}

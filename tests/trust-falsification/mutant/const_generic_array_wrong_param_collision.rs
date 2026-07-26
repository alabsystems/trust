#![crate_type = "lib"]
// Trust: piece #7a — THE M==N COLLISION (INV-1). Index `[u8; M]` under a bound on
// a DIFFERENT const-param `N`. MUST fail-closed: the guard `i < N` says NOTHING
// about `M`, so `a[i]` is OOB when M < N and M <= i < N. Under the OLD
// (width,signed)-keyed opaque-scalar scheme M and N would COLLIDE onto one symbol
// and this would FALSE-PROVE; the per-param `__trust_constparam_{index}_` keying
// gives M and N distinct symbols so this refutes.
pub fn cg_wrong_param<const M: usize, const N: usize>(a: [u8; M], i: usize) -> u8 {
    if i < N { a[i] } else { 0 }
}

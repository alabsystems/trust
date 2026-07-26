#![crate_type = "lib"]
// Trust: piece #7a — const-generic array symbolic-length model. A bound-checked
// index `if i < N { a[i] }` PROVES: the array `[u8; N]`'s modeled symbolic length
// IS the const-param `N`, so the guard `i < N` (whose `N` shares the SAME SMT
// symbol `__trust_constparam_*`) discharges the bounds obligation. Its buggy
// twins live in mutant/ (unguarded, off-by-one, wrong-param M==N collision).
pub fn cg_guarded<const N: usize>(a: [u8; N], i: usize) -> u8 {
    if i < N { a[i] } else { 0 }
}

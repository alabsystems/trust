#![crate_type = "lib"]
// MUTANT (clamp-cast STALENESS twin — the hunt-5/7/8 &mut reassignment vector): the clamp bound
// `j <= 9` is INVALIDATED by `*p = 100` (j reassigned through `p = &mut j`), so `arr[j as usize]`
// indexes 100 — OUT OF BOUNDS on a length-10 array. `build_clamp_cast_facts` must WITHHOLD the
// `(j as usize) <= 9` fact (its `is_single_static_assignment` gate kills on the `&mut j` borrow),
// leaving the access unproven; `-full` MUST refute (exit 1). If the gate leaked, the stale bound
// would FALSE-PROVE a guaranteed OOB — this fixture is the regression pin for that.
pub fn f(i: i32, arr: &[u8; 10]) -> u8 {
    let mut j = i.clamp(0, 9);
    let p = &mut j;
    *p = 100;
    arr[j as usize]
}

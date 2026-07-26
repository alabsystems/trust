#![crate_type = "lib"]
// MUTANT: the guard is widened so the assertion is violable (ms = 40).
pub fn frame_budget_assert(ms: u32) -> u32 {
    if ms <= 64 {
        assert!(ms < 32);
        ms
    } else {
        16
    }
}

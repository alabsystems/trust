#![crate_type = "lib"]
// Guarded explicit assertion: under the guard the asserted invariant holds
// by direct implication; the assert's failure path must be PROVED dead.
pub fn frame_budget_assert(ms: u32) -> u32 {
    if ms <= 16 {
        assert!(ms < 32);
        ms
    } else {
        16
    }
}

// Demonstrates the UnboundedAllocation obligation Trust now emits (#nia-oom).
//
// Background: AY's NIA solver grew an LRA tableau to 203 GB and OOM-killed the
// host because a bulk allocation was sized by an unbounded count with no proof
// it stays within budget. Proving "the solver stays under B bytes on all
// QF_NIA inputs" is undecidable (QF_NIA ⊇ Hilbert's 10th), so Trust does NOT
// attempt it. Instead it verifies the orthogonal SAFETY invariant: a bulk
// allocation is either provably bounded or fails closed. That is a property of
// the program text, not of the function computed — decidable to verify.
//
// Compile with:
//   trustc -Z trust-verify-output=both --crate-type lib alloc_budget_demo.rs
//
// Expectation:
//   * alloc_unguarded  -> UnboundedAllocation FAILS (counterexample n > 2^28)
//   * alloc_guarded    -> PROVED (dominating `if n <= 2^28` guard discharges it)
//   * alloc_const      -> no obligation (constant size is trivially bounded)

/// UNGUARDED: a bulk allocation sized by an unbounded `usize` parameter —
/// exactly AY's `Solver::ensure_num_vars(n)` pattern. Trust must emit an
/// `UnboundedAllocation` obligation that FAILS: nothing bounds `n`.
pub fn alloc_unguarded(n: usize) -> Vec<u8> {
    Vec::with_capacity(n)
}

/// GUARDED (the stable superior solution): the same allocation behind a
/// dominating budget check. Trust emits the obligation and PROVES it — the
/// `n <= 2^28` guard makes `n > 2^28` unsatisfiable on the allocating path.
/// This is what AY's fixed, budget-checked allocation path looks like to the
/// verifier: it fails closed (returns early) instead of allocating past budget.
pub fn alloc_guarded(n: usize) -> Vec<u8> {
    if n <= 268435456 {
        Vec::with_capacity(n)
    } else {
        Vec::new()
    }
}

/// CONSTANT: a fixed, trivially-bounded size — Trust emits no obligation at all.
pub fn alloc_const() -> Vec<u8> {
    Vec::with_capacity(1024)
}

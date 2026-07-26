#![crate_type = "lib"]
// SOUNDNESS mutant (#nia-oom, hunt-15 Class A shape). The over-budget bulk
// allocation from mutant/unbounded_alloc_const_oom.rs, in the exact tuple shape
// the `sr_vec_from_elem_*` fuzzer families use: alongside a provable arithmetic
// op (`a as u32 + 1` — a defined cast, then a widened add that cannot overflow).
//
// The sibling is the whole point. trust-mc's native lane translates the WHOLE
// FUNCTION into one Horn rule set whose `error` relation collects the panic
// edges — overflow, div-by-zero, bounds, bare traps. The allocation-budget
// violation `count >= CEILING` is NOT a panic edge, so it is absent from those
// rules. With the arithmetic sibling present the rule set is non-trivial and
// solves SAFE, and a lane that credits every obligation of the function from
// that one solve reports the allocation `Proved` — a proof of a proposition the
// solver was never asked. That is how the fuzzer families first reported FULLY
// PROVED for a function that panics "capacity overflow" at runtime.
//
// MUST refute (exit 1). The count folds to the ground constant `1 << 28`, so
// `alloc_over_ceiling_forced` flags the violation atom as forced-true on every
// reaching execution and `escalate_refuted_l0_safety_counterexamples` hard-errors
// regardless of any backend verdict.
//
// Pairs with mutant/unbounded_alloc_const_oom.rs (same constant allocation, no
// sibling) and mutant/bounded_alloc.rs (the symbolic-count form that needs real
// solver refutation rather than the forced-constant fast path).
pub fn alloc_beside_provable_arithmetic(a: u8) -> (u32, Vec<u8>) {
    (a as u32 + 1, vec![0u8; 1 << 28])
}

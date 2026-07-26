#![crate_type = "lib"]
// UnboundedAllocation (#nia-oom): a guarded BULK heap allocation. The
// `Vec::with_capacity(n)` element count is bounded by the dominating guard
// `n <= 1024`, so the OOM-safety obligation `count >= CEILING` is UNSAT under the
// guard and Trust discharges it STATICALLY (rustc proves NOTHING about allocation
// size — this is strictly superior). Guards the maintainer's #nia-oom VC kind
// (origin 30f4271ad8 / 90c79e4fd8), which converts an unbounded allocation (the
// real 203 GB OOM that killed the host) into a mechanically-flagged obligation.
// Pairs with mutant/bounded_alloc.rs (the bound guard removed).
pub fn bounded_alloc(n: usize) -> Vec<u8> {
    if n <= 1024 {
        Vec::with_capacity(n)
    } else {
        Vec::new()
    }
}

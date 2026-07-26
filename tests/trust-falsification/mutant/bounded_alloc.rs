#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard of proved/bounded_alloc.rs: the bound guard
// `if n <= 1024` is removed, so `Vec::with_capacity(n)` allocates an UNTRUSTED,
// unbounded element count `n` straight from the parameter. The OOM-safety
// obligation `n >= CEILING` is now SAT (no guard rules it out), so it cannot be
// discharged and the verifier MUST fail closed (`UnboundedAllocation` /
// `[unknown] FAILED`, exit 1). This is the exact unbounded-growth shape (#nia-oom)
// that OOM-killed the host at 203 GB — it must never be waved through.
pub fn bounded_alloc(n: usize) -> Vec<u8> {
    Vec::with_capacity(n)
}

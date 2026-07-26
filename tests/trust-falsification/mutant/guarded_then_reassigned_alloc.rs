#![crate_type = "lib"]
// SOUNDNESS mutant (#nia-oom, hunt-8 path-guard class). The dominating bound
// guard `n <= 1024` is REAL, but the TRUE branch REASSIGNS `n` to `1 << 30`
// (1 GiB) before `Vec::with_capacity(n)`. The guard is therefore STALE at the
// allocation: it constrains the pre-reassignment value, not the count that is
// actually allocated.
//
// trust-vcgen previously threaded the stale `n <= 1024` onto the allocation VC,
// where it CONTRADICTED the live `n == 1 << 30`, made the violation formula
// UNSAT, and so vacuously PROVED a ~1 GiB allocation safe — a false-PROVE that
// crossed even the kernel-certified `-full` lane. The path-guard kill
// (`v2_build_path_guard_map`) drops a dominating guard once its local is
// reassigned, so the OOM-safety obligation `count >= CEILING` is now SAT and
// Trust MUST fail closed (`UnboundedAllocation`, exit 1).
//
// Pairs with proved/bounded_alloc.rs — the SAME guard with NO reassignment,
// which still proves green: the kill must fire here without over-firing there.
pub fn grow_after_guard(mut n: usize) -> Vec<u8> {
    if n <= 1024 {
        n = 1 << 30;
        return Vec::with_capacity(n);
    }
    Vec::new()
}

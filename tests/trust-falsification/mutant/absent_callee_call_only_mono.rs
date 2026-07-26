#![crate_type = "lib"]
// Trust R3 prerequisite P0 (probe T6): a MONOMORPHIC function whose ONLY panic
// surface is a call to an ABSENT callee whose body the verifier never sees. The
// bridge mints a `[trust-absent-callee-assumption]` may-panic row for the call
// and the counted whole-function carrier (`f: all assertions hold`); before the
// counted-carrier fix the only PUBLIC obligation (the default trust-mc
// admission) direct-proved under ObligationBackwardSlice, the transport solve
// never ran, and this compiled CLEAN (rc=0) under the default strict policy — a
// fail-open acceptance of a callee the verifier never saw. Must FAIL CLOSED
// (exit 1).
//
// The callee is `Vec::remove` (body absent from the lowered bundle) — chosen for
// allowlist STABILITY: it PANICS on an out-of-bounds index, so it can never be
// on the panic-free total-model, unlike the original `std::process::id`, which
// the T3 total-std-accessor batch (8fc6cdcde3) soundly allowlisted as genuinely
// panic-free — correctly retiring it as a fail-closed probe (a panic-free callee
// proved clean is not a false-accept). A genuinely-panicking absent callee keeps
// the absent-callee fail-closed lane under test regardless of allowlist growth.
pub fn mono_absent(v: &mut Vec<u32>) -> u32 {
    v.remove(10)
}

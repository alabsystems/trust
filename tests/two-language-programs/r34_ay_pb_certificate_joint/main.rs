// A JOINT Rust + Lean program, compiled by ONE `trustc` invocation.
//
// LEAN HALF, two parts. (1) `pb_certificate_algebra` is ay's REAL pseudo-Boolean
// certificate-algebra proof, `first-party/ay/proofs/PBCertificateAlgebra.lean`,
// loaded verbatim: 14 definitions and 10 theorems, every one kernel-checked by
// the Clean CIC kernel as part of THIS compilation. (2) The inline island gives
// Rust a kernel-checked `pb_max` it calls AT RUNTIME.
//
// RUST HALF: the load-bearing invariant ay's SLS scoring layer relies on and its
// `ay-pb-verified` crate documents — the shortfall of a `>=` PB constraint is
// never negative and is zero exactly when the constraint holds — written over
// the Lean `pb_max`, and CARRYING a native Trust contract.
//
// WHAT THIS ROW DOES AND DOES NOT ESTABLISH. It runs `-Ztrust-verify=off`, so
// the `ensures` clause below is PARSED and carried, not discharged: this row is
// not evidence that the compiler proves it, and reading it that way is the
// mistake the flag makes easy. What the row does establish is the half that
// needs no verifier — the Lean declarations are kernel-checked by the Clean CIC
// kernel during this same compilation whatever the verification flag says, the
// island `pb_max` is materialized into Rust, and the program COMPILES AND RUNS
// with the two halves in one file. The contract's discharge is a different
// claim, measured by the rows that run with verification ON.
clean mod pb_certificate_algebra;

clean {
    def pb_max (lhs : UInt64) (rhs : UInt64) : UInt64 := if lhs < rhs then rhs else lhs
}

/// Shortfall of `lhs >= rhs`: how far `lhs` falls below `rhs`, saturating at 0.
fn shortfall_for(lhs: u64, rhs: u64) -> u64
    ensures result == 0 || result == rhs - lhs
{
    pb_max(lhs, rhs) - lhs
}

fn main() {
    let violated = shortfall_for(3, 10); // 3 >= 10 fails by 7
    let satisfied = shortfall_for(12, 10); // 12 >= 10 holds
    if violated == 7 && satisfied == 0 {
        println!("shortfall(3>=10) = {violated}, shortfall(12>=10) = {satisfied} — rust over lean pb_max, 24 lean decls kernel-checked");
    }
}

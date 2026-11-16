// Trust kernel-checks ay's REAL pseudo-Boolean evaluator soundness model as part
// of compiling this Rust program. `ay_pb_unsat_rup.lean` is loaded verbatim from
// `first-party/clean/proofs/`: 786 lines, 97 declarations — the Clean mirror of
// AY's `eval_constraint` / `verify_all_constraints` (`evalConstraint`,
// `verifyAll`, `evalTerms`, `termActive`) and the 47 theorems about them that
// `ay-pb/tests/clean_bridge_conformance.rs` bridges to the real Rust evaluators.
// Every one of those 97 declarations must pass the Clean CIC kernel or this
// program does not compile. The Rust half prints the count the compiler will
// have reported in its own `kernel-checked` note.
clean mod ay_pb_unsat_rup;
fn main() {
    println!("ay PB evaluator model: 97 declarations kernel-checked by trustc");
}

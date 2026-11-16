//@ needs-trust-verify
//@ revisions: verifyoff verifyon
//@[verifyoff] compile-flags: -Ztrust-verify=off
//@[verifyon] compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **CROSS-LANGUAGE CYCLE, TWO HOPS OUT — the edge one lane cannot see in time.**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`,
//! `callee_reaches_a_gate_on_this_stack`; 2026-09-25.)
//!
//! Same cycle as `clean_origin_cross_language_cycle_refused.rs`, with one extra
//! Rust hop: `def twice_h` calls `fn hop` calls `fn deep` calls `twice_h`. The
//! declaration's OWN callee (`hop`) names no Clean def at all — only `deep` does.
//!
//! THIS IS THE FIXTURE THAT FORCED A TRANSITIVE GUARD. A one-hop test (does the
//! callee reference a live gate?) passes `verifyoff` by luck: the purity walk
//! recurses `hop` -> `deep` itself and the test fires at `deep` in time. At
//! `verifyon` it never gets there — demanding `optimized_mir(hop)` runs hop's
//! verification, which bundles its callees and demands `optimized_mir(twice_h)`,
//! the query already on the stack, so E0391 lands INSIDE the first demand.
//! Measured 2026-09-25: one-hop guard -> `verifyoff` refuses, `verifyon` E0391.
//!
//! So the walk must be transitive AND must not use `optimized_mir` — it reads the
//! pre-steal levels instead (`trust_clean_origin_references` over `mir_built`,
//! `trust_mir_direct_local_callees` over elaborated MIR).

fn hop(x: u64) -> u64 {
    deep(x)
}

fn deep(x: u64) -> u64 {
    if x == 0 { 0 } else { twice_h(x - 1) }
}

clean {
    def twice_h (x : UInt64) : UInt64 := hop (hop x)
}
//~^^ ERROR cannot be called from Rust
//~| NOTE CROSS-LANGUAGE CYCLE

fn main() {
    let _v = twice_h(5);
}

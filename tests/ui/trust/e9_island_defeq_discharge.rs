//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//! R4 §1 POSITIVE fixture (the composed typed-citation discharge): an
//! UNCITED ensures clause calling an island definition whose body
//! DEFINITIONALLY AGREES with the function's E6-admitted kernel body. The
//! discharge composes three live lanes — E6 admission supplies
//! `trust_import_ident_isl`, the island environment supplies `ident_isl`,
//! and the kernel's own check of the constructed `Eq.refl` term closes the
//! goal (`clean-kernel-defeq` authority). The two RED batteries
//! (`e9_island_call_citation_battery`, `e9_island_call_divergence_battery`)
//! pin the OTHER direction: diverging bodies are structurally not defeq and
//! stay failed. Together the three fixtures are the lane's contract.

clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

fn pass_through(x: u64) -> u64
    ensures result == ident_isl(x)
    ensures result == ident_isl(x)
{
    x
}

fn main() {
    let _ = pass_through(3);
}

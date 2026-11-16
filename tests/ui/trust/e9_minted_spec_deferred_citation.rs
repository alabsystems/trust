//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9-DEFERRED-SUFFIX-ENV-1 (TG15 open item 6): a MINTED Clean def cited
//! through a theorem in a later island that names `trust_import_*`.
//!
//! `decide (a = b)` is a W6 comparison shape, so the resolver gives
//! `spec_same_code` a `DefId` (the `if a = b then true else false` spelling is
//! outside every emittable shape and mints none). The resolver mints from the
//! islands before the first one that names `trust_import_`; that island is
//! checked after program admissions exist. The environment code generation
//! gates every minted def against used to re-check ALL islands in a fresh
//! session, which declares no E6 import, so it was rejected and this crate
//! stopped with "internal: refusing to emit code for Clean declaration
//! `spec_same_code` ... did not produce a usable environment". It now re-checks
//! the islands the mint checked.
//!
//! `build-pass` because code generation demands the gated body. Not vacuous:
//! `-Ztrust-verify=on` is strict, and the NOTE pins the citation's discharge.
//! The close negative twin, whose deferred theorem is false and must still be
//! rejected, is `e9_minted_spec_deferred_citation_false.rs`.

clean {
    def spec_same_code (a b : UInt8) : Bool := decide (a = b)
}

pub fn same_code(a: u8, b: u8) -> bool
    ensures result == spec_same_code(a, b) by same_code_is_exact
    //~^ NOTE citation `same_code_is_exact` kernel-discharges this postcondition statement
{
    a == b
}

clean {
    theorem same_code_is_exact (a b : UInt8) :
        trust_import_e9_minted_spec_deferred_citation__same_code a b = spec_same_code a b := rfl
}

fn main() {
    let _ = same_code(1, 2);
}

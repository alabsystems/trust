//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! CLOSE NEGATIVE TWIN of `e9_minted_spec_deferred_citation.rs`: the same
//! minted `decide` spec and the same Rust body, with a FALSE theorem in the
//! deferred island (`not` around the spec). Code generation's environment no
//! longer includes the deferred suffix (E9-DEFERRED-SUFFIX-ENV-1); this file
//! pins that the suffix is still kernel-checked after program admission, so the
//! build fails on the theorem.
//!
//! `dont-require-annotations: ERROR` tolerates only the SECONDARY citation and
//! strict-verification errors; the primary rejection is pinned below.

clean {
    def spec_same_code (a b : UInt8) : Bool := decide (a = b)
}

pub fn same_code(a: u8, b: u8) -> bool
    ensures result == spec_same_code(a, b) by same_code_is_exact
{
    a == b
}

clean {
    theorem same_code_is_exact (a b : UInt8) :
        trust_import_e9_minted_spec_deferred_citation_false__same_code a b =
          not (spec_same_code a b) := rfl
}
//~^^^^ ERROR `same_code_is_exact` did not elaborate

fn main() {
    let _ = same_code(1, 2);
}

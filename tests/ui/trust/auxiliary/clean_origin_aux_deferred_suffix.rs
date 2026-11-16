//@ no-prefer-dynamic
//@ compile-flags: -Ztrust-verify=on
#![crate_type = "rlib"]

//! E9-DEFERRED-SUFFIX-ENV-2: the exporting side. `m::pick` is minted, gated and
//! digest-exported exactly as in `clean_origin_aux.rs`; this library also has a
//! DEFERRED island suffix, a theorem naming its own E6 program admission
//! `trust_import_clean_origin_aux_deferred_suffix__same_code`. The exporter's gate
//! and digest are built over the pre-admission prefix only (E9-DEFERRED-SUFFIX-ENV-1);
//! the suffix is checked by this build's own walk and its admission never crosses
//! crates. Modelled on `e9_minted_spec_deferred_citation.rs`.

pub mod m {
    clean {
        def pick (x y : UInt64) : UInt64 := x
    }
}

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
        trust_import_clean_origin_aux_deferred_suffix__same_code a b = spec_same_code a b := rfl
}

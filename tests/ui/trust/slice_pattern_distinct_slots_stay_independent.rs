//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! Two DIFFERENT elements named by constant pattern indices stay independent: a
//! store to one keeps what is known of the other. The twin of
//! `slice_pattern_spellings_alias_refused.rs`, whose spellings name one element.

pub fn other_slot(v: &mut [u8]) -> u8 {
    if let [a, b, ..] = v {
        if *a < 5 {
            *b = 250;
            return *a + 250;
        }
    }
    0
}

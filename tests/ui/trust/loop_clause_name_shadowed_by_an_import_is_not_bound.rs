//@ revisions: glob_block glob_param extern_block same_name_merged
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[same_name_merged] compile-flags: -Zmir-opt-level=2 -Cdebuginfo=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Review round 40 (2026-10-02), each PROVED and kernel-certified before: a glob
//! `use m::*` in a block (or in the function's top block, over a parameter) and an
//! `extern { static lim: u8; }` block shadow `lim` but carry no single ident, so the
//! visible-binding collectors never saw them and `invariant lim <= 127` bound the
//! outer `let`/parameter while the `lim` in scope is 200. Such an item now leaves no
//! name bindable at the loop. `same_name_merged`: DestinationPropagation merged two
//! `lim` bindings onto one mutated local (`debug lim => _2` twice), which the
//! distinct-name alias guard did not count.
#![allow(non_upper_case_globals, unused_variables, unused_imports, unused_assignments)]

#[cfg(any(glob_block, glob_param))]
pub mod m {
    pub const lim: u8 = 200;
}

#[cfg(glob_block)]
pub fn f(a: u8) -> u8 {
    let lim: u8 = a / 2;
    let mut i: u8 = 0;
    {
        use crate::m::*;
        while i < 3
            invariant lim <= 127
        {
            i += 1;
        }
    }
    i
}

#[cfg(glob_param)]
pub fn f(lim: u8) -> u8
    requires lim <= 100
{
    use crate::m::*;
    let mut i: u8 = 0;
    while i < 3
        invariant lim <= 127
    {
        i += 1;
    }
    i
}

#[cfg(extern_block)]
#[no_mangle]
pub static TRUST_LIM_REAL: u8 = 200;

#[cfg(extern_block)]
pub fn f(a: u8) -> u8 {
    let lim: u8 = a / 2;
    let mut i: u8 = 0;
    {
        extern "C" {
            #[link_name = "TRUST_LIM_REAL"]
            static lim: u8;
        }
        while i < 3
            invariant lim <= 127
        {
            i += 1;
        }
    }
    i
}

#[cfg(same_name_merged)]
pub fn f(a: u8) -> u8 {
    let lim: u8 = a / 2;
    let r: u8 = {
        let mut lim: u8 = lim;
        lim |= 128;
        lim ^ 1
    };
    let mut i: u8 = 0;
    while i < 3
        invariant lim >= 128
    {
        i += 1;
    }
    r ^ i
}

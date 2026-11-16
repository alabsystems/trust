//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `uninhabited_argument_function_is_uncallable.rs`: only a BY-VALUE
//! uninhabited argument makes a function uncallable. A reference to an uninhabited
//! type is itself an ordinary (inhabited) type, and an `unreachable_unchecked` body is
//! reachable UB, so both keep the fail-closed `UnreachableStart` refusal.
use std::convert::Infallible;

pub fn by_ref(x: &Infallible) -> u8 { //~ ERROR full verification skipped
    match *x {}
}

pub fn ub() -> u8 { //~ ERROR verification
    unsafe { core::hint::unreachable_unchecked() }
}

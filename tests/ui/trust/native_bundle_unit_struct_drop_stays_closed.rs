//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ rustc-env:TRUST_INFERRED_RETURN_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW TRUST_INFERRED_RETURN: native_bundle_unit_struct_drop_stays_closed::take declined: dataless parameter is used
//! A zero-field parameter can still run a panicking destructor. Inferring the
//! scalar identity return must not skip the original body's Drop terminator or
//! make the caller panic-free. The ordinary unit-struct positive keeps its full
//! original assertion; this is its destructor-effect negative.

pub struct Marker;

impl Drop for Marker {
    fn drop(&mut self) {
        panic!("the dataless value still has a destructor")
    }
}

#[inline(never)]
fn take(_marker: Marker, x: u64) -> u64 {
    x
}

pub fn pass(x: u64) -> u64 {
    //~^ ERROR Trust strict verification failed for `native_bundle_unit_struct_drop_stays_closed::pass`
    let result = take(Marker, x);
    if result != x {
        panic!()
    }
    result
}

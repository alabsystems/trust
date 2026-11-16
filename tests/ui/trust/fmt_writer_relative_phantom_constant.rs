//@ needs-trust-verify
//@ edition: 2021
//@ revisions: real real_named fake tuple reference
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Copt-level=0
//@[real] check-pass
//@[real_named] check-fail
//@[fake] check-fail
//@[tuple] check-fail
//@[reference] check-fail
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN

#![feature(fmt_helpers_for_derive)]

// Constant-only PhantomData origin controls. These are not type-walk exceptions.
// A non-inlined local call keeps each constant as a real MIR call operand.
//[real]~? RAW exact PhantomData ZeroSized constant in `<Probe as std::fmt::Debug>::fmt` at bb0
//[real_named,fake,tuple,reference]~? RAW dyn-bearing constant in `<Probe as std::fmt::Debug>::fmt` at bb0
//[real_named,fake,tuple,reference]~? RAW C-FLOW declined: trait std::fmt::Debug poisoned
use std::fmt;

#[cfg(any(real, real_named))]
type Marker = std::marker::PhantomData<&'static dyn fmt::Debug>;
#[cfg(real_named)]
const MARKER: Marker = std::marker::PhantomData;

#[cfg(fake)]
struct PhantomData<T: ?Sized>(std::marker::PhantomData<T>);
#[cfg(fake)]
type Marker = PhantomData<&'static dyn fmt::Debug>;
#[cfg(fake)]
const MARKER: Marker = PhantomData(std::marker::PhantomData);

#[cfg(tuple)]
type Marker = (std::marker::PhantomData<&'static dyn fmt::Debug>, &'static dyn fmt::Debug);
#[cfg(tuple)]
const MARKER: Marker = (std::marker::PhantomData, &17u32);

#[cfg(reference)]
type Marker = &'static std::marker::PhantomData<&'static dyn fmt::Debug>;
#[cfg(reference)]
const MARKER: Marker = &std::marker::PhantomData;

#[inline(never)]
fn retain_marker(_: Marker) {}

pub struct Probe;
impl fmt::Debug for Probe {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(real)]
        retain_marker(std::marker::PhantomData::<&'static dyn fmt::Debug>);
        #[cfg(not(real))]
        retain_marker(MARKER);
        formatter.debug_struct_field1_finish("Probe value", &1u32)
    }
}

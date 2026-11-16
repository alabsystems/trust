//@ needs-trust-verify
//@ edition: 2021
//@ revisions: safe authored_unsafe unknown_parameter
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Copt-level=0
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//[safe]~? RAW nested formatter site=<dyn core::fmt::Debug as core::fmt::Debug>::fmt => ADMITTED (writer-relative)
//[authored_unsafe,unknown_parameter]~? RAW nested formatter site=<dyn core::fmt::Debug as core::fmt::Debug>::fmt => refused
//[unknown_parameter]~? RAW poison from a ROOT PARAMETER (the caller chose this vtable): std::fmt::Debug
// This direct-call shape retains an independent full-verification refusal.
// The RAW probes isolate the nested target-set admission decision itself.
#![allow(unused_unsafe)]
#![feature(fmt_helpers_for_derive)]
use std::fmt;
#[cfg(not(unknown_parameter))]
pub struct Probe;
#[cfg(unknown_parameter)]
pub struct Probe<'a>(pub &'a dyn fmt::Debug);
#[cfg(unknown_parameter)]
impl fmt::Debug for Probe<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct_field1_finish("Probe value", &self.0)
    }
}
#[cfg(not(unknown_parameter))]
impl fmt::Debug for Probe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let a = 1u32;
        let value: &dyn fmt::Debug = &a;
        let forwarded: &dyn fmt::Debug = &value;
        #[cfg(authored_unsafe)]
        unsafe { let _ = 0u32; }
        fmt::Debug::fmt(forwarded, f)
    }
}

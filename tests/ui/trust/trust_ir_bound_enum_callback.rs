//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: internal compiler error

// A callback's bound lifetime reaches the faithful enum-field reader through
// the trait-object signature. It must not reach a Sized query as a free bound
// variable. This is required even when the callback is never called.
#![allow(dead_code)]

pub enum Payload<'a> {
    Empty,
    Slice(&'a [&'a ()]),
}

pub fn invoke(value: &Payload<'_>, callback: &dyn Fn(&Payload<'_>)) {
    callback(value);
}

pub fn signature_only(value: &Payload<'_>, callback: &dyn Fn(&Payload<'_>)) {
    let _ = (value, callback);
}

// Concrete-lifetime and non-enum signatures retain their existing behavior.
pub enum StaticPayload {
    Empty,
    Slice(&'static [&'static ()]),
}

pub fn static_lifetime(value: &StaticPayload, callback: &dyn Fn(&StaticPayload)) {
    callback(value);
}

pub fn slice(value: &[&()], callback: &dyn Fn(&[&()])) {
    callback(value);
}

// A generic pointee still lacks a concrete physical layout. Compilation must
// not turn that uncertainty into either an admission or a compiler panic.
pub fn generic<T: ?Sized>(callback: &dyn Fn(&Option<&T>)) {
    let _ = callback;
}

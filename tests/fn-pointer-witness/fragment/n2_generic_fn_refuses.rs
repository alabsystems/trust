//@ fn-ptr-witness: refuses
//! BOUNDARY CONTROL.
pub fn call<F: Fn()>(f: F) { f() }

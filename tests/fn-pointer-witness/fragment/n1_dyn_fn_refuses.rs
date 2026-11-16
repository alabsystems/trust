//@ fn-ptr-witness: refuses
//! BOUNDARY CONTROL. One step away and the verifier does mint an obligation.
pub fn call(f: &dyn Fn()) { f() }

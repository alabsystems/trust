//@ slice-facts: verifies
//! CONTROL. An explicit emptiness guard discharges an index — outside a loop.
pub fn f(w: &[u32]) -> u32 { if !w.is_empty() { w[0] } else { 0 } }

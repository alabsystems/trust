//@ slice-facts: verifies
//! CONTROL — the binding is not enough either. The identical `let w = v[0];`
//! plus guard, with no loop around it. Verifies.
//!
//! h1..h4 together are the characterisation: ASSIGNED-IN-A-LOOP is the
//! discriminator. Neither the loop alone (h3) nor the binding alone (h4) does it.
pub fn f(v: &[&[u32]]) -> u32 {
    if v.is_empty() { return 0 }
    let w = v[0];
    if !w.is_empty() { w[0] } else { 0 }
}

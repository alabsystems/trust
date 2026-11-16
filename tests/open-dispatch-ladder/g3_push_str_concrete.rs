//@ trust-ladder: verifies
//! CONTROL for g2 — the same mutation with no trait in the way.
pub fn f(buf: &mut String) { buf.push_str("S"); }

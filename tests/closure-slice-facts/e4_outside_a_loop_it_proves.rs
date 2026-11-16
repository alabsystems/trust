//@ slice-facts: verifies
//! THE CONTROL THAT MAKES THE ABOVE A LOOP DEFECT. The same constructor, the
//! same two indices, no loop — and it VERIFIES. So the yield fact exists, is
//! correct, and does reach a bounds check; something about the loop is where the
//! connection is lost.
pub fn f(v: &[u32]) -> bool { if let Some(w) = v.windows(2).next() { w[0] <= w[1] } else { true } }

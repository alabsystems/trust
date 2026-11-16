//@ slice-facts-witness: _1*.0__slice_len
//@ slice-facts: refuses
//! The other closure shape, and strictly harder than c1. Its counterexample is
//! `i = 0` with `_1*.0__slice_len = 0` — a length-0 captured slice indexed at 0,
//! which `(0..v.len())` makes unreachable. So it needs BOTH the Range's own
//! limit on `i` AND the relation `limit == v.len()` to a CAPTURED value, where
//! c1 needs only a postcondition on the closure's own parameter.
pub fn f(v: &[u32]) -> bool { (0..v.len()).all(|i| v[i] > 0) }

//! A GENUINE bounded collect with a USER element type — the precision control
//! for the 2026-08-18 unrendered/unauthenticated-source refusal.
#[derive(Clone)]
pub struct Item {
    pub a: u64,
    pub b: u64,
}

#[inline(never)]
pub fn ok(v: &[Item]) -> Vec<Item> {
    v.iter().cloned().collect()
}

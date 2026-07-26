#![crate_type = "lib"]
// Trust R3 TRAP T2: a T-method result feeding an index — `it.into()` is a
// havoc'd trait-call result (unbounded), so `xs[it.into()]` on a 4-element
// array must REFUTE (runtime witness: Item = usize, value 100). A pass here
// would mean an opaque T-derived value discharged a bounds VC. Must exit 1.
pub trait Feed {
    type Item: Into<usize> + Copy;
}
pub fn r3_t_feed<S: Feed>(xs: &[u8; 4], it: S::Item) -> u8 {
    xs[it.into()]
}

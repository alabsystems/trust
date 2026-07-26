#![crate_type = "lib"]
// Trust R3 soundness guard (probe T5b, blueprint §5): a generic caller of a
// trait method WITH a default body. Before the bundling guard,
// `Instance::try_resolve` returned Ok(None) for `<T as D>::m`, the collector
// fell back to the syntactic trait-method DefId, bundled the DEFAULT body,
// and the bridge lowered a real call INTO it — proving the caller's
// panic-freedom against a body an impl may OVERRIDE with a panicking one
// (a downstream `impl D for P { fn m(&self) -> u32 { panic!() } }` +
// `r3_t_default(&P)` panics at runtime). Must FAIL CLOSED (exit 1): the
// default body may be trusted only when the instance RESOLVES to it.
pub trait D {
    fn m(&self) -> u32 {
        1
    }
}
pub fn r3_t_default<T: D>(t: &T) -> u32 {
    t.m()
}

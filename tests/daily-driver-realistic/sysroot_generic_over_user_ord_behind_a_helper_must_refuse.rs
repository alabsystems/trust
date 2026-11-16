// MUST STAY REFUTED, and this is the sharpest guard rail for the ledger-coverage
// change, because `v.sort()` on a `Vec<u32>` is exactly what that change made
// verify. The ONLY difference here is the element type.
//
// `alloc::slice::stable_sort::<U, ..>` is instantiated at a USER type whose
// `Ord::cmp` panics, so the sort dispatches into user code. `U` is not
// foundational, so the verdict is `false` — reached through a bundled helper or
// not.
pub struct U(pub u32);
impl PartialEq for U {
    fn eq(&self, o: &U) -> bool {
        self.0 == o.0
    }
}
impl Eq for U {}
impl PartialOrd for U {
    fn partial_cmp(&self, o: &U) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for U {
    fn cmp(&self, o: &U) -> std::cmp::Ordering {
        if o.0 == 7 {
            panic!("reachable user panic inside a std sort")
        }
        self.0.cmp(&o.0)
    }
}
fn inner(v: &mut Vec<U>) {
    v.sort();
}
pub fn outer(v: &mut Vec<U>) {
    inner(v)
}

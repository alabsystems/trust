#![crate_type = "lib"]
// Trust R3 soundness guard (probe T9 — mixed-case name collision): the SAME
// body calls `D::m` once CONCRETELY (q.m() resolves to the default body — Q
// does not override) and once GENERICALLY (t.m() is unresolvable). The bridge
// matches callees BY RENDERED NAME, and both call sites render the trait
// method's generic def path — so bundling the default body for the resolved
// sibling would let the UNRESOLVED site match it too and be falsely proved
// against a body an impl may override. The whole function must FAIL CLOSED
// (exit 1); the narrow completeness cost (q.m() loses its bundled proof when
// co-located with an unresolved call to the same method) is the sound
// direction.
pub trait D {
    fn m(&self) -> u32 {
        1
    }
}
pub struct Q;
impl D for Q {}
pub fn mixed<T: D>(t: &T, q: &Q) -> u32 {
    q.m() + t.m()
}

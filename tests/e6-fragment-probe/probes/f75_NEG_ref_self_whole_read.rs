//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: A WHOLE-POINTEE read. `derive(Clone)`'s `clone(&self)` extracts as
//@ probe-note: `_0 = Copy(*_1)` — projections `[Deref]` with no `Field` — which no
//@ probe-note: scalar row denotes. The view admits exactly `[Deref, Field(k)]` with `k`
//@ probe-note: a listed row, and nothing else, so the whole-struct read refuses.
//@ probe-note: It also fails V3 (the return is a struct), and that redundancy is
//@ probe-note: deliberate: `clone` is the most common `&self` method in real code, so it
//@ probe-note: is the shape most likely to be reached by accident.
clean { def id32k (x : UInt32) : UInt32 := x }
#[derive(Clone)]
pub struct PointK { pub x: u32, pub y: u32 }
impl PointK {
    pub fn copy_of(&self) -> PointK
        ensures result.x == id32k(self.x)
    { self.clone() }
}

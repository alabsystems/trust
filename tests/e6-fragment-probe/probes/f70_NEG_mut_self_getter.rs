//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: f68 with `&mut self`. Through a mutable borrow the pointee at EXIT may
//@ probe-note: differ from the pointee at entry, and the parameter view models a
//@ probe-note: function of ENTRY values only — owner ruling R1's assumption is about a
//@ probe-note: SHARED borrow and says nothing here. This is C1, the first condition of
//@ probe-note: the frozen-shared-parameter table, and the diagnostic names the three
//@ probe-note: options (take `&self`; move the read into a helper; stay solver-only).
clean { def id32m (x : UInt32) : UInt32 := x }
pub struct PointM { pub x: u32, pub y: u32 }
impl PointM {
    pub fn x_mut(&mut self) -> u32
        ensures result == id32m(self.x)
    { self.x }
}

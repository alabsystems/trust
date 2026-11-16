//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: The body passes the BORROW to a sibling method instead of reading a
//@ probe-note: scalar through it. The callee could read any field in any combination,
//@ probe-note: so the result is not a function of the listed rows — and the view cannot
//@ probe-note: learn otherwise, because it is built before any interprocedural
//@ probe-note: reasoning. V2 refuses every occurrence of the borrow that is not a
//@ probe-note: `[Deref, Field(k)]` read by copy, and a call argument is one.
//@ probe-note: The fix the diagnostic names is the honest one: read the scalar first and
//@ probe-note: pass the VALUE (`let x = self.x; helper(x)`), then contract `helper`.
clean { def id32f (x : UInt32) : UInt32 := x }
pub struct PointF { pub x: u32, pub y: u32 }
impl PointF {
    fn inner(&self) -> u32 { self.x }
    pub fn outer(&self) -> u32
        ensures result == id32f(self.x)
    { self.inner() }
}

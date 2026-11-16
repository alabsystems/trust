//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: V3: `result` must be a by-value scalar. A function RETURNING a reference
//@ probe-note: has no scalar `result` row at all — `trust_param_scalar_rows` is unedited
//@ probe-note: by this lane and a `ty::Ref` is not an `Adt`, so it contributes nothing —
//@ probe-note: and this lane deliberately mints no `*result` and no `result.<field>` row
//@ probe-note: for one. A clause naming either therefore fails closed as an unbound
//@ probe-note: variable rather than binding a post-state reading nobody wrote.
clean { def id32r (x : UInt32) : UInt32 := x }
pub struct PointR { pub x: u32, pub y: u32 }
impl PointR {
    pub fn x_ptr(&self) -> &u32
        ensures *result == id32r(self.x)
    { &self.x }
}

//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: POSITIVE, increment I2. The INDEX-MAPPING probe, and the one a leading or
//@ probe-note: trailing skip cannot make: the skipped field sits in the MIDDLE, so the
//@ probe-note: listed rows carry DECLARED indices 0 and 2 while the view's parameters are
//@ probe-note: at positions 0 and 1.
//@ probe-note: The body reads `head`, declared index 0, which must become view parameter 0
//@ probe-note: and mint `fun p0 p1 => p0`. An off-by-one anywhere in the mapping would mint
//@ probe-note: `fun p0 p1 => p1` — an equation about `tail` for a function returning
//@ probe-note: `head`. It is WELL-TYPED, so the Clean kernel would re-check it happily and
//@ probe-note: the row would read discharged while being false. What refuses that is the
//@ probe-note: view's per-row check of the declared field NAME against the extracted IR,
//@ probe-note: plus `Admission::param_names`' exact-list comparison in `elaborate_ensures`.
//@ probe-note: Direct unit measurements, in `trust_types::e6_param_view::tests`:
//@ probe-note: `a_skipped_middle_field_keeps_the_declared_index_of_its_siblings` and
//@ probe-note: `m_the_field_index_is_load_bearing_for_the_minted_equation`.
//@ probe-note: Like every view row this is `Trusted`/`Constructive`, never `Certified`.
clean { def id32mid (x : UInt32) : UInt32 := x }
pub struct Gap { pub head: u32, pub body: f64, pub tail: u32 }
impl Gap {
    pub fn head_of(&self) -> u32
        ensures result == id32mid(self.head)
    { self.head }
}

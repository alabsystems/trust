//@ probe-shape: Projection
//@ probe-expect: defeq-rejected
//@ probe-note: NEGATIVE, and the DEFEQ half rather than the elaboration half — which is
//@ probe-note: why it is worth more than the refusals around it. MEASURED.
//@ probe-note: The view IS built and the import IS minted (`fun p0 p1 => p0`; the body
//@ probe-note: returns `self.x`), the clause elaborates, and the kernel then refuses:
//@ probe-note: the clause says `self.y` and the defining equation says `self.x`. So the
//@ probe-note: view's two binders are DISTINGUISHED all the way to the kernel, and a
//@ probe-note: scalarization that mixed them up — the one defect that keeps the goal
//@ probe-note: well-typed, so `reject_untyped_goal` cannot see it — is caught here.
//@ probe-note: The unit-level control for the same class is
//@ probe-note: `trust_types::e6_param_view::tests::m_the_field_index_is_load_bearing_for_the_minted_equation`.
clean { def id32w (x : UInt32) : UInt32 := x }
pub struct PointW { pub x: u32, pub y: u32 }
impl PointW {
    pub fn x_ref(&self) -> u32
        ensures result == id32w(self.y)
    { self.x }
}

//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: POSITIVE, increment I2. The ORDER-SENSITIVE row, and the one `f93` cannot
//@ probe-note: be: every other view probe names ONE binder in its clause, which pins WHICH
//@ probe-note: field a read became but not the ORDER the minted import is applied in.
//@ probe-note: `pickfst a b := a` is not `pickfst b a`, so this clause is a statement about
//@ probe-note: which binder is which. The goal is
//@ probe-note:   forall (self.head) (self.tail),
//@ probe-note:     <import head_ordered> self.head self.tail = pickfst self.head self.tail
//@ probe-note: and the import is `fun p0 p1 => p0`, because the body reads DECLARED field 0
//@ probe-note: across a SKIPPED middle field (`body: f64`) that contributes no binder.
//@ probe-note: WHAT IT HOLDS. Swap which view parameter that read becomes and the import is
//@ probe-note: `fun p0 p1 => p1`; the two sides are then `self.tail` and `self.head` —
//@ probe-note: well-typed, NOT defeq, so the row goes RED rather than certifying a false
//@ probe-note: equation. Fail-closed is the direction this pin exists to hold, and it is
//@ probe-note: only visible because the island definition distinguishes its arguments.
//@ probe-note: Mechanism-level twins in `trust_types::e6_param_view::tests`:
//@ probe-note: `m_the_field_index_is_load_bearing_for_the_minted_equation` and
//@ probe-note: `m_a_swapped_row_list_across_a_skipped_field_is_refused`, with
//@ probe-note: `Admission::param_names`' exact-list comparison in `elaborate_ensures`
//@ probe-note: behind both.
//@ probe-note: Like every view row this is `Trusted`/`Constructive`, never `Certified`.
clean { def pickfst (a b : UInt32) : UInt32 := a }
pub struct Ordered { pub head: u32, pub body: f64, pub tail: u32 }
impl Ordered {
    pub fn head_ordered(&self) -> u32
        ensures result == pickfst(self.head, self.tail)
    { self.head }
}

//@ probe-shape: FieldProjection
//@ probe-expect: discharged
//@ probe-note: THE CONTROL for f68, and it measures a shape with no view in it at all:
//@ probe-note: the by-value twin of the same getter over the same struct and the same
//@ probe-note: island definition. It discharged before this increment and must be
//@ probe-note: byte-unchanged by it — the parameter view is additive, and a regression
//@ probe-note: here means the clause-side row table or the mint changed for a shape
//@ probe-note: that has no borrow in it.
//@ probe-note: It is also the GOAL DIFFERENTIAL: f68's `goal_clean` must equal this
//@ probe-note: one's after replacing the `trust_import_*` constant name. The by-value
//@ probe-note: goal is already measured sound, so that equality is the strongest single
//@ probe-note: check on the view.
clean { def id32v (x : UInt32) : UInt32 := x }
pub struct PointV { pub x: u32, pub y: u32 }
pub fn x_val(c: PointV) -> u32
    ensures result == id32v(c.x)
{ c.x }

//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: A raw pointer carries NO validity and NO aliasing guarantee, so owner
//@ probe-note: ruling R1's assumption — the whole basis of the view — does not apply to
//@ probe-note: it in any form, and there is no value a clause could name. C1 refuses it
//@ probe-note: before `Freeze` is even consulted.
clean { def id32p (x : UInt32) : UInt32 := x }
pub struct PointP { pub x: u32, pub y: u32 }
pub unsafe fn x_raw(p: *const PointP) -> u32
    ensures result == id32p(0)
{ unsafe { (*p).x } }

//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1. A SCOPE CUT, recorded so it is not
//@ probe-note: mistaken for a soundness boundary.
//@ probe-note: A by-value STRUCT parameter beside a frozen shared one is refused. The
//@ probe-note: by-value half of scalarization changes `arg_count` and the local
//@ probe-note: numbering of bodies OTHER consumers read, and it changes currently-green
//@ probe-note: by-value admissions' names against the per-field mint lane. It belongs to
//@ probe-note: its own design with its own ruling, so this view admits a by-value SCALAR
//@ probe-note: beside a borrow and nothing else.
clean { def id32b (x : UInt32) : UInt32 := x }
pub struct PointB { pub x: u32, pub y: u32 }
pub struct Off { pub d: u32 }
pub fn shifted(p: &PointB, o: Off) -> u32
    ensures result == id32b(p.x)
{ p.x }

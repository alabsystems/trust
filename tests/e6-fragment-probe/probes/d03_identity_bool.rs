//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: Bool is a supported domain alongside the unsigned ints.
clean { def id_b (x : Bool) : Bool := x }
pub fn idb(x: bool) -> bool
    ensures result == id_b(x)
{ x }

//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: A borrowed parameter's clause rows are PREFIXED by its binding name
//@ probe-note: (`p.x`). A destructuring pattern binds no single name to prefix them
//@ probe-note: with, and the extracted local carries no debug name either, so there is
//@ probe-note: nothing for the view's C4 check to compare against and nothing for
//@ probe-note: `Admission::param_names` to record — the gate that catches a same-length
//@ probe-note: reordering. Refusing is the only honest option, and the diagnostic says
//@ probe-note: to name the parameter.
clean { def id32t (x : UInt32) : UInt32 := x }
pub struct PointT { pub x: u32, pub y: u32 }
pub fn x_pat(&PointT { x, .. }: &PointT) -> u32
    ensures result == id32t(x)
{ x }

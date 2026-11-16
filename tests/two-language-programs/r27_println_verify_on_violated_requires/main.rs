// r09's NEGATIVE CONTROL. Same program, one character changed: the call site
// violates `double`'s first `requires`. The row is green only if trustc REFUSES
// the crate with a `failed` precondition row for `main` — which pins that the
// print-gap tolerance r09 needs (std's `_print` panic-freedom row is
// `runtime_checked` and classed `std-print-dispatch` on the wire) cannot mask a
// violated callsite contract: the tolerance is keyed on the row's CLASS, and a
// failed precondition is a different row with a different outcome.
fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 2
{ x * 2 }
fn main() { println!("{}", double(0)); }

//@ probe-shape: none
//@ probe-expect: discharged
//@ probe-note: A bool match is not one of the frozen shapes, though it is semantically
//@ probe-note: an identity. Since E6 expansion I3′ the E6-only tree reader reads its
//@ probe-note: `switchInt` with `bool`-literal arms and normalizes it to `x`
//@ probe-note: (`Tree(Param(0))`). MEASURED 2026-09-29: `discharged` on stage 1 of
//@ probe-note: `e6/slice2` (`583de8e0bf6`), `clause-outside-fragment` on the pack `4d9a20e3d`.
clean { def ident_b (x : Bool) : Bool := x }
pub fn f(x: bool) -> bool
    ensures result == ident_b(x)
{
    match x {
        true => true,
        false => false,
    }
}

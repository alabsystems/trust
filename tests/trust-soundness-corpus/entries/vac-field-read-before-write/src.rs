// trust-soundness-corpus entry `vac-field-read-before-write` (vac). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub struct S {
    pub f: bool,
}

pub fn vac(mut s: S) -> bool
    ensures result && !result
{
    s.f = !s.f;
    s.f
}

// Twin: a true postcondition over a write of the same field.
pub fn set_true(mut s: S) -> bool
    ensures result
{
    s.f = true;
    s.f
}

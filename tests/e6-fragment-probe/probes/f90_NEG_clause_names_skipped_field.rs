//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. The OTHER close twin of I2: a clause that names a
//@ probe-note: SKIPPED field. `scale: f64` is outside the view vocabulary, so the compiler
//@ probe-note: emits one clause binder per LISTED row and `self.scale` is not among them —
//@ probe-note: it is an UNBOUND VARIABLE and the clause never elaborates.
//@ probe-note: WHAT WOULD BE THE REAL FAILURE is the silent one, which is why this probe
//@ probe-note: exists separately from `f89`: a skipped field that quietly defaulted to
//@ probe-note: zero, or that fell through to a same-named admitted ITEM (the name-capture
//@ probe-note: class closed by I0 — see `e9_signature_name_never_binds_an_admitted_item.rs`),
//@ probe-note: would certify a contract about a value nothing in the goal mentions. A
//@ probe-note: skipped field must be UNNAMEABLE, not defaulted.
//@ probe-note: Its positive sibling is `f86`: the SAME struct shape, with the clause over
//@ probe-note: the LISTED field, discharges. The pair is the differential — the struct is
//@ probe-note: admitted, the field is not.
clean { def id32sn (x : UInt32) : UInt32 := x }
pub struct Ratio2 { pub num: u32, pub scale: f64 }
impl Ratio2 {
    pub fn num_of(&self) -> u32
        ensures result == id32sn(self.scale)
    { self.num }
}

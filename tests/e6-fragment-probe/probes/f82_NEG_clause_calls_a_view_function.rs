//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red: another function's clause may not name a `&self`
//@ probe-note: getter. A view import's arity is the FLATTENED one —
//@ probe-note: `x_ref(self.x, self.y)` — while Rust reads `x_ref` as taking one borrow,
//@ probe-note: and rustc does not type-check clause text, so such a call would elaborate
//@ probe-note: against a signature no Rust caller can write.
//@ probe-note: WHICH NET HOLDS IT HERE, measured rather than assumed. `PointV2::x_ref`
//@ probe-note: carries NO contract in this file, deliberately: a probe file classifies as
//@ probe-note: `discharged` if ANY function in it discharges, so a contracted `x_ref`
//@ probe-note: would have made this row read `discharged` while saying nothing about
//@ probe-note: `other` (it did, on the first measurement). With no contract there is no
//@ probe-note: view to mint, so what refuses `other` is the pre-existing "callee is not
//@ probe-note: E6-admitted" path — NOT `Admission::self_result_only`.
//@ probe-note: THE MARK ITSELF is measured where it can be the sole net: the CITED route,
//@ probe-note: where the session mint really does put the callee's view admission in the
//@ probe-note: table the sweep reads. See `borrows_a_view` in
//@ probe-note: `tests/ui/trust/e6_param_view_refusals_say_why.rs`, whose measured error is
//@ probe-note: "`Named::a_of` is E6-admitted only through a borrow-erased PARAMETER VIEW".
//@ probe-note: Both rows must stay red; this one is the cheap ratchet, that one is the
//@ probe-note: discriminating measurement.
clean { def id32v2 (x : UInt32) : UInt32 := x }
pub struct PointV2 { pub x: u32, pub y: u32 }
impl PointV2 {
    pub fn x_ref(&self) -> u32 { self.x }
}
pub fn other(a: u32, b: u32) -> u32
    ensures result == id32v2(PointV2::x_ref(a, b))
{ a }

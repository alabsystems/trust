//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. THE CLOSE TWIN OF I2's PAYOFF (`f80`, `f86`).
//@ probe-note: With unsupported fields SKIPPED rather than refusing the pointee, the
//@ probe-note: question the increment has to answer is what happens when the body reads
//@ probe-note: one anyway. `pos: usize` is outside the view vocabulary deliberately, and
//@ probe-note: the reason is the PAIR, not `usize` alone — MEASURED: `ty_to_domain`
//@ probe-note: (clean_island.rs:3570) DOES map `PtrSizedInt { signed: false }` to
//@ probe-note: `Domain::Machine(U64)`, while `signed: true` falls to `None`. Admitting
//@ probe-note: `isize` alone would put the clause-side and mint-side flattenings at
//@ probe-note: different arities, so `e6_view_scalar` takes both or neither and the live
//@ probe-note: `usize` lane owns extending it. So the view has NO parameter holding
//@ probe-note: `self.pos` and the read
//@ probe-note: `Copy((*_1).0)` names a field that is not a listed row.
//@ probe-note: `e6_param_view`'s `read_place` admits `[Deref, Field(k)]` only for a LISTED
//@ probe-note: `k`, so the WHOLE view refuses and the function mints nothing — `max`'s own
//@ probe-note: row buys it nothing. Anything weaker would mint a defining equation over a
//@ probe-note: value the body does not compute from, which is a FALSE equation the kernel
//@ probe-note: would happily re-check.
//@ probe-note: Refused by the view BUILDER, not by the signature scan, so there is no
//@ probe-note: D-REF headline; `TRUST_E6_DEBUG=1` prints `field 0 is not a readable row of
//@ probe-note: this pointee`, and the compiler's own I2 note names `pos: usize` as skipped.
//@ probe-note: Direct unit measurement, in `trust_types::e6_param_view::tests`:
//@ probe-note: `n_a_body_that_reads_a_skipped_field_refuses_the_whole_view`.
clean { def id32sk (x : UInt32) : UInt32 := x }
pub struct Parser { pub pos: usize, pub max: u32 }
impl Parser {
    pub fn pos_as(&self) -> u32
        ensures result == id32sk(self.max)
    { self.pos as u32 }
}

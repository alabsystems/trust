//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: A call in PROPOSITION position is admitted ONLY when the callee's
//@ probe-note: admission RECORDS a `Bool` return domain — the gate is "records Bool",
//@ probe-note: never "is admitted". `ident_w` is a certified island definition, fully
//@ probe-note: admitted, and returns `BitVec 64`, so standing it alone as a proposition
//@ probe-note: is refused with the unchanged E6 fail-closed diagnostic rather than read
//@ probe-note: as `ident_w(x) = true`. This is the probe that catches a return-domain
//@ probe-note: gate widened from "is Bool" to "is present" — and note the island lane
//@ probe-note: records a domain ONLY for a literal `Bool` codomain, because the
//@ probe-note: Clean-type-to-Domain map is not injective (`BitVec 64` is the carrier of
//@ probe-note: both `i64` and `usize`).
clean { def ident_w (x : BitVec 64) : BitVec 64 := x }
pub fn idw(x: i64) -> i64
    ensures ident_w(x)
{ x }

//@ probe-shape: none
//@ probe-expect: unproved
//@ probe-note: `as` cast, isolated against f10. A cast is neither a recognized arith
//@ probe-note: method nor a Projection (which returns a parameter verbatim), so no shape
//@ probe-note: admits it. Required by `ExprMeta::loose_bvar_range`, which ends in
//@ probe-note: `as u32`. See g08.
//@ probe-note: MEASURED 2026-08-28 at trustc c4e667ca51: `unproved`, not the
//@ probe-note: `clause-outside-fragment` first predicted here. Both are refusals and
//@ probe-note: neither reaches defeq; the difference is WHERE. This clause parses, so
//@ probe-note: the refusal is the BODY failing admission, which is the sharper reading.
clean { def narrow_isl (x : UInt64) : UInt32 := x.toUInt32 }
pub fn narrow(x: u64) -> u32
    ensures result == narrow_isl(x)
{ x as u32 }

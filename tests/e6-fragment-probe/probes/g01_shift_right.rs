//@ probe-shape: none
//@ probe-expect: unproved
//@ probe-note: Right shift, isolated against f10 (wrapping_add, discharged). `arith_method`
//@ probe-note: (trust-types/src/admissible_body.rs) classifies exactly three callees --
//@ probe-note: WrappingAdd/WrappingSub/WrappingMul -- so `>>` has no Arithmetic arm at all.
//@ probe-note: Required by clean-kernel `ExprMeta::loose_bvar_range`, a body that holds a
//@ probe-note: full ten-criteria crystal scorecard. See g08.
//@ probe-note: MEASURED 2026-08-28 at trustc c4e667ca51: `unproved`, not the
//@ probe-note: `clause-outside-fragment` first predicted here. Both are refusals and
//@ probe-note: neither reaches defeq; the difference is WHERE. This clause parses, so
//@ probe-note: the refusal is the BODY failing admission, which is the sharper reading.
clean { def shr20_isl (x : UInt64) : UInt64 := x >>> 20 }
pub fn shr20(x: u64) -> u64
    ensures result == shr20_isl(x)
{ x >> 20 }

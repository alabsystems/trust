#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `arr[(a as usize) & 3]` over `[u8;4]`. A
// float→int `as` cast is SATURATING (Rust 1.45+): out-of-range clamps to MIN/MAX, NaN
// to 0 — it NEVER traps, so it carries no CastOverflow safety obligation. It previously
// emitted a fail-closed `[cast] UNKNOWN` (a float source has no integer width), blocking
// the proof. Fixed by returning None (no obligation) for a float→int cast in the cast-VC
// builder. The masked index `& 3` is in [0,3] < 4, so this fully proves (both modes).
pub fn f(a: f64, arr: &[u8; 4]) -> u8 {
    arr[(a as usize) & 3]
}

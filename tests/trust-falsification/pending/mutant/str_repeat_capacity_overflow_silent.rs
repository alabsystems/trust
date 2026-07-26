// KNOWN SILENT FALSE-ACCEPT (found 2026-07-10, 4th hunt) — str::repeat capacity
// overflow. Sibling of the iterator sum/product silent FA, same class + same fix.
//
// `"ab".repeat(usize::MAX)` computes capacity `len * n` INSIDE `str::<impl
// str>::repeat` and overflow-panics ("capacity overflow"), but the pre-fix binary
// exited 0 with ZERO obligations (no caller-visible BinaryOp). `slice`/`Vec::
// repeat` already mint a runtime-checked obligation (sound); only the `str` impl
// was missed.
//
// FIX IMPLEMENTED in crates/ (trust-vcgen `str_repeat_capacity_overflow_call`
// mints `UnsupportedMir { kind: "str-repeat-capacity-overflow" }` → Unknown →
// runtime-checked, the owner-decided demotion), unit-pinned by
// `crates/trust-vcgen/tests/str_repeat_capacity_overflow.rs`. Gated to `<impl
// str>::repeat` so slice/Vec repeat are untouched.
//
// Stays in pending/. The obligation is an UNMARKED UnsupportedMir, so per the
// current-source rc doctrine it should land runtime-checked at rc 0 (option C) —
// but this is E2E-UNVERIFIED (the available binary 84e63de6c1 predates the
// doctrine and gives rc 1 for sibling runtime-checked cases). SOUND either way
// (silent accept closed, never a false-accept); only drop-in is uncertain until a
// rebuild. E2E blocked on the 1.98/1.99 stage0.
#![crate_type = "lib"]

pub fn f(s: &str, n: usize) -> String {
    s.repeat(n)
}

pub fn trigger() -> String {
    f("ab", usize::MAX) // capacity overflow → "capacity overflow" panic
}

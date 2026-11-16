// WS7.11 (F-114): the F1 scout probe `sel`, the CondBr diamond whose then-arm
// COMPUTES before the merge. On stale stage1 `06ce3dd35` (2026-08-30) the
// proven-output gate refuted it as a MISCOMPILE. `no_std` so the object this
// crate emits holds `sel` and nothing a C `main` would have to resolve.
#![crate_name = "sel"]
#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn sel(a: u64, b: u64) -> u64 {
    if a == b { a ^ 1 } else { b }
}

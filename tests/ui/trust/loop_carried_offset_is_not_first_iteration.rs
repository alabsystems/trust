// Trust: KNOWN_HAZARDS "the 2026-09-25 offset repair proves a LOOP-CARRIED pointer's offset
// row from its first-iteration offset". `walk` steps past one-past-the-end whenever
// `n > s.len()`. The separation engine's single forward walk read `p`'s accumulated offset
// as the pre-loop `0`, so the `add`'s `[unsafe:sep:offset]` row PROVED. A pointer that is
// redefined around a back edge now takes no walk offset. `once` is the straight-line
// control: its offset row must still prove.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":23,"col_start":33,"line_end":23,"col_end":41},"outcome":"proved"
//@ forbid-output: "line_start":29,"col_start":13,"line_end":29,"col_end":21},"outcome":"failed"
//@ forbid-output: "line_start":29,"col_start":13,"line_end":29,"col_end":21},"outcome":"unknown"

pub fn walk(s: &[u8], n: usize) {
    if s.is_empty() { return; }
    let mut p = s.as_ptr();
    for _ in 0..n { p = unsafe { p.add(1) }; }
}

pub fn once(s: &[u8]) -> *const u8 {
    if s.is_empty() { return s.as_ptr(); }
    let p = s.as_ptr();
    unsafe { p.add(1) }
}

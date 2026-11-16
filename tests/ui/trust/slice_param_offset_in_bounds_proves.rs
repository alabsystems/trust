// Trust: KNOWN_HAZARDS "SOURCE REPAIR 2026-09-25 — concrete pointer-offset bounds". An
// in-bounds offset from a slice PARAMETER was refuted: `s.as_ptr().add(s.len())` (one past
// the end, which `add` permits) and the guarded `add(s.len() - 1)`. The count is defined in
// the SAME block as the `add` call (`_3 = PtrMetadata(copy _1)`), so the offset row had no
// tie to the slice's length. The separation rows now get their own block's definitions at
// the use point, and an unsigned count its `>= 0` type range. `past` (`len + 1`) must stay
// refuted.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":24,"col_start":13,"line_end":24,"col_end":36},"outcome":"failed"
//@ forbid-output: "line_start":29,"col_start":13,"line_end":29,"col_end":40},"outcome":"failed"
//@ forbid-output: "line_start":24,"col_start":13,"line_end":24,"col_end":36},"outcome":"unknown"
//@ forbid-output: "line_start":29,"col_start":13,"line_end":29,"col_end":40},"outcome":"unknown"
//@ forbid-output: "line_start":33,"col_start":13,"line_end":33,"col_end":40},"outcome":"proved"

pub fn one_past(s: &[u8]) -> *const u8 {
    unsafe { s.as_ptr().add(s.len()) }
}

pub fn last(s: &[u8]) -> *const u8 {
    if s.is_empty() { return s.as_ptr(); }
    unsafe { s.as_ptr().add(s.len() - 1) }
}

pub fn past(s: &[u8]) -> *const u8 {
    unsafe { s.as_ptr().add(s.len() + 1) }
}

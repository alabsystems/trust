// Trust: KNOWN_HAZARDS "a sub-object reference or `&raw` at offset 0 lets walk-derived
// size rows PROVE an out-of-bounds access". `read_elem` reads bytes 6..10 of a slice the
// guard only bounds to 8 bytes, and `add_from_elem` offsets to byte 10. A borrow of
// `s[6]` was given offset 0 of `s`'s allocation, so the copy-bounds row of the first and
// the offset row of the second PROVED. A sub-object borrow now takes a fresh offset.
// `read_base` is the control: the same read from the slice base must still prove.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":24,"col_start":13,"line_end":24,"col_end":68},"outcome":"proved"
//@ forbid-output: "line_start":30,"col_start":13,"line_end":30,"col_end":36},"outcome":"proved"
//@ forbid-output: "line_start":35,"col_start":13,"line_end":35,"col_end":64},"outcome":"unknown"

pub fn read_elem(s: &[u8]) -> u32 {
    if s.len() < 8 { return 0; }
    let _base = s.as_ptr();
    let r = &s[6];
    unsafe { core::ptr::read_unaligned(r as *const u8 as *const u32) }
}

pub fn add_from_elem(s: &[u8]) -> *const u8 {
    if s.len() < 8 { return s.as_ptr(); }
    let r = &s[6];
    unsafe { (r as *const u8).add(4) }
}

pub fn read_base(s: &[u8]) -> u32 {
    if s.len() < 8 { return 0; }
    unsafe { core::ptr::read_unaligned(s.as_ptr() as *const u32) }
}

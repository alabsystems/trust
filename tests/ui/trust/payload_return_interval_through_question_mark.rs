//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A local helper returning `Option<u8>` / `Result<u32, u8>` whose every `Some` /
//! `Ok` payload is bounded lends that bound to the payload its caller extracts,
//! directly or through `?`. The interval summary covered integer returns only, so
//! `h * 10 + l` was refuted with `h = 26` (sweep m21, r06b, c42). The twin
//! `_refused.rs` keeps an unbounded `Some` arm refused.
fn digit(c: u8) -> Option<u8> {
    if c <= 9 { Some(c) } else { None }
}

pub fn pair(hi: u8, lo: u8) -> Option<u8> {
    let h = digit(hi)?;
    let l = digit(lo)?;
    Some(h * 10 + l)
}

pub fn pair_match(hi: u8) -> u8 {
    match digit(hi) {
        Some(h) => h * 25,
        None => 0,
    }
}

fn dec(c: u8) -> Result<u32, u8> {
    if c >= b'0' && c <= b'9' { Ok((c - b'0') as u32) } else { Err(c) }
}

pub fn two_digits(a: u8, b: u8) -> Result<u32, u8> {
    let x = dec(a)?;
    let y = dec(b)?;
    Ok(x * 10 + y)
}

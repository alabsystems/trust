//@ revisions: open_arm mutated contracted
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `payload_return_interval_through_question_mark.rs`. `open_arm`: one
//! `Some` arm carries 200, so `h * 10` overflows. `mutated`: the return slot is
//! written through a `&mut` after its `Some` is built, so the summary must refuse.
//! `contracted`: a helper with an authored contract is used through its contract,
//! which says nothing about the payload.
#[cfg(open_arm)]
fn digit(c: u8) -> Option<u8> {
    if c <= 9 { Some(c) } else if c == 200 { Some(c) } else { None }
}

#[cfg(mutated)]
fn digit(c: u8) -> Option<u8> {
    let mut r = if c <= 9 { Some(c) } else { None };
    if let Some(p) = &mut r {
        *p = c.wrapping_mul(30);
    }
    r
}

#[cfg(contracted)]
fn digit(c: u8) -> Option<u8>
    ensures true
{
    if c <= 9 { Some(c) } else { Some(c / 2) }
}

pub fn pair(hi: u8) -> Option<u8> { //~ ERROR verification
    let h = digit(hi)?;
    Some(h * 10)
}

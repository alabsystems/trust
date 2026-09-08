//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-WVBP): the MEMORY-BACKED half of wave-WVB's whole-value binding.
//!
//! `match e { x => body }` is `let x = e; body`. wave-WVB landed the SSA half
//! and deliberately declined the case where the bound local is `&mut`-borrowed
//! somewhere, because binding it correctly means minting a slot. So the
//! hand-written `for`-loop desugaring below refused while the identical
//! `let mut iter = ..; loop { .. }` lowered clean.
//!
//! The binding-type agreement (`bind_ty == scrut_rty`) sits on the PROMOTED
//! branch only — the slot is minted AT the mapped SCRUTINEE type, so a
//! disagreement would Store at the wrong type — which leaves wave-WVB's shipped
//! SSA lane byte-identical.

pub fn match_loop_nonfor(x: u32, y: u32) -> u32 {
    let mut total = 0;
    match IntoIterator::into_iter(x..y) {
        mut iter => loop {
            match Iterator::next(&mut iter) {
                None => break,
                Some(v) => total += v,
            }
        },
    }
    total
}

fn main() {
    assert_eq!(match_loop_nonfor(0, 5), 10);
    assert_eq!(match_loop_nonfor(3, 3), 0);
}

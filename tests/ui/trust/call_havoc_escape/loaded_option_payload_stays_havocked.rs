//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! RETURN-PAYLOAD-RETAG-1 negative control (2026-10-18): the `draw_trail` body of
//! `call_returned_option_payload_keeps_its_pointee.rs`, but the `Option<&TrailCell>` is
//! LOADED FROM MEMORY (`input.cached`), not returned by a call. A reference stored in
//! memory is never retagged and may carry raw-pointer bits with write permission:
//! `drive` stores one, and `row_is_uniform` writes `usize::MAX` through a `static mut`
//! copy of the same pointer, which is defined, so `t.col + 1` overflows. The add must
//! NOT be proved (CALL-HAVOC-ESCAPE-2's havoc of the payload's pointee stays).

pub struct TrailCell {
    pub row: usize,
    pub col: usize,
}

pub struct TrailInput {
    pub cols: usize,
    pub cached: Option<&'static TrailCell>,
}

static mut CELL: TrailCell = TrailCell { row: 0, col: 0 };
static mut W: *mut TrailCell = core::ptr::null_mut();

#[inline(never)]
pub fn row_is_uniform(_input: &TrailInput, _row: usize) -> bool {
    unsafe {
        if !W.is_null() {
            (*W).col = usize::MAX;
        }
    }
    true
}

pub fn cached_trail(input: &TrailInput) -> usize {
    //~^ ERROR Trust strict verification failed for `loaded_option_payload_stays_havocked::cached_trail`
    if let Some(t) = input.cached {
        if t.col >= input.cols {
            return 0;
        }
        if row_is_uniform(input, t.row) {
            return t.col + 1;
        }
    }
    0
}

pub fn drive() -> usize {
    unsafe {
        let p = &raw mut CELL;
        W = p;
        let t: &'static TrailCell = &*(p as *const TrailCell);
        cached_trail(&TrailInput { cols: 4, cached: Some(t) })
    }
}

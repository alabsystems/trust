//@ edition: 2021
//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-UPC): a frame-pointer coroutine capturing a bare `ty::Param` is
//! ADMITTED at the stage-2b havoc, not refused as untyped. `Ty::Unit` is
//! overloaded — the fail-closed collapse AND the deliberate tag-free wave-PO
//! opaque spelling of a bare param (which already marked the body SYMBOLIC) —
//! so the guard now asks the GROUND-TRUTH rustc type, never the mapped result.

pub async fn generic<T>(t: T) -> usize {
    let _x = t;
    core::mem::size_of::<usize>()
}

fn main() {
    let _f = generic(5u32);
    let _g = generic("s");
    assert_eq!(core::mem::size_of::<usize>(), 8);
}

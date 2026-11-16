//! **Non-exportable notice, transport control — the SUPPORTED importer.**
//!
//! Links `triangle`'s symbol. It never asks for `countdownSum`'s body, so the
//! readmission chokepoint is never reached and the notice row is never
//! consulted for a verdict: this builds and runs against the pristine rlib.

extern crate wf_notice_aux;

fn main() {
    let v = wf_notice_aux::triangle(5);
    println!("triangle={v:?}");
    assert_eq!(v, Some(15), "5 + 4 + 3 + 2 + 1, by the library's emitted recursion");
}

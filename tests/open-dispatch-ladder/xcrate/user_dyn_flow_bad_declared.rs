//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libs
//@ trust-ladder-xcrate-declare: libs
//! GUARD RAIL for D4-A: one of two coerced `Self` types panics, so the case
//! split fails. Going green is a FALSE PROOF until shown otherwise.
extern crate libs;
use libs::Shape;
fn main() {
    let b = core::hint::black_box(true);
    let s: &dyn Shape = if b { &libs::Sq(3) } else { &libs::Boom };
    let _ = s.area();
}

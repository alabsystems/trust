// The Clean-origin def was minted, gated and digest-exported in a SEPARATE
// rlib; this crate re-admits it through the extern readmission chokepoint.
extern crate clean_origin_aux;
fn main() {
    let v = clean_origin_aux::m::pick(41, 7);
    assert!(v == 41);
    println!("pick(41,7) = {v}");
}

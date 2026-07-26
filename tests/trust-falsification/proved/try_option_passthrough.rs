#![crate_type = "lib"]
// PROVED (#84 completeness): `?` on `Option`. `o?` desugars to `Try::branch(o)` plus,
// on the `None` arm, `FromResidual::from_residual` — for `Option` this is the identity
// `None => None`, which runs NO `From` conversion and is TOTAL. Both calls live in
// `core`, so without the `?`-totality model the bridge would fail-close this. The
// extractor marks them total (Option from_residual never converts), so the function
// lowers and proves panic-free. The `Some(x)` payload stays unconstrained — sound, and
// here nothing depends on its value.
pub fn passthrough(o: Option<u32>) -> Option<u32> {
    let x = o?;
    Some(x)
}

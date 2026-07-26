#![crate_type = "lib"]
// MUTANT (#84 soundness boundary): a CONVERTING `?` whose error `From` conversion
// can PANIC. `r?` on `Result<u32, E1>` in a fn returning `Result<u32, E2>` desugars
// to `FromResidual::from_residual`, which runs `E2::from(E1)` — here a user impl that
// PANICS. The function is therefore NOT panic-free and MUST be refused (exit 1).
//
// This guards the `?`-totality model: the extractor only marks `from_residual` total
// when NO real `From` runs (identity, same error type). A converting `?` (E1 != E2)
// must stay fail-closed — if a future change naively modeled EVERY `from_residual` as
// total, this mutant would survive (false proof of panic-freedom).
pub struct E1;
pub struct E2;
impl From<E1> for E2 {
    fn from(_: E1) -> E2 {
        panic!("converting From may panic")
    }
}
pub fn convert_try(r: Result<u32, E1>) -> Result<u32, E2> {
    let x = r?;
    Ok(x)
}

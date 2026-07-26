#![crate_type = "lib"]
// `?` on `Result<u32, ()>` (unit Err). The `Err(())` payload is zero-size — now
// modeled as a zero-field aggregate (#46) — so the function lowers + proves.
pub fn try_result_unit(r: Result<u32, ()>) -> Result<u32, ()> {
    let x = r?;
    Ok(x)
}

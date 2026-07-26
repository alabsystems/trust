#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: assert the `?`-extracted Ok payload is 0, which CAN
// FAIL (x is an unconstrained u32). MUST be refused (exit 1). If the unit-aggregate
// change mis-modeled the value layout (e.g. x aliased to a constant), this assert
// could falsely prove — so the mutant guards that the extracted payload stays free.
pub fn try_result_unit(r: Result<u32, ()>) -> Result<u32, ()> {
    let x = r?;
    assert!(x == 0);
    Ok(x)
}

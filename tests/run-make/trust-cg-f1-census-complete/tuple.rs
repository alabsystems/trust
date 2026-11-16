#![crate_name = "census_tuple"]

#[unsafe(no_mangle)]
pub extern "C" fn pairs(x: u64) -> u64 {
    let t = (x, x ^ 1);
    t.0 | t.1
}

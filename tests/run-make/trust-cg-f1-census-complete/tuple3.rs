#![crate_name = "census_tuple3"]

#[unsafe(no_mangle)]
pub extern "C" fn pairs(x: u64) -> u64 {
    let t = (x as u8, x ^ 1, x as u8);
    t.0 as u64 | t.1 | t.2 as u64
}

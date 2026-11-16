#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = [x, 2, 3, 4]; a[0] + a[3] }

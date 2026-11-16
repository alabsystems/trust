#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = [x, 7]; let p = a.as_ptr(); unsafe { *p + *p.add(1) } }

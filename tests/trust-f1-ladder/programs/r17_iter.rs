#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { (0..x % 1000).filter(|i| i % 3 == 0).map(|i| i * 2).sum::<u64>() }

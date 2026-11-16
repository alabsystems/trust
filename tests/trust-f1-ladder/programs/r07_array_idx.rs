#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let a = [3u64, 1, 4, 1, 5, 9, 2, 6]; let i = (x % 12) as usize; a[i] + a[(i + 1) % 8] }

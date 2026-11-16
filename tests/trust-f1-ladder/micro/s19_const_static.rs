const K: u64 = 77; static S: u64 = 1234;
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { x + K + S }

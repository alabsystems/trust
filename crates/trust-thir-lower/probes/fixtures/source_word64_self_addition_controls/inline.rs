#[inline(never)]
fn double(x: u64) -> u64 { x.wrapping_add(x) }

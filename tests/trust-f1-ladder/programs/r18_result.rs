#[inline(never)] fn half(x: u64) -> Result<u64, u8> { if x % 2 == 0 { Ok(x / 2) } else { Err(1) } }
#[inline(never)] fn quarter(x: u64) -> Result<u64, u8> { let h = half(x)?; let q = half(h)?; Ok(q + 1) }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { match quarter(x) { Ok(v) => v, Err(e) => 1000 + e as u64 } }

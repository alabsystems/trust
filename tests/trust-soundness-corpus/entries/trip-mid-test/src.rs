// trust-soundness-corpus entry `trip-mid-test` (TRIP-MID-TEST-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn mid_wrap() -> u8 {
    let mut c: u8 = 0;
    let mut i: u32 = 0;
    loop {
        c += 1;
        if i >= 254 {
            break;
        }
        i += 1;
    }
    c + 1
}

// Twin: the same loop leaves c = 255 only when it runs 255 times; 253 passes leave room.
pub fn mid_ok() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..200u32 {
        c += 1;
    }
    c + 1
}

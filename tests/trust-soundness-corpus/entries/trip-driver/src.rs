// trust-soundness-corpus entry `trip-driver` (TRIP-DRIVER-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn stray_on_cycle(limit: u8) -> u8 {
    let mut r = 0..2u32;
    let mut c: u8 = 0;
    loop {
        let _ = r.next();
        c += 1;
        if c == limit {
            break;
        }
    }
    c
}

// Twin: a `for` loop that the iterator really drives.
pub fn plain_for() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..2u32 {
        c += 1;
    }
    c
}

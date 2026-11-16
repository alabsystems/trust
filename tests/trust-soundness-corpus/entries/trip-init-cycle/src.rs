// trust-soundness-corpus entry `trip-init-cycle` (TRIP-INIT-CYCLE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub fn reset_loop(limit: u8) -> u8 {
    let mut c: u8 = 0;
    let mut i: u32;
    loop {
        i = 0;
        c += 1;
        if c == limit {
            break;
        }
        i += 1;
        if i >= 10 {
            break;
        }
    }
    c
}

// Twin: a counted `for` loop: 10 adds to a u8.
pub fn counted_for() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..10u32 {
        c += 1;
    }
    c
}

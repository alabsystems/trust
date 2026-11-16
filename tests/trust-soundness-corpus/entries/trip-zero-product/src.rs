// trust-soundness-corpus entry `trip-zero-product` (TRIP-ZERO-PRODUCT-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
const WARMUP: u32 = 0;

pub fn count_after_warmup() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..WARMUP {}
    for _ in 0..300u32 {
        c += 1;
    }
    c
}

// Twin: 200 adds to a u8 never overflow.
pub fn count_200() -> u8 {
    let mut c: u8 = 0;
    for _ in 0..200u32 {
        c += 1;
    }
    c
}

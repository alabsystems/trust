// trust-soundness-corpus entry `union-sibling-write` (UNION-SIBLING-WRITE-1). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
pub union V {
    pub a: u8,
    pub b: i8,
}

pub fn u_dst_add(x: u32) -> u8 {
    let mut u = V { a: 0 };
    u.a = x as u8;
    u.b = -56;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}

// Twin: the sibling is written first and the field that is read last, and the guard
// tests the value read, so the add stays below 0xff on every input.
pub fn u_dst_add_ctl(x: u32) -> u8 {
    let mut u = V { a: 0 };
    u.b = -56;
    u.a = x as u8;
    let y = unsafe { u.a };
    if y < 0x80 { y + 0x7f } else { 0 }
}

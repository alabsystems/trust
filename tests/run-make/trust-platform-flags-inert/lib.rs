// Trust (platform protocols, plan L1a): the subject of `rmake.rs`. Plain safe code with no
// platform policy site, so every later landing of the platform pass analyses nothing here and the
// emitted bytes must stay those of a compile without the flags.

pub fn checksum(bytes: &[u8]) -> u32 {
    let mut acc: u32 = 0x811c_9dc5;
    for &b in bytes {
        acc ^= u32::from(b);
        acc = acc.wrapping_mul(0x0100_0193);
    }
    acc
}

pub fn widths(words: &[&str]) -> Vec<usize> {
    words.iter().map(|w| w.len()).collect()
}

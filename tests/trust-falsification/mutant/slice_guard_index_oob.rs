#![crate_type = "lib"]
// MUTANT / SOUNDNESS LOCK for Imp3. The guard `buf.len() < 12` only establishes
// `buf.len() >= 12`, so index 12 is OUT OF BOUNDS when `buf.len() == 12` exactly (valid
// indices are 0..=11). Imp3 must NOT over-discharge: connecting the `Rvalue::Len` guard
// proves `buf[i]` for `i < 12`, but `buf[12]` stays a real obligation. This program panics
// for a 12-byte slice, so `-full` MUST refute it (exit 1). If it ever PROVES, the guard
// linkage has become unsound.
pub fn over_read(buf: &[u8]) -> u8 {
    if buf.len() < 12 {
        return 0;
    }
    buf[12] // OOB: buf.len() may be exactly 12 (indices 0..=11 valid)
}

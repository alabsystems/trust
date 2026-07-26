#![crate_type = "lib"]
// MUTANT / SOUNDNESS LOCK for Imp5. THREE slice lengths CAN overflow `usize`:
// `3 * isize::MAX = 3*(2^63 - 1) = 2^64 + 2^63 - 3 > usize::MAX`. The `len <= isize::MAX`
// fact is SELF-LIMITING — it discharges the first add (`len + len <= 2^64 - 2`) but NOT the
// second (`(len + len) + len` can exceed `usize::MAX`), which stays a real obligation.
// `-full` MUST refute it (exit 1). If it ever PROVES, the len bound has become unsound.
pub fn add_three_lens(s: &[u8]) -> usize {
    s.len() + s.len() + s.len()
}

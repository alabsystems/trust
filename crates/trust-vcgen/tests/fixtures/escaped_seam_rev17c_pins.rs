#![allow(unconditional_panic, unused_assignments, unused_variables, unused_mut, clippy::all, dead_code, unused_unsafe)]
// rev17c: the A12 walk is VALUE-BLIND. It taints on a WRITE of the guard's name, never on a
// change of the guard's value, and a tainted region refuses the fold outright. Every function
// here is CORRECT (the oracle never panics): the index local is written between the borrow and
// the deref but holds its borrow-time value at the deref.

#[inline(never)] pub fn bb(x: usize) -> usize { std::hint::black_box(x) }

// n1: written then restored (the minimal shape)
pub fn n1_restore_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; j = k; j = 0; *r = 3; t[s[j] as usize] }
// n2: the guard is rewritten with the SAME value in a branch
pub fn n2_same_value_branch_ctl(s: &mut [u8], t: &[u8; 4], c: bool) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; if c { j = 0; } *r = 3; t[s[j] as usize] }
// n3: incremented and decremented back
pub fn n3_roundtrip_ctl(s: &mut [u8], t: &[u8; 4]) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; j += 1; j -= 1; *r = 3; t[s[j] as usize] }
// n4: a loop that never executes writes the guard
pub fn n4_zero_trip_ctl(s: &mut [u8], t: &[u8; 4]) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; let mut i = 0usize; while i < 0 { j = 1; i += 1; } *r = 3; t[s[j] as usize] }
// n5: the guard is reassigned from itself
pub fn n5_self_assign_ctl(s: &mut [u8], t: &[u8; 4]) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; let q = j; j = q; *r = 3; t[s[j] as usize] }
// n6: the BASELINE — no write of the guard at all between borrow and deref (must prove)
pub fn n6_baseline_ctl(s: &mut [u8], t: &[u8; 4]) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; *r = 3; t[s[j] as usize] }
// n7: the guard is written AFTER the deref (must prove)
pub fn n7_write_after_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; *r = 3; let x = t[s[j] as usize]; j = k; x }
// n8: the genuine bug twin of n1 — restored to a DIFFERENT value
pub fn n8_restore_wrong_bug(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; j = k; j = 1; *r = 3; t[s[j] as usize] }

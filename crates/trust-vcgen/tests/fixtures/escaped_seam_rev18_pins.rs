#![allow(unconditional_panic, unused_assignments, unused_variables, unused_mut, clippy::all, dead_code, unused_unsafe)]
// rev18: the SOUNDNESS MARGIN of round A13's constant re-establishment. Every `_bug`
// here writes the guard with a CONSTANT before the deref — the shape the new rule
// admits — but the guard's BORROW-TIME value is not that constant, so the fold must
// stay refused. `c0(g)` is what has to tell them apart from `n1_restore_ctl`.

// p1: the borrow-time value is a PARAMETER (c0 = no constant); j is then set to 0.
pub fn p1_param_guard_then_const_bug(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = k; if s.len() < 2 { return 0; } if j >= s.len() { return 0; } let r = &mut s[j]; j = 0; *r = 3; t[s[j] as usize] }
// p2: TWO different constants reach the borrow (c0 = no single constant).
pub fn p2_two_consts_before_bug(s: &mut [u8], t: &[u8; 4], c: bool) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } if c { j = 1; } let r = &mut s[j]; j = 0; *r = 3; t[s[j] as usize] }
// p3: the restore happens inside a LOOP that runs twice (correct; c0 = 0).
pub fn p3_loop_restore_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; let mut i = 0usize; while i < 2 { j = k; j = 0; i += 1; } *r = 3; t[s[j] as usize] }
// p4: restored to a constant of the right VALUE but through a copy (not Use(Constant)).
pub fn p4_restore_via_copy_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; let z = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; j = k; j = z; *r = 3; t[s[j] as usize] }
// p5: the guard of a NESTED referent restored (two guards, only one written).
pub fn p5_two_guards_one_written_ctl(s: &mut [u8], t: &[u8; 4], k: usize) -> u8 { let mut j = 0usize; let mut m = 0usize; if s.len() < 2 { return 0; } let r = &mut s[j]; m = k; *r = 3; t[s[j] as usize] }

use std::ptr::addr_of;
// GUARDED: len <= 64 — the bounds obligation should DISCHARGE.
pub fn guarded(len: usize) -> usize {
    let buf = [0u8; 64];
    if len <= 64 { let p = addr_of!(buf) as *const u8; unsafe { std::slice::from_raw_parts(p, len).len() } } else { 0 }
}
// UNGUARDED: no bound — the bounds obligation MUST still fail (control).
pub fn unguarded(len: usize) -> usize {
    let buf = [0u8; 64];
    let p = addr_of!(buf) as *const u8;
    unsafe { std::slice::from_raw_parts(p, len).len() }
}
// WRONG GUARD: len <= 128 > array size 64 — MUST still fail (soundness check).
pub fn wrong_guard(len: usize) -> usize {
    let buf = [0u8; 64];
    if len <= 128 { let p = addr_of!(buf) as *const u8; unsafe { std::slice::from_raw_parts(p, len).len() } } else { 0 }
}

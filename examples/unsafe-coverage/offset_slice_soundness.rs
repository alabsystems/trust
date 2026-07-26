use std::ptr::addr_of;
// Simpler: sum = start+len then `if sum <= 64` — def `sum == start+len` + guard.
pub fn offset_direct(start: usize, len: usize) -> usize {
    let buf = [0u8; 64];
    let sum = start + len;
    if sum <= 64 {
        let p = unsafe { (addr_of!(buf) as *const u8).add(start) };
        return unsafe { std::slice::from_raw_parts(p, len).len() };
    }
    0
}
// checked_add + match (aterm-exact shape).
pub fn offset_ok(start: usize, len: usize) -> usize {
    let buf = [0u8; 64];
    match start.checked_add(len) {
        Some(end) if end <= 64 => {
            let p = unsafe { (addr_of!(buf) as *const u8).add(start) };
            unsafe { std::slice::from_raw_parts(p, len).len() }
        }
        _ => 0,
    }
}
// WRONG guard (len<=64 ignores start) — MUST FAIL.
pub fn offset_bad(start: usize, len: usize) -> usize {
    let buf = [0u8; 64];
    if len <= 64 {
        let p = unsafe { (addr_of!(buf) as *const u8).add(start) };
        unsafe { std::slice::from_raw_parts(p, len).len() }
    } else { 0 }
}

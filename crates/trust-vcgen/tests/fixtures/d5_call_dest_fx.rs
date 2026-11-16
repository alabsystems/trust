pub fn guard(bit: u32) -> bool { bit < 64 }
pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
    if !guard(bit) { return None; }
    Some(x >> bit)
}
pub fn guard_bad(bit: u32) -> bool { bit < 65 }
pub fn unguarded_after_call(x: u64, bit: u32) -> u64 {
    let _ = guard_bad(bit);
    x >> bit
}
pub fn nz(d: u32) -> u32 { if d == 0 { 1 } else { d } }
pub fn div_nz(x: u32, d: u32) -> u32 { x / nz(d) }
pub fn one() -> u32 { 1 }
pub fn div_one_bad(x: u32) -> u32 { x / (one() - 1) }

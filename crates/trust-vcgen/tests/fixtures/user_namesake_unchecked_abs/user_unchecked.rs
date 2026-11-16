// User functions merely NAMED like core's UB-on-overflow operations; none of
// them performs any arithmetic.
#[inline(never)]
pub fn unchecked_add(a: u32, b: u32) -> u32 { a ^ b }
#[inline(never)]
pub fn unchecked_mul(a: u64, b: u64) -> u64 { a | b }
pub trait T { fn unchecked_mul(self, b: u32) -> u32; }
impl T for u32 { #[inline(never)] fn unchecked_mul(self, b: u32) -> u32 { self | b } }
pub fn x_add(a: u32, b: u32) -> u32 { unchecked_add(a, b) }
pub fn x_mul(a: u64, b: u64) -> u64 { unchecked_mul(a, b) }
pub fn y_add(a: u32, b: u32) -> u32 { if a < 10 && b < 10 { unchecked_add(a, b) } else { 0 } }
pub fn y_tmul(a: u32, b: u32) -> u32 { if a < 10 && b < 10 { T::unchecked_mul(a, b) } else { 0 } }
// Controls: core's own operations.
pub fn m_unguarded(a: u32, b: u32) -> u32 { unsafe { a.unchecked_add(b) } }
pub fn m_guarded(a: u32, b: u32) -> u32 { if a < 10 && b < 10 { unsafe { a.unchecked_add(b) } } else { 0 } }
pub fn path_unguarded(a: u64, b: u64) -> u64 { unsafe { u64::unchecked_mul(a, b) } }

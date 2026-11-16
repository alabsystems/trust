pub struct S { n: u32, m: u32 }
pub fn n_of(s: &S) -> u32 { s.n }
pub fn is_zero(s: &S) -> bool { n_of(s) == 0 }
pub fn div_when_zero(s: &S, x: u32) -> u32 { if is_zero(s) { x / s.n } else { 0 } }
pub fn div_when_nonzero(s: &S, x: u32) -> u32 { if is_zero(s) { 0 } else { x / s.n } }
pub fn div_m_when_nonzero(s: &S, x: u32) -> u32 { if is_zero(s) { 0 } else { x / s.m } }

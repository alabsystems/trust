pub struct Cfg { pub heads: usize, pub groups: usize }

// R3: the nn `num_kv_groups` shape. The early return guards the division.
pub fn guarded_fmt_divisor(c: &Cfg) -> Result<usize, String> {
    if c.groups == 0 { return Err(String::new()); }
    if !c.heads.is_multiple_of(c.groups) { return Err(format!("{}", c.groups)); }
    Ok(c.heads / c.groups)                                         // line 7
}
// Control: the format names the OTHER field (proved before the fix too).
pub fn guarded_fmt_other(c: &Cfg) -> Result<usize, String> {
    if c.groups == 0 { return Err(String::new()); }
    if !c.heads.is_multiple_of(c.groups) { return Err(format!("{}", c.heads)); }
    Ok(c.heads / c.groups)                                         // line 13
}
// Adversarial: no guard on the divisor. Must stay refuted.
pub fn unguarded_fmt_divisor(c: &Cfg) -> Result<usize, String> {
    if c.heads == 0 { return Err(String::new()); }
    if !c.heads.is_multiple_of(2) { return Err(format!("{}", c.groups)); }
    Ok(c.heads / c.groups)                                         // line 19
}
#[inline(never)]
pub fn zero(c: &mut Cfg) { c.groups = 0; }
// Adversarial: a call that really writes the divisor after the guard. Must not prove.
pub fn guard_then_mut_call(c: &mut Cfg) -> Result<usize, String> {
    if c.groups == 0 { return Err(String::new()); }
    zero(c);
    if !c.heads.is_multiple_of(c.groups) { return Err(format!("{}", c.groups)); }
    Ok(c.heads / c.groups)                                         // line 28
}

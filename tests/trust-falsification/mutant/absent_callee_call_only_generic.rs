#![crate_type = "lib"]
// Trust R3 prerequisite P0 (probe T5d): a GENERIC caller of a bodyless trait
// method. No body exists ANYWHERE for `D::m`, yet before the counted-carrier
// fix this compiled clean (rc=0) under the default strict policy — panic-freedom
// claimed for a callee that does not exist. The call must take the bridge's
// absent-callee arm and FAIL CLOSED (exit 1).
pub trait D {
    fn m(&self) -> u32;
}
pub fn r3_t_default<T: D>(t: &T) -> u32 {
    t.m()
}

//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: An inherent method taking `&self`, isolated against f14 (a free fn with a
//@ probe-note: `&u64` parameter). f14 pins the reference DOMAIN; this pins the receiver
//@ probe-note: POSITION, which is how every clean-kernel method is actually spelled.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct S(pub u64);
impl S {
    pub fn get(&self) -> u64
        ensures result == ident_isl(self.0)
    { self.0 }
}

//@ trust-ladder: refuses
//@ trust-ladder-row: <dyn core::fmt::Write as core::fmt::Write>::write_str
use core::fmt;
pub struct S(pub u32);
impl fmt::Debug for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "S({})", self.0) }
}

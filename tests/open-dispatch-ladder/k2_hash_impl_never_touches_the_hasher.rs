//@ trust-ladder: verifies
//! k1's control, and the exact mirror of g4/h4: an `impl Hash` whose body never
//! calls a method on its `H` verifies. So the trigger is the CALL, not the
//! non-foundational type in the signature.
use core::hash::{Hash, Hasher};
pub struct S(pub u32);
impl Hash for S {
    fn hash<H: Hasher>(&self, _state: &mut H) {}
}

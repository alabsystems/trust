//@ trust-ladder: verifies
//! SCOPE CONTROL. Six of the eight common derives verify today. Recorded so the
//! open-dispatch item is never restated as "derives do not work".
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct S { pub a: u32 }

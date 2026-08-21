#![crate_type = "lib"]

use std::ops::Deref;

pub struct LevelArc(Box<Level>);

impl Deref for LevelArc {
    type Target = Level;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(u32),
}

impl Level {
    // This is the wave-W3 target shape: matching through `&self` creates the
    // binding/reborrow/call-result/autoref relay around each overloaded Deref
    // call. `panic=abort` then changes each built-side call unwind to
    // `Unreachable`, exercising wave-W3b before this body can flip.
    #[inline(never)]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Zero => true,
            Self::Succ(_) | Self::Param(_) => false,
            Self::Max(left, right) => left.is_zero() && right.is_zero(),
            Self::IMax(_, right) => right.is_zero(),
        }
    }
}

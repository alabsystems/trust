#![crate_type = "lib"]

use std::ops::Deref;

pub struct StrBox(Box<str>);

impl Deref for StrBox {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub enum TextTree {
    Empty,
    Pair(StrBox, StrBox),
}

impl TextTree {
    // The W3 relay shape is otherwise the same as `Level::is_zero`, but the
    // accessor result and autoref are wide `&str` values. The flip fragment
    // has no metadata lane, so this must fail closed at the relay gate.
    #[inline(never)]
    pub fn all_empty(&self) -> bool {
        match self {
            Self::Empty => true,
            Self::Pair(left, right) => left.is_empty() && right.is_empty(),
        }
    }
}

//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An unverified dependency whose query type's `Hash`/`PartialEq` panic (review round
//! 66: a `HashMap` lookup through `K: Borrow<Q>` hashes and compares `Q`, not `K`).
use std::hash::{Hash, Hasher};

pub struct Q(pub u8);

impl Hash for Q {
    fn hash<H: Hasher>(&self, _h: &mut H) {
        if self.0 == 7 {
            panic!("Q::hash panics")
        }
    }
}

impl PartialEq for Q {
    fn eq(&self, o: &Q) -> bool {
        if self.0 == 9 {
            panic!("Q::eq panics")
        }
        self.0 == o.0
    }
}

impl Eq for Q {}

pub static QS: Q = Q(0);

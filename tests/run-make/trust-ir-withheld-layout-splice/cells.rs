//! Thread-locals whose cells carry a DECLINED `Option` payload (a tuple, a fn pointer): the
//! producer spells the `Option` as its `Ty::Bool` flag lane and withholds the layout of every
//! struct row over it. `plain` is the control whose `Option` is a first-class enum.
use std::cell::{Cell, RefCell};

thread_local! {
    static PAIR: RefCell<Option<(u64, u64)>> = RefCell::new(None);
    static HOOK: Cell<Option<fn(u32) -> u32>> = Cell::new(None);
    static PLAIN: RefCell<Option<u64>> = RefCell::new(None);
}

pub fn pair() -> usize {
    PAIR.with(|c| std::mem::size_of_val(&*c.borrow()))
}

pub fn hook() -> usize {
    HOOK.with(|c| std::mem::size_of_val(c))
}

pub fn plain() -> usize {
    PLAIN.with(|c| std::mem::size_of_val(&*c.borrow()))
}

//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_trusts.rs` and `_trusts_holds.rs`:
//! items whose paths, where they are defined, end as std's do. Its fns are
//! safe to call, and sound.

/// A bounded stack named `Vec`: when it is full, the newest value takes the
/// place of the last one (a value put over another). At
/// `seal_dep_collide::stack::Vec::push`.
pub mod stack {
    pub struct Vec<T> {
        items: std::vec::Vec<T>,
        cap: usize,
    }
    impl<T> Vec<T> {
        pub fn with_capacity(cap: usize) -> Self {
            Vec { items: std::vec::Vec::new(), cap }
        }
        pub fn push(&mut self, value: T) {
            if self.items.len() < self.cap {
                self.items.push(value);
            } else if let Some(last) = self.items.last_mut() {
                *last = value;
            }
        }
    }
}

/// A bag named `Vec` that only ever adds. At `seal_dep_collide::bag::Vec::push`.
pub mod bag {
    pub struct Vec<T> {
        items: std::vec::Vec<T>,
    }
    impl<T> Vec<T> {
        pub fn new() -> Self {
            Vec { items: std::vec::Vec::new() }
        }
        pub fn push(&mut self, value: T) {
            self.items.push(value);
        }
        pub fn len(&self) -> usize {
            self.items.len()
        }
    }
}

/// A trait of its own at `seal_dep_collide::any::Any`, and a fn that swaps
/// two boxed values of it (not generic: never read).
pub mod any {
    pub trait Any {
        fn label(&self) -> u8 {
            0
        }
    }
    pub fn exchange(a: &mut Box<dyn Any>, b: &mut Box<dyn Any>) {
        std::mem::swap(a, b)
    }
}

/// A ring, convertible into a std `Vec`: the newest value takes the oldest
/// one's slot. Its `from` is defined at `seal_dep_collide::Vec::from`.
pub struct Ring<T> {
    items: Vec<T>,
    cap: usize,
}
impl<T> Ring<T> {
    pub fn new(cap: usize) -> Self {
        Ring { items: Vec::new(), cap }
    }
    pub fn put(&mut self, value: T) {
        self.items.push(value)
    }
}
impl<T> From<Ring<T>> for Vec<T> {
    fn from(mut ring: Ring<T>) -> Vec<T> {
        while ring.items.len() > ring.cap {
            let newest = ring.items.pop().unwrap();
            ring.items[0] = newest;
        }
        ring.items
    }
}

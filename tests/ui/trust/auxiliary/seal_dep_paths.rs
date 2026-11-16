//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_impl_paths.rs` and `_impl_paths_holds.rs`:
//! in one module, a free fn `reset` that only measures beside a blanket impl's
//! `reset` that overwrites `*self`; and a blanket `Touch::touch` that measures
//! beside a slice impl's `Shuffle::touch` that swaps. Safe, and sound.
#![forbid(unsafe_code)]

pub mod coll {
    pub fn reset<T>(x: &mut T) -> usize {
        core::mem::size_of_val(x)
    }
    pub trait Reset {
        fn reset(&mut self);
    }
    impl<T: Default> Reset for T {
        fn reset(&mut self) {
            *self = T::default()
        }
    }
    pub trait Touch {
        fn touch(&mut self) -> usize;
    }
    impl<T> Touch for T {
        fn touch(&mut self) -> usize {
            core::mem::size_of_val(self)
        }
    }
    pub trait Shuffle {
        fn touch(&mut self) -> usize;
    }
    impl<T> Shuffle for [T] {
        fn touch(&mut self) -> usize {
            if self.len() > 1 {
                self.swap(0, 1)
            }
            self.len()
        }
    }
}

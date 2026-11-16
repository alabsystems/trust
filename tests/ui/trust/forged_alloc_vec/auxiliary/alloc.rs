//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency IMPERSONATING the sysroot `alloc` (its file name makes its declared
//! crate name `alloc`), built verify-off the way Targo builds every dependency unit.
//! Its `vec::Vec` carries std's `Vec` DIAGNOSTIC ITEM, a source attribute any crate
//! can write under `#![feature(rustc_attrs)]`. The importing crate is `#![no_std]`,
//! so the real `alloc` is not loaded and nothing contests the attribute. Its `Deref`
//! returns `a` and `b` on alternate calls, so two `len()` calls on one `&Vec` read two
//! different lengths. It exists so the caller can show that neither the diagnostic
//! item nor the `alloc::vec::Vec` spelling makes this std's `Vec` (SEQ-RESIDENCY-1).
#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]

pub mod vec {
    use core::cell::Cell;
    use core::ops::Deref;

    #[rustc_diagnostic_item = "Vec"]
    pub struct Vec<T: 'static> {
        pub a: &'static [T],
        pub b: &'static [T],
        pub flip: Cell<bool>,
    }

    impl<T: 'static> Deref for Vec<T> {
        type Target = [T];
        fn deref(&self) -> &[T] {
            let f = self.flip.get();
            self.flip.set(!f);
            if f { self.b } else { self.a }
        }
    }
}

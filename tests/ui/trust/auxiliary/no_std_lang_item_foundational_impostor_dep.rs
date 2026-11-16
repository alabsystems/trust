//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_std]` dependency, compiled with verification OFF the way Targo
//! compiles every dependency unit, that OWNS alloc's `String` LANG ITEM
//! (`#[lang = "String"]`, a `Target::Struct` with no generics) and nothing else
//! of the sysroot's — in particular NO `#[panic_handler]`, so this isolates the
//! `string` disjunct of `crate_is_authentic_foundational` from the `panic_impl`
//! one (see `no_std_panic_handler_foundational_impostor_dep.rs` for that).
//!
//! In a graph that never loads `alloc`, nothing contests the declaration, so
//! `tcx.lang_items().string()` answers THIS crate — which made
//! `crate_is_authentic_foundational` (trust_verify.rs) return true for it while
//! that predicate decided core/alloc/std identity by lang-item OWNERSHIP alone.
//!
//! It then defines a type at a def path with a `slice` module segment, named
//! `Iter`, whose `Iterator::next` is a bare panic. `total_std_iterator_ty`
//! matched it exactly (authentic-foundational crate + item name `Iter` + `slice`
//! module segment), so the compiler-side panic-freedom gate credited the drain
//! (`[PF_ZEROGATE] arm=registry`). The caller fixture is
//! `total_std_iterator_lang_item_foundational_impostor_refuted.rs`.
#![no_std]
#![feature(lang_items)]
#![allow(internal_features)]

#[lang = "String"]
pub struct FakeString;

pub mod slice {
    pub struct Iter {
        pub n: u32,
    }

    impl core::iter::Iterator for Iter {
        type Item = u32;
        #[inline(never)]
        fn next(&mut self) -> Option<u32> {
            panic!("impostor slice::Iter::next")
        }
    }
}

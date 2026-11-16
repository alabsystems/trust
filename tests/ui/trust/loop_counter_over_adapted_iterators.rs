//@ needs-trust-verify
//@ edition: 2021
//@ revisions: skip bytes windows_enumerate while_let vec_ref chars_rev owned_vec
//@ revisions: cycle_overflows zst_overflows fake_slice_iter user_trait_split zst_enum_slice
//@ revisions: fieldless_enum_counters zst_enumerate_index one_variant_enum_overflows
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[skip] check-pass
//@[bytes] check-pass
//@[windows_enumerate] check-pass
//@[while_let] check-pass
//@[vec_ref] check-pass
//@[chars_rev] check-pass
//@[owned_vec] check-pass
//@[cycle_overflows] check-fail
//@[zst_overflows] check-fail
//@[fake_slice_iter] check-fail
//@[user_trait_split] check-fail
//@[zst_enum_slice] check-fail
//@[fieldless_enum_counters] check-pass
//@[zst_enumerate_index] check-pass
//@[one_variant_enum_overflows] check-fail
//! **A `usize` counter over an ADAPTED iterator cannot overflow (Trust, 2026-09-29).**
//!
//! `for &x in v { n += 1 }` over a slice already proved: the loop runs at most
//! `v.len() <= isize::MAX` times. The same counter over `v.iter().skip(1)`,
//! `s.bytes()`, `v.windows(2).enumerate()` or a `while let` over `v.iter()` was
//! refuted with `n = usize::MAX` (the ordinary-Rust completeness sweep's most
//! common default-lane refusal), because the trip-count trace stopped at the first
//! adapter. It now follows `into_iter`, the slice iterators, the `str` views and
//! the adapters that yield at most what they wrap, down to the array, slice, `Vec`
//! or `str` at the root (`loop_bounds::iterated_source_yield_bound`).
//!
//! * `skip` … `owned_vec`: POSITIVE. `owned_vec` iterates a `Vec` by value: its
//!   `IntoIter` is dropped after the loop, which the origin hop refused until the
//!   loop's own instance was traced through its one initializer
//!   (`loop_bounds::loop_instance_initializer`).
//! * `cycle_overflows`: `cycle` yields forever, so a `u8` counter over it overflows;
//!   it is not a length-non-increasing adapter and must stay refuted.
//! * `zst_overflows`: a slice of `()` can hold `usize::MAX` elements, so a `usize`
//!   counter over it really can overflow on the last one.
//! * `fake_slice_iter`, `user_trait_split`, `zst_enum_slice`: the three shapes the
//!   trip-count lane review (2026-09-29) found proved and panicking. A user
//!   `impl<T> Foo<[T]> { fn iter(..) }` was matched as `<[T]>::iter`; a user trait's
//!   `split` implemented for `String` was matched as `str::split`; a slice of
//!   `Result<(), Infallible>` (zero-sized) was bounded by `isize::MAX`.
//! * `fieldless_enum_counters`: POSITIVE. `Ordering`, `enum { A, B }` and
//!   `Option<()>` are one byte, so their slices hold at most `isize::MAX` elements.
//!   (A `Vec` of them by value proves its counter too, but the default policy keeps
//!   `IntoIter<Two>`'s drop, an absent std callee instantiated at a user type,
//!   fail-closed.) Fixing `zst_enum_slice` stopped counting the extractor's synthetic tag
//!   as a byte and lost these with it; one variant-aware rule in trust-types
//!   (`alloc_model::ty_is_definitely_nonzero_sized`) now serves every length lane
//!   (the trip-count lane's precondition audit, 2026-09-29).
//! * `zst_enumerate_index`: POSITIVE. `i < len <= usize::MAX` whatever the element
//!   size, so `i + 1` cannot overflow even over `&[()]`; a zero-sized element's length
//!   used to have no upper bound at all.
//! * `one_variant_enum_overflows`: `enum E { A }` is zero-sized, so a counter that
//!   starts at 1 really overflows on `usize::MAX` elements.

#[cfg(skip)]
pub fn tail_len(v: &[u32]) -> usize {
    let mut n = 0usize;
    for _ in v.iter().skip(1) {
        n += 1;
    }
    n
}

#[cfg(bytes)]
pub fn byte_count(s: &str) -> usize {
    let mut n = 0usize;
    for _ in s.bytes() {
        n += 1;
    }
    n
}

#[cfg(windows_enumerate)]
pub fn window_count(v: &[u32]) -> usize {
    let mut n = 0usize;
    for (_i, _w) in v.windows(2).enumerate() {
        n += 1;
    }
    n
}

#[cfg(while_let)]
pub fn manual_count(v: &[u32]) -> usize {
    let mut n = 0usize;
    let mut it = v.iter();
    while let Some(_) = it.next() {
        n += 1;
    }
    n
}

#[cfg(vec_ref)]
pub fn vec_count(v: &Vec<u64>) -> usize {
    let mut n = 0usize;
    for _ in v {
        n += 1;
    }
    n
}

#[cfg(chars_rev)]
pub fn char_count(s: &str) -> usize {
    let mut n = 0usize;
    for _ in s.chars().rev() {
        n += 1;
    }
    n
}

#[cfg(owned_vec)]
pub fn owned_count(v: Vec<u32>) -> usize {
    let mut n = 0usize;
    for x in v {
        if x > 10 {
            n += 1;
        }
    }
    n
}

#[cfg(cycle_overflows)]
pub fn forever(v: &[u32]) -> u8 {
    //[cycle_overflows]~^ ERROR Trust
    let mut c = 0u8;
    for _ in v.iter().cycle() {
        c += 1;
    }
    c
}

#[cfg(zst_overflows)]
pub fn units(v: &[()]) -> usize {
    //[zst_overflows]~^ ERROR Trust
    let mut n = 0usize;
    for _ in v {
        n += 1;
    }
    n
}

#[cfg(fake_slice_iter)]
pub struct Foo<T: ?Sized>(pub core::marker::PhantomData<T>);

#[cfg(fake_slice_iter)]
impl<T> Foo<[T]> {
    pub fn iter(_a: &[u8; 3]) -> core::ops::Range<u32> {
        0..300
    }
}

#[cfg(fake_slice_iter)]
pub fn range_iter<T>(a: &[u8; 3]) -> u8 {
    //[fake_slice_iter]~^ ERROR Trust
    let mut c: u8 = 0;
    for _ in Foo::<[T]>::iter(a) {
        c += 1;
    }
    c
}

#[cfg(user_trait_split)]
static BIG: [u8; 300] = [0; 300];

#[cfg(user_trait_split)]
pub trait MySplit {
    fn split(a: &[u8; 3]) -> core::slice::Iter<'static, u8>;
}

#[cfg(user_trait_split)]
impl MySplit for String {
    fn split(_a: &[u8; 3]) -> core::slice::Iter<'static, u8> {
        BIG.iter()
    }
}

#[cfg(user_trait_split)]
pub fn count_pieces(a: &[u8; 3]) -> u8 {
    //[user_trait_split]~^ ERROR Trust
    let mut c: u8 = 0;
    for _ in <String as MySplit>::split(a) {
        c += 1;
    }
    c
}

#[cfg(zst_enum_slice)]
pub fn count_units(s: &[Result<(), core::convert::Infallible>]) -> usize {
    //[zst_enum_slice]~^ ERROR Trust
    let mut c: usize = 1;
    for _ in s.iter().skip(0) {
        c += 1;
    }
    c
}

#[cfg(any(fieldless_enum_counters, zst_enumerate_index))]
#[derive(Clone, Copy)]
pub enum Two {
    A,
    B,
}

#[cfg(fieldless_enum_counters)]
pub fn count_orderings(s: &[core::cmp::Ordering]) -> usize {
    let mut c = 1usize;
    for _ in s {
        c += 1;
    }
    c
}

#[cfg(fieldless_enum_counters)]
pub fn two_len_plus_one(s: &[Two]) -> usize {
    s.len() + 1
}

#[cfg(fieldless_enum_counters)]
pub fn count_option_units(s: &[Option<()>]) -> usize {
    let mut c = 1usize;
    for _ in s {
        c += 1;
    }
    c
}

#[cfg(zst_enumerate_index)]
pub fn last_unit_index(v: &[()]) -> usize {
    let mut m = 0usize;
    for (i, _) in v.iter().enumerate() {
        m = i + 1;
    }
    m
}

#[cfg(zst_enumerate_index)]
pub fn last_two_index(v: &[Two]) -> usize {
    let mut m = 0usize;
    for (i, _) in v.iter().enumerate() {
        m = i + 1;
    }
    m
}

#[cfg(one_variant_enum_overflows)]
#[derive(Clone, Copy)]
pub enum One {
    A,
}

#[cfg(one_variant_enum_overflows)]
pub fn count_ones(s: &[One]) -> usize {
    //[one_variant_enum_overflows]~^ ERROR Trust
    let mut c = 1usize;
    for _ in s {
        c += 1;
    }
    c
}

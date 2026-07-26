#![crate_type = "lib"]
// In-place mutation over a slice: `for x in s.iter_mut() { *x = … }` — one of the
// most common Rust loops. It desugars to `<[T]>::iter_mut` (a total `slice::IterMut`)
// + `IntoIterator::into_iter` (identity on the iterator) + repeated `next(&mut iter)`
// yielding `Option<&mut i32>`, whose payload is loaded AND stored through a
// `ValidBorrow` reference. The native CHC proves the whole thing panic-free under
// the default strict policy: the iterator/borrow are sound fresh-symbolic, the store
// through the `&mut` is valid (not fail-closed), and the `wrapping_add` body has no
// arithmetic obligation.
pub fn foreach_iter_mut(s: &mut [i32]) {
    for x in s.iter_mut() {
        *x = x.wrapping_add(1);
    }
}

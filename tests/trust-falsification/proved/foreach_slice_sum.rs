#![crate_type = "lib"]
// The dominant Rust loop form: `for &x in s { … }` over a slice. It desugars to
// `IntoIterator::into_iter(s)` + repeated `Iterator::next(&mut iter)` + a match on
// the yielded `Option<&i32>`. The native CHC now proves the whole thing
// panic-free under the default strict policy: the slice iterator's total
// into_iter/next are modeled as fresh-symbolic, the `&mut iter` borrow is
// transparent (not unsupported), the yielded `Option` threads across the
// loop-body→match block boundary, its discriminant-validity assume discharges the
// match's otherwise→unreachable, and the `&x` deref is a `ValidBorrow` load. The
// body uses `wrapping_add`, so there is no arithmetic obligation — the function is
// statically panic-free.
pub fn foreach_slice_sum(s: &[i32]) -> i32 {
    let mut t = 0i32;
    for &x in s {
        t = t.wrapping_add(x);
    }
    t
}

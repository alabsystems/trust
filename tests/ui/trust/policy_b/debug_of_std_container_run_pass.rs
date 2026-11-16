//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ run-pass
//! `<Option<T> as Debug>::fmt`, `<[T; N] as Debug>::fmt` and the tuple `Debug`
//! impls are core code that only forward to `<T as Debug>::fmt`; over foundational
//! `T` no user code runs, so the format is foundational. The discriminator used to
//! admit only scalars/`str`/`String` and refused these as a "user Display".
//! (`vec![..]` is deliberately absent: its `IntoIter` projects a `MaybeUninit`
//! union field, which the typed lowering does not model yet — a separate gap,
//! not a `Display` question.)
fn main() {
    println!("{:?}", Some(std::hint::black_box(5u64)));
    println!("{:?}", (std::hint::black_box(1i32), "x"));
    println!("{:?}", [std::hint::black_box(7u8), 8]);
}

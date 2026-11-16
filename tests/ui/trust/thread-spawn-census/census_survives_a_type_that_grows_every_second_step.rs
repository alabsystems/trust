//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census -Ztrust-writer-census=n
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=n
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `Z<T, U>` holds a `Z<U, Option<T>>`: the nesting grows only every second
//! step (2, 3, 3, 4, 4, ...), so counting re-entries at a STRICTLY deeper
//! type than the one just before never passed one, and every type walk went
//! to its backstop, once per root type. The count skips an entry that is not
//! shallower and keeps looking, and a walk that reaches the backstop names
//! what multiplied, so the next walk does not enter it again.

struct Z<T: 'static, U: 'static>(
    T,
    U,
    Option<&'static Z<U, Option<T>>>,
    Option<&'static Z<U, (T,)>>,
);

fn make<T: Default + 'static, U: Default + 'static>() -> u8 {
    let z: Z<T, U> = Z(T::default(), U::default(), None, None);
    let r = &z;
    r.2.is_none() as u8
}

fn main() {
    let mut n = 0u8;
    n += make::<u8, u8>();
    n += make::<u8, u16>();
    n += make::<u8, u32>();
    n += make::<u8, u64>();
    n += make::<u8, i8>();
    n += make::<u8, i16>();
    n += make::<u8, i32>();
    n += make::<u8, i64>();
    println!("{n}");
}

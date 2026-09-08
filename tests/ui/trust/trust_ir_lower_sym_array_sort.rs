//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-SA): a PARAM-BEARING array type — `[T; N]`, `[u8; N]`,
//! `[T; SIZE]` — is a pre-monomorphization SORT, not a gap: it lowers to the
//! same opaque zero-field struct the `ty::Alias` arm registers for
//! `<T as Tr>::Assoc`, and the body is SYMBOLIC. What this admits is exactly
//! the value-less carrier: params, locals, returns and call arguments of the
//! type. Every array OPERATION (index, unsize to a slice, repeat) keeps failing
//! closed at its own site, which is why none appears below. Under `strict` so
//! a regression is a compile error.

fn pass_through<const N: usize>(a: [u8; N]) -> [u8; N] {
    a
}

fn rebind<T, const N: usize>(a: [T; N]) -> [T; N] {
    let b = a;
    b
}

fn count<T, const N: usize>(_a: [T; N]) -> usize {
    N
}

fn forward<const N: usize>(a: [u32; N]) -> usize {
    count(a)
}

fn main() {
    if pass_through([1u8, 2, 3])[2] != 3 {
        std::process::exit(1);
    }
    if rebind([7u16; 2])[1] != 7 {
        std::process::exit(2);
    }
    if forward([0u32; 5]) != 5 {
        std::process::exit(3);
    }
}

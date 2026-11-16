//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-SA2): the CONSTRUCTION twin of wave-SA. A repeat whose array
//! type is the pre-monomorphization sort — `[a; N]`, `[0; N]`,
//! `[T::default(); N]` — lowers to the sort's only inhabitant (the empty
//! aggregate of the shared opaque zero-field struct); the element is still
//! lowered for its effects and a borrow-pointer element keeps its refusal.
//! Body SYMBOLIC, as wave-SA left it. Under `strict`.

fn zeros<const N: usize>() -> [u8; N] {
    [0; N]
}

fn splat<T: Copy, const N: usize>(a: T) -> [T; N] {
    [a; N]
}

fn defaults<T: Default + Copy, const N: usize>() -> [T; N] {
    [T::default(); N]
}

fn main() {
    if zeros::<3>()[2] != 0 {
        std::process::exit(1);
    }
    if splat::<u16, 2>(9)[1] != 9 {
        std::process::exit(2);
    }
    if defaults::<u8, 4>()[3] != 0 {
        std::process::exit(3);
    }
}

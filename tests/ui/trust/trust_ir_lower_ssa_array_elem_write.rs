//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-AI): `a[K] = v` and `a[K] op= v` on an UNPROMOTED, SSA-bound
//! array local with a CONSTANT in-bounds index lower as value surgery —
//! `InsertElement` + `set_local` (the element twin of wave-AW's `a.b = v`),
//! with the compound form reading the element through the `Index` arm's own
//! `ExtractElement`. Oracle parity: the bridge's `lower_array_projected_store`
//! emits exactly `InsertElement` at a constant index for the same statement.
//! Never borrowed, so every local below stays SSA; under `strict` so a
//! regression is a compile error. A dynamic index (`a[i] = v`) and a
//! promoted (`&mut`-borrowed) array keep failing closed and are absent here.

fn set_third() -> u8 {
    let mut buf = [0u8; 4];
    buf[2] = 7;
    buf[2]
}

fn bump() -> u32 {
    let mut ints = [1u32, 2, 3];
    ints[0] += 41;
    ints[0]
}

fn chain(v: u16) -> u16 {
    let mut a = [0u16; 2];
    a[0] = v;
    a[1] = a[0];
    a[0] += a[1];
    a[0]
}

fn main() {
    if set_third() != 7 {
        std::process::exit(1);
    }
    if bump() != 42 {
        std::process::exit(2);
    }
    if chain(21) != 42 {
        std::process::exit(3);
    }
}

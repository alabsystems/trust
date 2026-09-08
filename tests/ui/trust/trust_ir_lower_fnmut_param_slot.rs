//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-PM): a by-value param of bare type-parameter type (`f: F`,
//! `F: FnMut`) that the body `&mut`-borrows (`f(x)` is `FnMut::call_mut(&mut
//! f, (x,))`) is promoted to a symbolic `Unit` slot, so the reborrow resolves
//! to a ledgered slot pointer that forwards into the generic `call_mut` havoc
//! call. The body stays SYMBOLIC (never spliced or sampled). Under `strict`.

fn call_twice<F: FnMut(u32) -> u32>(mut f: F, x: u32) -> u32 {
    f(x) + f(x)
}

fn call_it<F: FnMut()>(mut f: F) {
    f();
    f();
}

fn main() {
    // Capture-free closures only: a CAPTURING closure literal in argument
    // position is a different (wave-ZC) question and stays out of this pin.
    call_it(|| {});
    if call_twice(|v| v + 1, 20) != 42 {
        std::process::exit(1);
    }
}

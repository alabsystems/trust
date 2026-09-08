//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-FI2): a FUNCTION ITEM in `let` or statement position — `let f =
//! foo;`, `let _ = foo::<T>;`, `ensure_is_sized::<T>;` — binds nothing, the
//! fn-item twin of the non-capturing-closure `let` skip: calls through the
//! local resolve by its TYPE, and any use as a VALUE keeps failing closed.
//! Under `strict`.

fn foo<T>() -> u32 {
    let _ = std::mem::size_of::<T>;
    41
}

fn ensure_is_sized<T: Sized>() {}

fn call_through_local(x: u32) -> u32 {
    let f = foo::<u8>;
    f() + x
}

fn statement_form<T>() {
    ensure_is_sized::<T>;
    let _ = ensure_is_sized::<T>;
}

fn main() {
    statement_form::<u16>();
    if call_through_local(1) != 42 {
        std::process::exit(1);
    }
}

//@ dont-check-compiler-stderr
//@ check-fail
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Re-pinned 2026-10-15 (the merge of 2026-10-14 brought WS5.2, 87388a9d3ec and aa2f22aa306):
// `Function.name` is now the link-time symbol, and a GENERIC definition has none until
// per-instance lowering (B8), so `-Ztrust-ir-lower=strict` refuses each one by name at crate
// assembly ("lowered for coverage, never spliced"). Those refusals are pinned below; every
// other body must still lower, and any other strict error fails this test.
//! Trust (wave-FI2): a FUNCTION ITEM in `let` or statement position — `let f =
//! foo;`, `let _ = foo::<T>;`, `ensure_is_sized::<T>;` — binds nothing, the
//! fn-item twin of the non-capturing-closure `let` skip: calls through the
//! local resolve by its TYPE, and any use as a VALUE keeps failing closed.
//! Under `strict`.

fn foo<T>() -> u32 {
    //~^ ERROR NoLinkTimeSymbol(foo): no link-time symbol for `foo`
    let _ = std::mem::size_of::<T>;
    41
}

fn ensure_is_sized<T: Sized>() {}
    //~^ ERROR NoLinkTimeSymbol(ensure_is_sized): no link-time symbol for `ensure_is_sized`

fn call_through_local(x: u32) -> u32 {
    let f = foo::<u8>;
    f() + x
}

fn statement_form<T>() {
    //~^ ERROR NoLinkTimeSymbol(statement_form): no link-time symbol for `statement_form`
    ensure_is_sized::<T>;
    let _ = ensure_is_sized::<T>;
}

fn main() {
    statement_form::<u16>();
    if call_through_local(1) != 42 {
        std::process::exit(1);
    }
}

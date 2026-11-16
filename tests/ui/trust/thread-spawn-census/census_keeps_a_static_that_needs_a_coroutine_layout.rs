//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A census flag only adds notes: it must not reject a valid program. A
//! static's initializer can need an async fn's coroutine layout; with a census
//! forced, that layout is read from the coroutine's pre-steal MIR, as under
//! verification, and not from an `optimized_mir` that forces the census while
//! it is evaluating this same static (E0391).

async fn f() {}

const fn ret_size<T>(_: &fn() -> T) -> usize {
    std::mem::size_of::<T>()
}

static N: usize = ret_size(&(f as fn() -> _));

fn main() { //~ NOTE send census: `main` sends on no std channel
    println!("{}", N);
}

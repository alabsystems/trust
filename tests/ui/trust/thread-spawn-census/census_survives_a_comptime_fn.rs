//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The actor censuses are notes: they must not crash the compiler. Const
//! evaluation steals the elaborated MIR of a `#[rustc_comptime]` fn; such a
//! body runs only at compile time, so the consumer and writer censuses do not
//! read it.
#![feature(rustc_attrs)]
#![allow(internal_features)]

enum Msg {
    A,
}

#[rustc_comptime]
fn leaf() -> usize {
    1
}

const N: usize = leaf();

fn main() { //~ NOTE send census: `main` sends `Msg` (A) via
    let (tx, _rx) = std::sync::mpsc::channel();
    tx.send(Msg::A).unwrap();
    let _ = N;
}

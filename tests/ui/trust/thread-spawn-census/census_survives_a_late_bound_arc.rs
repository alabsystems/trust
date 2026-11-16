//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The actor censuses are notes: they must not crash the compiler. A consumer's
//! signature can hold an `Arc` of a type with an elided (late-bound) lifetime,
//! and a field can be a fn pointer that binds one: the shared-state census
//! erases the signature's bound regions and asks no trait query of a type that
//! still names one.

use std::sync::{Arc, mpsc};

struct Holder<'a>(&'a u8);

struct Hooks {
    on: for<'a> fn(Arc<Holder<'a>>),
}

enum Msg {
    A,
    B,
}

fn consume(rx: mpsc::Receiver<Msg>, _shared: Arc<Holder<'_>>, hooks: &Hooks) -> u8 { //~ NOTE consumer census: `consume` drains a channel of `Msg`
    let _ = hooks.on;
    match rx.recv().unwrap() {
        Msg::A => 1,
        Msg::B => 2,
    }
}

fn main() {
    let (tx, rx) = mpsc::channel();
    tx.send(Msg::A).unwrap();
    consume(rx, Arc::new(Holder(&0)), &Hooks { on: |_| {} });
}

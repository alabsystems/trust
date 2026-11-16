//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The actor censuses are notes: they must not hang the compiler. A legal
//! polymorphically recursive type has a new instantiation at every step
//! (`Nest<u8>`, `Nest<Option<u8>>`, ...): the shared-state census's walk over a
//! consumer's fields does not expand a type again below itself.

use std::sync::mpsc;

struct Nest<T: 'static>(T, Option<&'static Nest<Option<T>>>);

enum Msg {
    A,
    B,
}

fn consume(rx: mpsc::Receiver<Msg>, _nest: Nest<u8>) -> u8 { //~ NOTE consumer census: `consume` drains a channel of `Msg`
    match rx.recv().unwrap() {
        Msg::A => 1,
        Msg::B => 2,
    }
}

fn main() {
    let (tx, rx) = mpsc::channel();
    tx.send(Msg::A).unwrap();
    consume(rx, Nest(0, None));
}

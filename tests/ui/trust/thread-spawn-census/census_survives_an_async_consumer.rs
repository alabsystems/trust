//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The actor censuses are notes: they must not crash the compiler. An async
//! fn body that takes a message is a coroutine, which has no `fn_sig`, and a
//! message it holds across an await lives in the coroutine's state. The
//! consumer census does not examine it, and says so at the body instead of
//! saying nothing; the writer census counts it.

use std::sync::mpsc;

enum Msg {
    A,
    B,
}

async fn consume(rx: mpsc::Receiver<Msg>) -> u8 { //~ NOTE consumer census: `consume::{closure#0}` is async and takes `Msg` (off a channel, or as an argument): an async body is not examined
    match rx.recv().unwrap() {
        Msg::A => 1,
        Msg::B => 2,
    }
}

fn main() {
    let (tx, rx) = mpsc::channel();
    tx.send(Msg::A).unwrap();
    drop(consume(rx));
}

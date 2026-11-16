//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Temporal P3, the send census (`-Ztrust-send-census`): for every thread the
//! spawn census finds, and for `main`, a note naming each std channel send the
//! thread can reach, with the message type and a shortest call path. These are
//! the actors a model derived from this program would have, and what each
//! posts. `post` is generic, as winit's `EventLoopProxy::send_event` is, so the
//! census walks its MIR to the std `Sender::send` it ends in; the watcher's send
//! is carried by the closure the thread runs. Each note names the variants the
//! thread sends, traced back from the send through `post`'s parameter to the
//! value constructed (a branch gives both). The `_watch` thread posts one
//! variant itself and the other through a closure it hands a generic
//! `impl FnOnce` parameter, as aterm's config watcher does: two routes to the
//! one send instance, both named. `each` builds the variant and hands it to the closure
//! it is given, which the Fn traits call with its arguments in a tuple (aterm's
//! `read_seed_markers`); the variant is traced through that tuple.

use std::sync::mpsc::{Sender, channel};

#[derive(Debug)]
enum Wake {
    Policy(u8),
    Commit,
}

fn post<T>(tx: &Sender<T>, value: T) {
    let _ = tx.send(value);
}

fn post_with(send: impl FnOnce(u8) -> bool, value: u8) -> bool {
    send(value)
}

fn sender(tx: &Sender<Wake>) -> impl FnOnce(u8) -> bool + '_ {
    move |value| tx.send(Wake::Policy(value)).is_ok()
}

fn each<F: FnMut(Wake)>(mut post: F) {
    post(Wake::Commit);
}

fn main() { //~ NOTE send census: `main` sends `Wake` (Commit) via
    let (tx, rx) = channel::<Wake>();
    let watcher = tx.clone();
    let _poll = std::thread::spawn(move || post(&watcher, Wake::Policy(1))); //~ NOTE send census: the thread spawned here sends `Wake` (Policy) via
    let either = tx.clone();
    let _pick = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Commit, Policy) via
        let wake = if std::env::args().count() > 1 { Wake::Policy(2) } else { Wake::Commit };
        post(&either, wake);
    });
    let _idle = std::thread::spawn(|| { //~ NOTE send census: the thread spawned here sends on no std channel
        let _ = 1 + 1;
    });
    let both = tx.clone();
    let _watch = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Commit, Policy) via
        post(&both, Wake::Commit);
        let _ = post_with(sender(&both), 3);
    });
    let tupled = tx.clone();
    let _each = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Commit) via
        each(|wake| {
            let _ = tupled.send(wake);
        });
    });
    let _ = tx.send(Wake::Commit);
    while let Ok(wake) = rx.try_recv() {
        let _ = wake;
    }
}

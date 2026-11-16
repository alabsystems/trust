//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Temporal P3, the consumer census (after the send census, same flag): the
//! body that takes a message off a `Receiver` (`main`), or that foreign code
//! calls with it (aterm's `App::user_event` for `Wake`), and each local fn it
//! passes the message on to by value without getting it back (`handle`), is a
//! consumer when it switches over the message. A note there names the calls the
//! message passes through first (`admit` may drop it) and which variants the
//! switch gives an arm; a note at each arm names the threads that send it. A
//! variant no thread sends is named, and so is one sent but left to a catch-all
//! arm. `relay` takes a `Wake` by value and switches over it too, but forwards
//! it to a send: no drain or handler hands it one, so it is no consumer.

use std::sync::mpsc::channel;

enum Wake {
    Policy(u8),
    Commit,
    Quit,
}

enum Ack {
    Done,
    Failed,
    Retry,
}

/// Drops a `Policy` of zero before dispatch.
fn admit(wake: Wake) -> Option<Wake> {
    match wake {
        Wake::Policy(0) => None,
        other => Some(other),
    }
}

fn handle(count: &mut u32, wake: Wake) { //~ NOTE consumer census: `handle` receives `Wake` by value from `main`, through `admit` (which may drop it); its switch gives each of its 3 variants an arm. No enumerated thread sends `Wake::Quit` over the calls the census resolved
    let Some(wake) = admit(wake) else { return };
    match wake {
        Wake::Policy(n) => *count += u32::from(n), //~ NOTE consumer census: the arm for `Wake::Policy` in `handle` takes it from `main::{closure#0}` and `main::{closure#1}`
        Wake::Commit => *count += 1, //~ NOTE consumer census: the arm for `Wake::Commit` in `handle` takes it from `main` and `main::{closure#1}`
        Wake::Quit => *count = 0, //~ NOTE consumer census: the arm for `Wake::Quit` in `handle` takes it from no enumerated thread
    }
}

/// Forwards every `Wake` but `Quit`: a relay, not a consumer.
fn relay(tx: &std::sync::mpsc::Sender<Wake>, wake: Wake) {
    if !matches!(wake, Wake::Quit) {
        let _ = tx.send(wake);
    }
}

fn main() { //~ NOTE consumer census: `main` drains a channel of `Ack`; its switch gives 1 of its 3 variants an arm, and 2 share the catch-all (Failed, Retry). Sent but left to the catch-all: `Ack::Retry`. No enumerated thread sends `Ack::Failed`
    let (tx, rx) = channel::<Wake>();
    let (ack_tx, ack_rx) = channel::<Ack>();
    let poll = tx.clone();
    let _poll = std::thread::spawn(move || {
        let _ = poll.send(Wake::Policy(1));
    });
    let both = tx.clone();
    let _both = std::thread::spawn(move || {
        relay(&both, Wake::Commit);
        let _ = both.send(Wake::Policy(2));
        let _ = ack_tx.send(Ack::Retry);
        let _ = ack_tx.send(Ack::Done);
    });
    let _ = tx.send(Wake::Commit);
    let mut count = 0;
    while let Ok(wake) = rx.try_recv() {
        handle(&mut count, wake);
    }
    match ack_rx.recv() {
        Ok(Ack::Done) => count += 1, //~ NOTE consumer census: the arm for `Ack::Done` in `main` takes it from `main::{closure#1}`
        Ok(_) | Err(_) => {}
    }
    let _ = count;
}

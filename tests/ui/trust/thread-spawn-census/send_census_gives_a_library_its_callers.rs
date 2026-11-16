//@ needs-trust-verify
//@ compile-flags: --crate-type lib -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A library has no `main`: what runs its code is whoever calls it. The send
//~^ NOTE send census: code called from outside this crate (it has no `main`) sends `Wake` (Explained, Posted, Retried, Shared, …) via
//! census gives it one more actor, "code called from outside this crate",
//! starting at every body outside code can name, so a variant a public fn
//! posts is attributed and the consumer does not say no thread sends it.
//! aterm-gui is such a crate. An exported fn is a start whatever calls it
//! inside the crate: one that calls itself (`retry`), one the crate's own
//! thread also calls (`shared`), a generic one (`post_why`). An exported fn
//! that takes the message (`forward`) can be given any variant: the list ends
//! in `…`. A private type's `Drop` that only the crate's thread runs
//! (`Guard`) is that thread's send, not the callers'.

use std::fmt::Debug;
use std::sync::mpsc::{Receiver, Sender, channel};

pub enum Wake {
    Started,
    Posted,
    Forwarded,
    Explained,
    Retried,
    Shared,
    Guarded,
}

pub fn post(tx: &Sender<Wake>) {
    let _ = tx.send(Wake::Posted);
}

pub fn forward(tx: &Sender<Wake>, wake: Wake) {
    let _ = tx.send(wake);
}

pub fn post_why<T: Debug>(tx: &Sender<Wake>, why: T) {
    let _ = (why, tx.send(Wake::Explained));
}

pub fn retry(tx: &Sender<Wake>, times: u8) {
    if times > 0 {
        retry(tx, times - 1);
    }
    let _ = tx.send(Wake::Retried);
}

pub fn shared(tx: &Sender<Wake>) {
    let _ = tx.send(Wake::Shared);
}

struct Guard(Sender<Wake>);

impl Drop for Guard {
    fn drop(&mut self) {
        let _ = self.0.send(Wake::Guarded);
    }
}

pub fn start() -> (Sender<Wake>, Receiver<Wake>) {
    let (tx, rx) = channel::<Wake>();
    let worker = tx.clone();
    let _thread = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Guarded, Shared, Started) via
        let _guard = Guard(worker.clone());
        shared(&worker);
        let _ = worker.send(Wake::Started);
    });
    (tx, rx)
}

pub fn run(rx: Receiver<Wake>) -> u32 { //~ NOTE consumer census: `run` drains a channel of `Wake`; its switch gives each of its 7 variants an arm. No send was traced to `Wake::Forwarded`. 1 thread(s) send `Wake` with a value the census could not trace to a variant
    let mut seen = 0;
    while let Ok(wake) = rx.recv() {
        match wake {
            Wake::Started => seen += 1,
            Wake::Posted => seen += 10, //~ NOTE consumer census: the arm for `Wake::Posted` in `run` takes it from code called from outside the crate
            Wake::Forwarded => seen += 100,
            Wake::Explained => seen += 1000,
            Wake::Retried => seen += 10000,
            Wake::Shared => seen += 100000, //~ NOTE consumer census: the arm for `Wake::Shared` in `run` takes it from code called from outside the crate and `start::{closure#0}`
            Wake::Guarded => seen += 1000000, //~ NOTE consumer census: the arm for `Wake::Guarded` in `run` takes it from `start::{closure#0}`
        }
    }
    seen
}

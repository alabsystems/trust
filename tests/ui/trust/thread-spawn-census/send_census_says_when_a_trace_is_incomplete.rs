//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The send census says what it could not trace instead of leaving it out.
//! `SyncSender::send` and `try_send` are sends. A fn item called through a
//! generic `FnOnce` parameter gets its argument from the Fn traits' tuple, like
//! a closure. A value a call returns is not traced: the thread's variants end
//! in `…` (`(…)` alone when none was traced), and the consumer says "No send
//! was traced to" a variant, not that no thread sends it. A thread started
//! with a boxed job runs a callable the census cannot name: its note says so,
//! and so does the consumer's. The boxed job is in the pool of every
//! `dyn FnOnce()` call, so each thread that can make one "may also reach" its
//! send: the notes say that, whether or not the thread sends `Wake` itself.

use std::sync::OnceLock;
use std::sync::mpsc::{Sender, channel, sync_channel};

enum Wake {
    Tick,
    Stop,
    Late,
}

static TX: OnceLock<Sender<Wake>> = OnceLock::new();

fn post(wake: Wake) {
    if let Some(tx) = TX.get() {
        let _ = tx.send(wake);
    }
}

fn apply<F: FnOnce(Wake)>(f: F) {
    f(Wake::Tick)
}

fn pick() -> Wake {
    Wake::Late
}

fn main() { //~ NOTE consumer census: `main` drains a channel of `Wake`; its switch gives each of its 3 variants an arm. No send was traced to `Wake::Late`. 2 thread(s) send `Wake` with a value the census could not trace to a variant. 5 thread(s) may also reach a send of `Wake` behind an indirect call or a hand-off, which is not counted. 1 thread(s) run a callable the census could not name, and what they send is not counted
    let (tx, rx) = channel::<Wake>();
    let (ack, acks) = sync_channel::<u8>(1);
    let _ = TX.set(tx.clone());
    let _item = std::thread::spawn(|| apply(post)); //~ NOTE send census: the thread spawned here sends `Wake` (Tick) via main::{closure#0} -> apply::<fn(Wake) {post}> -> post -> std::sync::mpsc::Sender::<Wake>::send
    let partly = tx.clone();
    let _partly = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Stop, …) via
        let _ = partly.send(Wake::Stop);
        let _ = partly.send(pick());
    });
    let only = tx.clone();
    let _only = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (…) via
        let _ = only.send(pick());
    });
    let _sync = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `u8` via main::{closure#3} -> std::sync::mpsc::SyncSender::<u8>::send; `u8` via main::{closure#3} -> std::sync::mpsc::SyncSender::<u8>::try_send
        let _ = ack.send(1);
        let _ = ack.try_send(2);
    });
    let job: Box<dyn FnOnce() + Send> = Box::new(move || {
        let _ = tx.send(Wake::Late);
    });
    let _boxed = std::thread::spawn(job); //~ NOTE send census: the thread spawned here runs a callable the census could not name
    let _ = acks.recv();
    while let Ok(wake) = rx.recv() {
        match wake {
            Wake::Tick => {}
            Wake::Stop => {}
            Wake::Late => {} //~ NOTE consumer census: the arm for `Wake::Late` in `main`: no send was traced to it
        }
    }
}

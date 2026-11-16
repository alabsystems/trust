//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! What a library hands out, outside code runs. "Code called from outside
//~^ NOTE send census: code called from outside this crate (it has no `main`) sends `T` (any type its callers pass) via Bus::<T>::post -> std::sync::mpsc::Sender::<T>::send; `Wake` (Boxed, Dyn, Later, Pointed) via
//! this crate" starts at each callback whatever shape it leaves in: a closure
//! behind `dyn Fn` (`boxed`), a fn pointer made from a closure (`pointed`),
//! the impl behind a `dyn Trait` (`Quiet::fire`). The body of an exported
//! `async fn` (`later`) is the callers', and stays theirs when one of the
//! crate's own threads drives it too. An exported fn generic in its message
//! (`Bus::post`) can be given any of the program's message enums: its entry
//! says so, and the consumer does not say that no thread sends `Generic`.

use std::future::Future;
use std::pin::pin;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::task::{Context, Poll, Waker};

pub enum Wake {
    Boxed,
    Pointed,
    Dyn,
    Later,
    Generic,
}

pub fn boxed(tx: Sender<Wake>) -> Box<dyn Fn() + Send> {
    Box::new(move || {
        let _ = tx.send(Wake::Boxed);
    })
}

pub fn pointed() -> fn(&Sender<Wake>) {
    |tx| {
        let _ = tx.send(Wake::Pointed);
    }
}

pub trait Fire {
    fn fire(&self, tx: &Sender<Wake>);
}

struct Quiet;

impl Fire for Quiet {
    fn fire(&self, tx: &Sender<Wake>) {
        let _ = tx.send(Wake::Dyn);
    }
}

pub fn quiet() -> Box<dyn Fire> {
    Box::new(Quiet)
}

pub async fn later(tx: Sender<Wake>) {
    let _ = tx.send(Wake::Later);
}

pub struct Bus<T>(pub Sender<T>);

impl<T> Bus<T> {
    pub fn post(&self, message: T) {
        let _ = self.0.send(message);
    }
}

pub fn start() -> (Sender<Wake>, Receiver<Wake>) {
    let (tx, rx) = channel::<Wake>();
    let worker = tx.clone();
    let _thread = std::thread::spawn(move || { //~ NOTE send census: the thread spawned here sends `Wake` (Later) via
        let mut job = pin!(later(worker));
        let mut cx = Context::from_waker(Waker::noop());
        while let Poll::Pending = job.as_mut().poll(&mut cx) {}
    });
    (tx, rx)
}

pub fn run(rx: Receiver<Wake>) -> u32 {
    let mut seen = 0;
    while let Ok(wake) = rx.recv() {
        match wake {
            Wake::Boxed => seen += 1, //~ NOTE consumer census: the arm for `Wake::Boxed` in `run` takes it from code called from outside the crate
            Wake::Pointed => seen += 10, //~ NOTE consumer census: the arm for `Wake::Pointed` in `run` takes it from code called from outside the crate
            Wake::Dyn => seen += 100, //~ NOTE consumer census: the arm for `Wake::Dyn` in `run` takes it from code called from outside the crate
            Wake::Later => seen += 1000, //~ NOTE consumer census: the arm for `Wake::Later` in `run` takes it from code called from outside the crate and `start::{closure#0}`
            Wake::Generic => seen += 10000, //~ NOTE consumer census: the arm for `Wake::Generic` in `run`: no send was traced to it
        }
    }
    seen
}

//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: census_dep.rs
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The message is followed in whatever holds it on the way to the switch.
//! Each of these consumers was once not found, or described falsely:
//!
//! - `Boxed`: the drain loop boxes the message and hands the box to
//!   `handle`, which matches on `*boxed`. A wrapper moved to a local fn is a
//!   hand-off, as the message itself is.
//! - `Prev`: `match (rx.recv(), &last)` puts the receive's `Result` in a
//!   tuple beside a reference to another value of the message's type. The
//!   two are told apart by field.
//! - `Stamped`: `stamp` returns a struct with an `Option` of the message: it
//!   "may drop it", though the struct itself always comes back.
//! - `Looped`: a dependency's run loop was given the closure when it was
//!   built, and is given the receiver by `run`. The closure is in the type
//!   of the value handed over with the receiver.

extern crate census_dep;

use std::sync::mpsc::{Receiver, channel};

enum Boxed {
    A,
    B(u8),
}

fn handle(n: &mut u32, boxed: Box<Boxed>) { //~ NOTE consumer census: `handle` receives `Boxed` by value from `boxed`; its switch gives each of its 2 variants an arm
    match *boxed {
        Boxed::A => *n += 1, //~ NOTE consumer census: the arm for `Boxed::A` in `handle` takes it from `main::{closure#0}`
        Boxed::B(k) => *n += k as u32, //~ NOTE consumer census: the arm for `Boxed::B` in `handle` takes it from `main::{closure#0}`
    }
}

fn boxed(rx: Receiver<Boxed>) -> u32 {
    let mut n = 0;
    for message in rx.iter().take(2) {
        handle(&mut n, Box::new(message));
    }
    n
}

#[derive(Clone)]
enum Prev {
    A,
    B(u8),
    C,
}

fn prev(rx: Receiver<Prev>) -> u32 { //~ NOTE consumer census: `prev` drains a channel of `Prev`; its switch gives each of its 3 variants an arm. No enumerated thread sends `Prev::C` over the calls the census resolved
    let mut n = 0;
    let mut last = Prev::C;
    for _ in 0..2 {
        match (rx.recv(), &last) {
            (Ok(Prev::A), _) => { //~ NOTE consumer census: the arm for `Prev::A` in `prev` takes it from `main::{closure#1}`
                n += 1;
                last = Prev::A;
            }
            (Ok(Prev::B(k)), _) => { //~ NOTE consumer census: the arm for `Prev::B` in `prev` takes it from `main::{closure#1}`
                n += k as u32;
                last = Prev::B(k);
            }
            (Ok(Prev::C), _) => n += 100, //~ NOTE consumer census: the arm for `Prev::C` in `prev` takes it from no enumerated thread over the calls the census resolved
            (Err(_), _) => break,
        }
    }
    n
}

enum Stamped {
    A,
    B(u8),
}

struct Stamp {
    seq: u32,
    message: Option<Stamped>,
}

fn stamp(seq: u32, message: Stamped) -> Stamp {
    let message = if let Stamped::A = message { None } else { Some(message) };
    Stamp { seq, message }
}

fn stamped(rx: Receiver<Stamped>) -> u32 { //~ NOTE consumer census: `stamped` drains a channel of `Stamped`, through `stamp` (which may drop it); its switch gives each of its 2 variants an arm
    let mut n = 0;
    for message in rx.iter().take(2) {
        let stamp = stamp(n, message);
        let Some(message) = stamp.message else {
            n += stamp.seq;
            continue;
        };
        match message {
            Stamped::A => n += 1, //~ NOTE consumer census: the arm for `Stamped::A` in `stamped` takes it from `main::{closure#2}`
            Stamped::B(k) => n += k as u32, //~ NOTE consumer census: the arm for `Stamped::B` in `stamped` takes it from `main::{closure#2}`
        }
    }
    n
}

enum Looped {
    A,
    B(u8),
}

fn looped(rx: Receiver<Looped>) {
    census_dep::Loop::new(|message| match message { //~ NOTE consumer census: `looped::{closure#0}` receives `Looped` by value from `looped`; its switch gives each of its 2 variants an arm
        Looped::A => {} //~ NOTE consumer census: the arm for `Looped::A` in `looped::{closure#0}` takes it from `main::{closure#3}`
        Looped::B(_) => {} //~ NOTE consumer census: the arm for `Looped::B` in `looped::{closure#0}` takes it from `main::{closure#3}`
    })
    .run(rx);
}

fn main() {
    let (tx, rx) = channel::<Boxed>();
    std::thread::spawn(move || {
        let _ = tx.send(Boxed::A);
        let _ = tx.send(Boxed::B(1));
    });
    let _ = boxed(rx);
    let (tx, rx) = channel::<Prev>();
    std::thread::spawn(move || {
        let _ = tx.send(Prev::A);
        let _ = tx.send(Prev::B(1));
    });
    let _ = prev(rx);
    let (tx, rx) = channel::<Stamped>();
    std::thread::spawn(move || {
        let _ = tx.send(Stamped::A);
        let _ = tx.send(Stamped::B(1));
    });
    let _ = stamped(rx);
    let (tx, rx) = channel::<Looped>();
    std::thread::spawn(move || {
        let _ = tx.send(Looped::A);
        let _ = tx.send(Looped::B(1));
    });
    looped(rx);
}

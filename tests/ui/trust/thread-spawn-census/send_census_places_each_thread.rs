//@ needs-trust-verify
//@ aux-build: census_dep.rs
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//! One thread note per thread, at the call that starts it. The whole output
//! is checked, since both defects were a note too many or too few:
//!
//! - `outer_a` and `outer_b` are generic and spawn through a generic helper.
//!   The program instantiates each once. The walk of the generic code as
//!   written is the same spawn as its one instance: two thread notes, and
//!   none for "a generic fn this crate never instantiates".
//! - `near` is one call from a dependency's spawn site and `far` three calls
//!   from the same site. Each is a thread of its own, named at its own call.

extern crate census_dep;

use std::fmt::Debug;
use std::sync::OnceLock;
use std::sync::mpsc::{Receiver, Sender, channel};

pub enum Wake {
    A,
    B,
    Pumped,
}

fn inner<F: FnOnce() + Send + 'static>(f: F) -> std::thread::JoinHandle<()> {
    std::thread::spawn(f)
}

fn outer_a<T: Debug + Send + Clone + 'static>(tx: Sender<Wake>, t: T) {
    let other = outer_b(tx.clone(), t.clone());
    inner(move || {
        let _ = (t, tx.send(Wake::A));
    })
    .join()
    .unwrap();
    other.join().unwrap();
}

fn outer_b<T: Debug + Send + 'static>(tx: Sender<Wake>, t: T) -> std::thread::JoinHandle<()> {
    inner(move || {
        let _ = (t, tx.send(Wake::B));
    })
}

static TX: OnceLock<Sender<Wake>> = OnceLock::new();

fn pump() {
    let _ = TX.get().unwrap().send(Wake::Pumped);
}

fn run(rx: Receiver<Wake>) -> u32 {
    let mut n = 0;
    while let Ok(wake) = rx.try_recv() {
        match wake {
            Wake::A => n += 1,
            Wake::B => n += 10,
            Wake::Pumped => n += 100,
        }
    }
    n
}

fn main() {
    let (tx, rx) = channel();
    let _ = TX.set(tx.clone());
    outer_a(tx, 1u8);
    let near = census_dep::spawn_it(pump);
    let far = census_dep::spawn_via(pump);
    near.join().unwrap();
    far.join().unwrap();
    let _ = run(rx);
}

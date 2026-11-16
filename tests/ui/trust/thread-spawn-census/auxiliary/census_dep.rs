//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency with generic helpers, for
//! `send_census_follows_a_dependencys_generic_code.rs`.

use std::sync::mpsc::Sender;
use std::thread::JoinHandle;

pub enum Reply {
    Done,
    Failed,
}

pub fn spawn_named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> JoinHandle<()> {
    std::thread::Builder::new().name(name.to_owned()).spawn(f).expect("spawn")
}

pub fn post<T>(tx: &Sender<T>, message: T) {
    let _ = tx.send(message);
}

pub fn post_all<T>(tx: &Sender<T>, messages: Vec<T>) {
    for message in messages {
        let _ = tx.send(message);
    }
}

pub fn post_default<T: Default>(tx: &Sender<T>) {
    let _ = tx.send(T::default());
}

pub fn reply_from<T: Into<Reply>>(tx: &Sender<Reply>, from: T) {
    let _ = tx.send(from.into());
}

/// One spawn site, reached directly and through two more generic fns.
pub fn spawn_it<F: FnOnce() + Send + 'static>(f: F) -> JoinHandle<()> {
    std::thread::spawn(f)
}

fn spawn_mid<F: FnOnce() + Send + 'static>(f: F) -> JoinHandle<()> {
    spawn_it(f)
}

pub fn spawn_via<F: FnOnce() + Send + 'static>(f: F) -> JoinHandle<()> {
    spawn_mid(f)
}

/// A run loop that is given its handler first and its receiver later.
pub struct Loop<F> {
    on: F,
}

impl<F> Loop<F> {
    pub fn new(on: F) -> Self {
        Loop { on }
    }

    pub fn run<T>(mut self, rx: std::sync::mpsc::Receiver<T>)
    where
        F: FnMut(T),
    {
        for event in rx {
            (self.on)(event);
        }
    }
}

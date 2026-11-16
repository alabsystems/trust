//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Both sides of the Arc match are read at the instance that runs, and a
//! cell is what can still change:
//!
//! - `spawn_with` is generic over the cell: the thread it starts captures
//!   `Arc<Slots<T>>`, which is `Arc<Slots<u8>>` at the instance `main` makes.
//! - `Bus<S>::on_wake` runs on a generic `self`: its `Arc<Slots<S>>` field is
//!   the same `Arc<Slots<u8>>` there.
//! - `MIXED` is set once and holds both a lock and an atomic: neither kind
//!   alone, so it is listed as other interior mutability.
//! - `PROXY` is a set-once sender: the channel is the model's FIFO, and a
//!   sender holds no cell, whatever the message carries.
//! - `Hook` names `App` only in a callable's signature: an `Arc<Hook>` does
//!   not hold the `App` the consumer runs on.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc::{Sender, channel};
use std::sync::{Arc, Mutex, OnceLock};

struct Slots<T> {
    count: AtomicU32,
    last: Mutex<Option<T>>,
}

struct Mixed {
    lock: Mutex<u8>,
    hits: AtomicU32,
}

static MIXED: OnceLock<Mixed> = OnceLock::new();
static PROXY: OnceLock<Sender<Wake>> = OnceLock::new();

enum Wake {
    Tick,
    Carry(Arc<Mutex<u8>>),
}

struct Hook {
    call: Box<dyn Fn(&mut Bus<u8>) + Send + Sync>,
}

struct Bus<S> {
    slots: Arc<Slots<S>>,
    n: u32,
}

impl<S> Bus<S> {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Tick => {
                self.n += self.slots.count.load(Ordering::Relaxed);
                if let Some(mixed) = MIXED.get() {
                    self.n += mixed.hits.load(Ordering::Relaxed);
                }
                let _ = PROXY.get();
            }
            Wake::Carry(_) => self.n += 1,
        }
    }
}

fn spawn_with<T: Send + Sync + 'static>(
    slots: Arc<Slots<T>>,
    hook: Arc<Hook>,
    tx: Sender<Wake>,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || { //~ NOTE shared-state census: this thread and the consumer `Bus::<S>::on_wake` both reach the interior-mutable static `MIXED` (`OnceLock<Mixed>`); the set-once static `PROXY` and both hold `Arc<Slots<u8>>`, matched by type
        slots.count.fetch_add(1, Ordering::Relaxed);
        let _ = &hook;
        if let Some(mixed) = MIXED.get() {
            *mixed.lock.lock().unwrap() += 1;
        }
        let _ = PROXY.get();
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Carry(Arc::new(Mutex::new(0))));
    })
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let slots = Arc::new(Slots::<u8> { count: AtomicU32::new(0), last: Mutex::new(None) });
    let hook = Arc::new(Hook { call: Box::new(|bus| bus.n += 1) });
    let _ = MIXED.set(Mixed { lock: Mutex::new(0), hits: AtomicU32::new(0) });
    let _ = PROXY.set(tx.clone());
    let sender = spawn_with(Arc::clone(&slots), Arc::clone(&hook), tx);
    let mut bus = Bus { slots, n: 0 };
    while let Ok(wake) = rx.recv() {
        bus.on_wake(wake);
    }
    (hook.call)(&mut bus);
    sender.join().unwrap();
}

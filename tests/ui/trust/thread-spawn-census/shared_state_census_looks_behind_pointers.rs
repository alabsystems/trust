//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Interior mutability behind a pointer is still shared state. A set-once
//! static counts as what it holds OR points to: `REGISTRY`, an
//! `OnceLock<Arc<Mutex<_>>>`, is locked; `SLOTS`, a `LazyLock<Vec<AtomicU32>>`,
//! is atomic; `QUARANTINE`, a `OnceLock<&'static Quarantine>` whose target has
//! a `Mutex`, is locked; only `NAME`, a `OnceLock<String>`, is set once. An
//! `Arc<Slots>` whose atomics sit in a `Vec` is a cell. The worker's closure
//! is bound to a variable before it is spawned (it is then entered through a
//! shim): its captures count all the same. The consumer's `self` is generic
//! in a field that names no cell: its other fields are still searched. A
//! boxed callable that only NAMES an `Arc` (`Box<dyn Fn() -> Arc<Ghost>>`)
//! holds none. A thread that holds an `Arc` of the very type the consumer
//! runs on (`Arc<Mutex<Tally>>`, `Tally::on_wake`) shares that.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::mpsc::channel;
use std::sync::{Arc, LazyLock, Mutex, OnceLock};

struct Quarantine {
    entries: Mutex<Vec<u8>>,
}

static REGISTRY: OnceLock<Arc<Mutex<Vec<u8>>>> = OnceLock::new();
static SLOTS: LazyLock<Vec<AtomicU32>> = LazyLock::new(|| vec![AtomicU32::new(0)]);
static QUARANTINE: OnceLock<&'static Quarantine> = OnceLock::new();
static NAME: OnceLock<String> = OnceLock::new();

struct Slots {
    cells: Vec<AtomicU32>,
}

struct Ghost {
    hits: AtomicU32,
}

struct App<S> {
    slots: Arc<Slots>,
    make: Box<dyn Fn() -> Arc<Ghost>>,
    sink: S,
    n: u32,
}

#[derive(Clone, Copy)]
enum Wake {
    Tick,
    Stop,
}

impl<S> App<S> {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Tick => {
                let registry = REGISTRY.get().map_or(0, |all| all.lock().unwrap().len());
                let quarantined = QUARANTINE.get().map_or(0, |q| q.entries.lock().unwrap().len());
                self.n += SLOTS[0].load(Ordering::Relaxed) + registry as u32 + quarantined as u32;
            }
            Wake::Stop => {
                self.n += self.slots.cells[0].load(Ordering::Relaxed)
                    + (self.make)().hits.load(Ordering::Relaxed)
                    + NAME.get().map_or(0, |name| name.len() as u32);
            }
        }
    }
}

struct Tally {
    n: u32,
}

impl Tally {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Tick => self.n += 1,
            Wake::Stop => self.n += 2,
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let slots = Arc::new(Slots { cells: vec![AtomicU32::new(0)] });
    let tally = Arc::new(Mutex::new(Tally { n: 0 }));
    let ghost = Arc::new(Ghost { hits: AtomicU32::new(0) });
    let (theirs, counted, unused) = (Arc::clone(&slots), Arc::clone(&tally), Arc::clone(&ghost));
    let worker = move || {
        let _ = NAME.set(String::from("worker"));
        let _ = REGISTRY.set(Arc::new(Mutex::new(Vec::new())));
        let _ = QUARANTINE.set(Box::leak(Box::new(Quarantine { entries: Mutex::new(Vec::new()) })));
        SLOTS[0].store(1, Ordering::Relaxed);
        theirs.cells[0].store(1, Ordering::Relaxed);
        counted.lock().unwrap().n += 1;
        unused.hits.store(1, Ordering::Relaxed);
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Stop);
    };
    //~v NOTE shared-state census: this thread and the consumer `Tally::on_wake` share `Arc<std::sync::Mutex<Tally>>` (the consumer runs on the `Tally` in it), matched by type
    let _worker = std::thread::spawn(worker); //~ NOTE shared-state census: this thread and the consumer `App::<S>::on_wake` both reach the atomic static `SLOTS`; the locked statics `QUARANTINE` and `REGISTRY`; the set-once static `NAME` and both hold `Arc<Slots>`, matched by type
    let mut app =
        App { slots, make: Box::new(|| Arc::new(Ghost { hits: AtomicU32::new(0) })), sink: 0u8, n: 0 };
    while let Ok(wake) = rx.recv() {
        tally.lock().unwrap().on_wake(wake);
        app.on_wake(wake);
    }
    let _ = (app.n, app.sink);
}

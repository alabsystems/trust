//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! How a shared static synchronizes is read off the parts of it that can
//! change, however it is spelled. One cell, several spellings, and each is
//! filed with its kind: a newtype of an atomic and an `Option` of one are
//! atomic, bare or inside a `OnceLock`; an `Option`, a tuple and a `Vec` of
//! `Mutex`es inside a set-once cell are locked. (An `Option` around a cell
//! was once the part itself, and filed as "interior-mutable" with its type.)

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::mpsc::channel;
use std::sync::{LazyLock, Mutex, OnceLock};

struct Flag(AtomicBool);

static NEWTYPE: Flag = Flag(AtomicBool::new(false));
static NEWTYPE_ONCE: OnceLock<Flag> = OnceLock::new();
static OPT_ATOMIC: Option<AtomicU32> = Some(AtomicU32::new(0));
static OPT_ATOMIC_ONCE: OnceLock<Option<AtomicU32>> = OnceLock::new();
static OPT_MUTEX_LAZY: LazyLock<Option<Mutex<u8>>> = LazyLock::new(|| Some(Mutex::new(0)));
static TUP_MUTEX_ONCE: OnceLock<(Mutex<u8>, u8)> = OnceLock::new();
static VEC_MUTEX_LAZY: LazyLock<Vec<Mutex<u8>>> = LazyLock::new(Vec::new);

enum Wake {
    Tick,
    Stop,
}

fn touch() -> u32 {
    NEWTYPE.0.store(true, Ordering::Relaxed);
    NEWTYPE_ONCE.get_or_init(|| Flag(AtomicBool::new(false))).0.store(true, Ordering::Relaxed);
    if let Some(atomic) = &OPT_ATOMIC {
        atomic.store(1, Ordering::Relaxed);
    }
    if let Some(atomic) = OPT_ATOMIC_ONCE.get_or_init(|| Some(AtomicU32::new(0))) {
        atomic.store(1, Ordering::Relaxed);
    }
    if let Some(mutex) = &*OPT_MUTEX_LAZY {
        *mutex.lock().unwrap() += 1;
    }
    *TUP_MUTEX_ONCE.get_or_init(|| (Mutex::new(0), 0)).0.lock().unwrap() += 1;
    VEC_MUTEX_LAZY.len() as u32
}

fn handle(wake: Wake) -> u32 {
    match wake {
        Wake::Tick => touch(),
        Wake::Stop => 0,
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || { //~ NOTE shared-state census: this thread and the consumer `handle` both reach the atomic statics `NEWTYPE`, `NEWTYPE_ONCE`, `OPT_ATOMIC` and `OPT_ATOMIC_ONCE`; the locked statics `OPT_MUTEX_LAZY`, `TUP_MUTEX_ONCE` and `VEC_MUTEX_LAZY`
        touch();
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Stop);
    });
    while let Ok(wake) = rx.recv() {
        handle(wake);
    }
    sender.join().unwrap();
}

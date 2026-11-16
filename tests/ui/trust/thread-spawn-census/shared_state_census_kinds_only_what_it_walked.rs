//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A cell's kind is read off every part of it that can change, or it is not
//! read at all.
//!
//! `REG` has sixteen locks and, after them, an atomic flag both threads store
//! to with no lock held. The walk for parts takes sixteen: once it called the
//! static "locked" on those alone. A walk that stopped short decides no kind.
//!
//! `DEEP` keeps an atomic eighteen structs down, behind one wrapper used at
//! two shapes in turn (`Own<S>`, `Own<Vec<S>>`). The walk's guard against a
//! definition that keeps coming back LARGER once counted every second step as
//! growth, stopped at the ninth, and called the static "set-once": the one
//! kind that needs no ruling. A definition that comes back at two sizes in
//! turn does not grow.

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::mpsc::channel;
use std::sync::{Arc, Mutex, OnceLock};

struct Registry {
    m0: Mutex<Vec<u8>>,
    m1: Mutex<String>,
    m2: Mutex<Option<u32>>,
    m3: Mutex<Vec<String>>,
    m4: Mutex<u64>,
    m5: Mutex<(u32, u32)>,
    m6: Mutex<Vec<u32>>,
    m7: Mutex<Option<String>>,
    m8: Mutex<[u8; 4]>,
    m9: Mutex<Vec<(u32, String)>>,
    m10: Mutex<bool>,
    m11: Mutex<u8>,
    m12: Mutex<i64>,
    m13: Mutex<Option<Vec<u8>>>,
    m14: Mutex<Vec<u64>>,
    m15: Mutex<char>,
    live: AtomicBool,
}

static REG: Registry = Registry {
    m0: Mutex::new(Vec::new()),
    m1: Mutex::new(String::new()),
    m2: Mutex::new(None),
    m3: Mutex::new(Vec::new()),
    m4: Mutex::new(0),
    m5: Mutex::new((0, 0)),
    m6: Mutex::new(Vec::new()),
    m7: Mutex::new(None),
    m8: Mutex::new([0; 4]),
    m9: Mutex::new(Vec::new()),
    m10: Mutex::new(false),
    m11: Mutex::new(0),
    m12: Mutex::new(0),
    m13: Mutex::new(None),
    m14: Mutex::new(Vec::new()),
    m15: Mutex::new('a'),
    live: AtomicBool::new(false),
};

struct Own<T> {
    inner: Option<Box<T>>,
}

macro_rules! chain {
    ($($this:ident => $next:ty,)*) => {
        $(struct $this { pad: u8, next: Own<$next> })*
    };
}

chain! {
    S0 => S1, S1 => Vec<S2>, S2 => S3, S3 => Vec<S4>, S4 => S5, S5 => Vec<S6>,
    S6 => S7, S7 => Vec<S8>, S8 => S9, S9 => Vec<S10>, S10 => S11, S11 => Vec<S12>,
    S12 => S13, S13 => Vec<S14>, S14 => S15, S15 => Vec<S16>, S16 => S17, S17 => Vec<S18>,
}

struct S18 {
    hits: AtomicU32,
}

static DEEP: OnceLock<S0> = OnceLock::new();

fn s0() -> S0 {
    S0 { pad: 0, next: Own { inner: None } }
}

enum Wake {
    Tick,
    Stop,
}

struct App {
    n: u32,
    shared: Arc<S0>,
}

impl App {
    fn on_wake(&mut self, wake: Wake) -> bool {
        match wake {
            Wake::Tick => {
                self.n += 1;
                REG.live.store(true, Ordering::Relaxed);
                let _ = DEEP.get().is_some();
                let _ = &self.shared;
                true
            }
            Wake::Stop => false,
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let shared: Arc<S0> = Arc::new(s0());
    let theirs = shared.clone();
    let _ = DEEP.set(s0());
    let sender = std::thread::spawn(move || { //~ NOTE shared-state census: this thread and the consumer `App::on_wake` both reach the atomic static `DEEP`; the interior-mutable static `REG` (`Registry`) and both hold `Arc<S0>`, matched by type
        REG.live.store(false, Ordering::Relaxed);
        REG.m0.lock().unwrap().push(1);
        let _ = DEEP.get().is_some();
        let _ = &theirs;
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Stop);
    });
    let mut app = App { n: 0, shared };
    while let Ok(wake) = rx.recv() {
        if !app.on_wake(wake) {
            break;
        }
    }
    sender.join().unwrap();
}

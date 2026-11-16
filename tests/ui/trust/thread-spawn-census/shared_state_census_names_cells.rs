//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Temporal P3, the shared-state census (after the consumer census, same
//! flag): the cells a consumer and another thread can both reach, which a
//! model may interleave only if they publish no data. `REPOST` is a static
//! atomic the ticker sets and the consumer swaps, as aterm's
//! `REPOST_AFTER_COMMIT` is; `Shared` is an `Arc` of a `Mutex` the filler
//! captures and the consumer's `self` holds, matched by type, as aterm's
//! `HarnessHost.shared` is. The note groups statics by how they synchronize:
//! `ID` is set once, and `QUEUE`, a `LazyLock` of a `Mutex`, is locked: a
//! set-once cell counts as what it holds when that can still change. `LIMIT`
//! has no interior mutability, so it is no cell; an
//! `Arc<AtomicBool>` names no type of the program, so matching it by type would
//! say nothing; `Wake::Handoff` carries an `Arc<Shared>`, but a payload goes
//! in the channel, so the ticker's `Sender<Wake>` holds no cell; and `main`
//! runs the consumer, so it is not named.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::channel;
use std::sync::{Arc, LazyLock, Mutex, OnceLock};

static REPOST: AtomicBool = AtomicBool::new(false);
static LIMIT: u32 = 3;
static ID: OnceLock<String> = OnceLock::new();
static QUEUE: LazyLock<Mutex<Vec<u8>>> = LazyLock::new(|| Mutex::new(Vec::new()));

struct Shared {
    queue: Mutex<Vec<u8>>,
}

struct App {
    shared: Arc<Shared>,
    stop: Arc<AtomicBool>,
    seen: u32,
}

enum Wake {
    Tick,
    Stop,
    Handoff(Arc<Shared>),
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Tick => {
                if REPOST.swap(false, Ordering::Relaxed) && ID.get().is_some() {
                    self.seen += LIMIT + QUEUE.lock().unwrap().len() as u32;
                }
            }
            Wake::Stop => self.shared.queue.lock().unwrap().clear(),
            Wake::Handoff(shared) => self.shared = shared,
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let shared = Arc::new(Shared { queue: Mutex::new(Vec::new()) });
    let stop = Arc::new(AtomicBool::new(false));
    let mut app = App { shared: Arc::clone(&shared), stop: Arc::clone(&stop), seen: 0 };
    let ticker = tx.clone();
    let _tick = std::thread::spawn(move || { //~ NOTE shared-state census: this thread and the consumer `App::on_wake` both reach the atomic static `REPOST`; the locked static `QUEUE`; the set-once static `ID`
        let _ = ID.set(String::from("tick"));
        REPOST.store(true, Ordering::Relaxed);
        QUEUE.lock().unwrap().push(1);
        let _ = ticker.send(Wake::Tick);
    });
    let _fill = std::thread::spawn(move || { //~ NOTE shared-state census: this thread and the consumer `App::on_wake` both hold
        shared.queue.lock().unwrap().push(1);
        let _ = tx.send(Wake::Stop);
    });
    let _alone = std::thread::spawn(move || {
        let _ = LIMIT + 1;
        stop.store(true, Ordering::Relaxed);
    });
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = app.stop.load(Ordering::Relaxed);
}

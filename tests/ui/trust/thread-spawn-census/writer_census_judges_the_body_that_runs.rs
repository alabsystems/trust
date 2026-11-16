//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-writer-census=config.harness.inner
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=config.harness.inner
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A site is judged by the code that runs there and the type it runs on:
//!
//! - `Slot<T>::set` is generic code that writes at a place on the path: a
//!   write of the field where it runs on the path's `Slot<Policy>`, and no
//!   write of it where it runs on `Slot<String>` (the arm for `Label`).
//! - `self.config += 1` names a std trait's method and runs the local impl,
//!   which writes a sibling field: nothing is lent, and no site.
//! - `peek` is generic and only reads through its pointer: no writer.
//! - `put` hands a raw pointer it was given straight to `ptr::write`: a site.
//! - `drain` is a second consumer, called from an arm of the first: the write
//!   in `adopt` below it is reached from both.
//! - The arm for `Replay` hands the consumer other messages of the same type
//!   (it calls `on_wake` again for each deferred one). The innermost dispatch
//!   decides: no write is reached "from the arm for `Replay`".

use std::ops::AddAssign;
use std::sync::mpsc::{Receiver, channel};

#[derive(Clone, Copy, Default)]
struct Policy(u8);

#[derive(Default)]
struct Slot<T> {
    inner: T,
}

impl<T> Slot<T> {
    fn set(&mut self, value: T) {
        self.inner = value; //~ NOTE writer census: this writes `App.config.harness.inner`; reached from the arm for `Wake::Observed` in `App::on_wake`
    }
}

#[derive(Default)]
struct Config {
    harness: Slot<Policy>,
    theme: u8,
}

impl AddAssign<u8> for Config {
    fn add_assign(&mut self, by: u8) {
        self.theme += by;
    }
}

fn peek<T>(value: &mut T) -> usize {
    std::mem::size_of_val(value)
}

unsafe fn put(slot: *mut Slot<Policy>, policy: Policy) {
    unsafe { slot.write(Slot { inner: policy }) } //~ NOTE a `&mut` reaching `App.config.harness.inner`; reached from the arm for `Wake::Raw` in `App::on_wake`
}

enum Reply {
    Policy(Policy),
    Idle,
}

enum Wake {
    Observed(Policy),
    Label(String),
    Bump,
    Peek,
    Raw,
    Drain,
    Replay,
}

struct App {
    config: Config,
    label: Slot<String>,
    replies: Receiver<Reply>,
    deferred: Vec<Wake>,
    seen: usize,
}

impl App {
    fn adopt(&mut self, policy: Policy) {
        self.config.harness.inner = policy; //~ NOTE writer census: this writes `App.config.harness.inner`; reached from the arm for `Reply::Policy` in `App::drain` and the arm for `Wake::Drain` in `App::on_wake`
    }

    fn drain(&mut self) { //~ NOTE writer census: `App.config.harness.inner` may be written at 3 site(s), from the arm for `Reply::Policy` in `App::drain`. 1 other consumer(s) run on `App`, each with its own summary: `App::on_wake`
        while let Ok(reply) = self.replies.try_recv() {
            match reply {
                Reply::Policy(policy) => self.adopt(policy),
                Reply::Idle => self.seen += 1,
            }
        }
    }

    fn on_wake(&mut self, wake: Wake) { //~ NOTE writer census: `App.config.harness.inner` may be written at 3 site(s), from the 3 arms for `Wake::Observed`, `Wake::Raw` and `Wake::Drain` in `App::on_wake`
        match wake {
            Wake::Observed(policy) => self.config.harness.set(policy),
            Wake::Label(label) => self.label.set(label),
            Wake::Bump => self.config += 1,
            Wake::Peek => self.seen += peek(&mut self.config),
            Wake::Raw => unsafe { put(&mut self.config.harness, Policy(7)) },
            Wake::Drain => self.drain(),
            Wake::Replay => {
                for wake in std::mem::take(&mut self.deferred) {
                    self.on_wake(wake);
                }
            }
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let (reply_tx, replies) = channel::<Reply>();
    let sender = std::thread::spawn(move || {
        let _ = reply_tx.send(Reply::Policy(Policy(1)));
        let _ = reply_tx.send(Reply::Idle);
        let _ = tx.send(Wake::Observed(Policy(2)));
        let _ = tx.send(Wake::Label(String::new()));
        let _ = tx.send(Wake::Bump);
        let _ = tx.send(Wake::Peek);
        let _ = tx.send(Wake::Raw);
        let _ = tx.send(Wake::Drain);
        let _ = tx.send(Wake::Replay);
    });
    let mut app = App {
        config: Config::default(),
        label: Slot::default(),
        replies,
        deferred: Vec::new(),
        seen: 0,
    };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    sender.join().unwrap();
}

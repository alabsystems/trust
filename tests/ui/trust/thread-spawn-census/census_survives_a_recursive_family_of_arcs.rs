//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! `A`, `B` and `C` name each other at ever larger instantiations, in several
//! directions at once, and the family holds `Arc`s on the way
//! (`Arc<Mutex<T>>`, `Arc<A<U>>`). A walk of what such a type holds runs to
//! its bound and meets thousands of distinct `Arc`s. The shared-state census
//! asked a question of each one with a walk of its own (does it hold a cell?
//! does it hold the type the consumer runs on?): three minutes and 8 GB for
//! this program, where it is two seconds now that one walk answers for all
//! of them. A test that hangs here is that regression.

use std::mem::ManuallyDrop;
use std::sync::mpsc::channel;
use std::sync::{Arc, Mutex, OnceLock};

struct Tag {
    n: Mutex<u32>,
}

struct A<T: 'static> {
    v: T,
    b: Option<&'static B<(T, T)>>,
    c: *const C<T, Vec<T>>,
    cell: Arc<Tag>,
    p: Option<&'static A<Option<T>>>,
}

struct B<T: 'static> {
    v: T,
    a: Option<ManuallyDrop<Box<A<Option<T>>>>>,
    c: *mut C<[T; 2], T>,
    f: Option<fn(B<(T,)>) -> A<Box<T>>>,
}

struct C<T: 'static, U: 'static> {
    t: T,
    u: U,
    a: Option<&'static A<(U, T)>>,
    b: *const B<fn(T) -> U>,
    c: Option<&'static C<U, (T, U)>>,
    d: Option<&'static C<Arc<Mutex<T>>, Arc<A<U>>>>,
}

unsafe impl<T> Send for A<T> {}
unsafe impl<T> Sync for A<T> {}

static ROOT: OnceLock<A<u8>> = OnceLock::new();

enum Wake {
    Tick,
    Stop,
    Carry(Box<A<u16>>),
}

struct App {
    a: A<u8>,
    b: B<u8>,
    c: C<u8, u16>,
    n: u32,
}

impl App {
    fn on_wake(&mut self, wake: Wake) { //~ NOTE consumer census: `App::on_wake` receives `Wake` by value from `main`; its switch gives each of its 3 variants an arm
        match wake {
            Wake::Tick => {
                self.n += 1;
                let _ = ROOT.get();
            }
            Wake::Stop => self.n = *self.a.cell.n.lock().unwrap(),
            Wake::Carry(a) => self.n = a.v as u32,
        }
    }
}

fn a<T>(v: T, cell: &Arc<Tag>) -> A<T> {
    A { v, b: None, c: std::ptr::null(), cell: Arc::clone(cell), p: None }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let cell = Arc::new(Tag { n: Mutex::new(0) });
    let theirs = a(0u8, &cell);
    let carried = a(0u16, &cell);
    let sender = std::thread::spawn(move || {
        *theirs.cell.n.lock().unwrap() += 1;
        let _ = ROOT.get();
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Stop);
        let _ = tx.send(Wake::Carry(Box::new(carried)));
    });
    let mut app = App {
        a: a(0u8, &cell),
        b: B { v: 0, a: None, c: std::ptr::null_mut(), f: None },
        c: C { t: 0, u: 0, a: None, b: std::ptr::null(), c: None, d: None },
        n: 0,
    };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    sender.join().unwrap();
}

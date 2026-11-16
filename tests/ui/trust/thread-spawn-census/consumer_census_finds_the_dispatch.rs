//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The consumer census finds a drain loop written as `for wake in rx` (MIR
//! calls `IntoIterator::into_iter`, not an inherent method), and a consumer
//! that is a method of a LOCAL trait (the call names the trait's method; the
//! census resolves it to the impl). "Its switch" is the switch over the message
//! the body holds: `handle` also matches on `self.last`, a field of the same
//! type, and that switch says nothing about the message being dispatched. An
//! or-pattern arm takes each of its variants.

use std::sync::mpsc::{Receiver, channel};

#[derive(Clone, Copy)]
enum Wake {
    A,
    B,
    C,
    D,
}

trait Handler {
    fn handle(&mut self, wake: Wake);
}

struct App {
    last: Wake,
    n: u32,
}

impl Handler for App {
    fn handle(&mut self, wake: Wake) { //~ NOTE consumer census: `<App as Handler>::handle` receives `Wake` by value from `pump`; its switch gives 3 of its 4 variants an arm, and 1 share the catch-all (D) (1 switch(es) over another `Wake` value in this body are not counted). Sent but left to the catch-all: `Wake::D`. No enumerated thread sends `Wake::B` and `Wake::C` over the calls the census resolved
        match wake {
            Wake::A | Wake::B => self.n += 1, //~ NOTE consumer census: the arm for `Wake::A` | `Wake::B` in `<App as Handler>::handle` takes it from `main::{closure#0}`
            Wake::C => self.n += 2, //~ NOTE consumer census: the arm for `Wake::C` in `<App as Handler>::handle` takes it from no enumerated thread
            _ => self.n += 50,
        }
        match self.last {
            Wake::A => self.n += 1000,
            Wake::B => self.n += 2000,
            Wake::C => self.n += 3000,
            Wake::D => self.n += 4000,
        }
        self.last = wake;
    }
}

fn pump(app: &mut App, rx: Receiver<Wake>) {
    for wake in rx {
        app.handle(wake);
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::A);
        let _ = tx.send(Wake::D);
    });
    let mut app = App { last: Wake::A, n: 0 };
    pump(&mut app, rx);
    let _ = app.n;
}

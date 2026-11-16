//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! "The held message" is the value a body was given or received, and only
//! that value. `Relay::handle` holds `wake` and switches over three other
//! values of its type, none of which is its dispatch: the payload of a
//! `Batch`, the previous message `mem::replace` returns, and the other half
//! of a tuple. So it is no consumer. `App::handle` is one: its message passes
//! through `admit`, which hands it back (the note names it), and then through
//! a tuple with an unrelated message, which is told apart by field. `requeue`
//! is called after the dispatch with a result nobody reads, so the message
//! does not pass "through" it. `describe` is only ever given a value its
//! caller builds, so nothing hands it a message and it is no consumer,
//! however it matches. A trait's provided method is a consumer like any
//! other body (`Sink::on`).

use std::sync::mpsc::{Receiver, Sender, channel};

#[derive(Clone)]
enum Wake {
    Tick,
    Stop,
    Batch(Vec<Wake>),
}

struct Relay {
    last: Wake,
    seen: u32,
}

impl Relay {
    fn handle(&mut self, wake: Wake) {
        if let Wake::Batch(inner) = &self.last {
            for one in inner {
                match one {
                    Wake::Tick => self.seen += 1,
                    Wake::Stop => self.seen += 2,
                    Wake::Batch(_) => {}
                }
            }
        }
        let pair = (wake.clone(), self.last.clone());
        if let Wake::Stop = pair.1 {
            self.seen += 10;
        }
        match std::mem::replace(&mut self.last, wake) {
            Wake::Tick => self.seen += 100,
            Wake::Stop => self.seen += 200,
            Wake::Batch(_) => {}
        }
    }
}

struct App {
    back: Sender<Wake>,
    prev: Wake,
    n: u32,
}

fn describe(wake: Wake) -> u32 {
    match wake {
        Wake::Tick => 1,
        Wake::Stop => 2,
        Wake::Batch(_) => 3,
    }
}

impl App {
    fn admit(&mut self, wake: Wake) -> Option<Wake> {
        if self.n > 100 { None } else { Some(wake) }
    }

    fn requeue(&mut self, wake: Wake) -> Result<(), Wake> {
        self.back.send(wake).map_err(|refused| refused.0)
    }

    fn handle(&mut self, wake: Wake) { //~ NOTE consumer census: `App::handle` receives `Wake` by value from `pump`, through `App::admit` (which may drop it); its switch gives 2 of its 3 variants an arm, and 1 share the catch-all (Batch)
        let Some(wake) = self.admit(wake) else { return };
        let both = (self.prev.clone(), wake);
        match both.1 {
            Wake::Tick => self.n += describe(Wake::Stop), //~ NOTE consumer census: the arm for `Wake::Tick` in `App::handle` takes it from `main::{closure#0}`
            Wake::Stop => self.n += 2,
            other => {
                let _ = self.requeue(other);
            }
        }
    }
}

trait Sink {
    fn count(&mut self) -> &mut u32;

    fn on(&mut self, wake: Wake) { //~ NOTE consumer census: `Sink::on` receives `Wake` by value from `pump`
        match wake {
            Wake::Tick => *self.count() += 1,
            Wake::Stop => *self.count() += 2,
            Wake::Batch(_) => {}
        }
    }
}

impl Sink for App {
    fn count(&mut self) -> &mut u32 {
        &mut self.n
    }
}

fn pump(app: &mut App, relay: &mut Relay, rx: Receiver<Wake>) {
    for wake in rx {
        relay.handle(wake.clone());
        app.on(wake.clone());
        app.handle(wake);
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let back = tx.clone();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Batch(vec![Wake::Stop]));
    });
    let mut app = App { back, prev: Wake::Tick, n: 0 };
    let mut relay = Relay { last: Wake::Tick, seen: 0 };
    pump(&mut app, &mut relay, rx);
    let _ = (app.n, relay.seen);
}

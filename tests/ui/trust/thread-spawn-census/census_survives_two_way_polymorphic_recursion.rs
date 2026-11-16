//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-send-census -Ztrust-writer-census=n
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=n
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A type with TWO polymorphically recursive fields is a tree of
//! instantiations, 2^(recursion limit) of them: the census's type walks end
//! by counting how often a definition is entered again along one path, not
//! by the nesting depth alone. The same holds for several generic types that
//! name each other. The program has a consumer whose `self` holds such a
//! type, so every census walks it.

use std::sync::mpsc::channel;

struct Nest<T: 'static>(T, Option<&'static Nest<Option<T>>>, Option<&'static Nest<(T,)>>);

struct Ping<T: 'static>(T, Option<&'static Pong<(T, u8)>>, Option<&'static Pong<(T, u16)>>);
struct Pong<T: 'static>(T, Option<&'static Ping<[T; 1]>>, Option<&'static Ping<Option<T>>>);

enum Wake {
    Tick,
    Stop,
}

struct App {
    nest: Nest<u8>,
    ping: Ping<u8>,
    n: u32,
}

impl App {
    fn on_wake(&mut self, wake: Wake) { //~ NOTE consumer census: `App::on_wake` receives `Wake` by value from `main`
        match wake {
            Wake::Tick => self.n += u32::from(self.nest.0),
            Wake::Stop => self.n += u32::from(self.ping.0),
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Tick);
        let _ = tx.send(Wake::Stop);
    });
    let mut app = App { nest: Nest(0, None, None), ping: Ping(0, None, None), n: 0 };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = app.n;
}

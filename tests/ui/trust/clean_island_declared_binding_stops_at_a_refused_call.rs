//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The census does not ask rustc to resolve a call at a type nested close to
//! the recursion limit (a blanket impl there would overflow the resolver,
//! which is a fatal error and not an answer). What such a call runs is then
//! not in the graph. Here it is `Config::put::<Deep>`, which writes the bound
//! field from an undeclared arm: the binding once held. A binding in a crate
//! with a refused call is an error that says so.

#![recursion_limit = "32"]

use std::sync::mpsc::channel;

struct Config {
    harness: u8,
    theme: u8,
}

struct App {
    config: Config,
}

enum Wake {
    Observed(u8),
    Reset,
    Tick,
}

struct W<T>(T);

type Deep = W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<u8>>>>>>>>>>>>>>>>>>>>;

trait Level {
    fn level(&self) -> u8;
}

impl Level for u8 {
    fn level(&self) -> u8 {
        *self
    }
}

impl<T: Level> Level for W<T> {
    fn level(&self) -> u8 {
        self.0.level()
    }
}

fn deep(v: u8) -> Deep {
    W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(W(v))))))))))))))))))))
}

impl Config {
    fn put<T: Level>(&mut self, v: T) {
        self.harness = v.level();
    }
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(level) => self.config.put(level),
            Wake::Reset => self.config.put(deep(7)),
            Wake::Tick => self.config.theme += 1,
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Reset);
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App { config: Config { harness: 0, theme: 0 } };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    sender.join().unwrap();
}

clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding := binds "config.harness" ["Observed"] []
}
//~^^ ERROR binding `policy` cannot be checked against the code: the census did not follow

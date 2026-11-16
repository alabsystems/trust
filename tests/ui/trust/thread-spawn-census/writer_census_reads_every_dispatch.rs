//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-send-census -Ztrust-writer-census=flag
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! One body can consume two message types (`App::pump` drains a channel of
//! `Wake` and one of `Key`): the writer census reads both dispatches, so a
//! write in an arm for a `Key` is in that arm, not "outside its arms". A
//! dispatch written by a macro puts every arm's call at one span: the census
//! tells the calls apart by the fn they call, so only the arm that calls
//! `raise` reaches its write. A provided method of a trait is a consumer, and
//! the path is resolved on the type that implements the trait. Two consumers
//! then run on `App` (`App::pump` and `Quiet::hush`): each site is named once,
//! with the consumer that reaches it, and each consumer gets a summary.

use std::sync::mpsc::{Receiver, channel};

enum Wake {
    Up,
    Down,
}

enum Key {
    Enter,
    Escape,
}

struct App {
    flag: bool,
    n: u32,
}

macro_rules! dispatch {
    ($app:expr, $wake:expr, $($variant:ident => $handler:ident),*) => {
        match $wake {
            $(Wake::$variant => $app.$handler(),)*
        }
    };
}

impl App {
    fn raise(&mut self) {
        self.flag = true; //~ NOTE writer census: this writes `App.flag`; reached from the arm for `Wake::Up` in `App::pump`
    }

    fn lower(&mut self) {
        self.n += 1;
    }

    fn pump(&mut self, wakes: Receiver<Wake>, keys: Receiver<Key>) { //~ NOTE writer census: `App.flag` may be written at 4 site(s), from the arm for `Wake::Up` in `App::pump` and the arm for `Key::Escape` in `App::pump`. 1 other consumer(s) run on `App`, each with its own summary: `Quiet::hush`
        while let Ok(wake) = wakes.recv() {
            dispatch!(self, wake, Up => raise, Down => lower);
        }
        while let Ok(key) = keys.recv() {
            match key {
                Key::Enter => self.n += 1,
                Key::Escape => self.flag = false, //~ NOTE writer census: this writes `App.flag`; reached from the arm for `Key::Escape` in `App::pump`
            }
        }
    }
}

trait Quiet {
    fn flag(&mut self) -> &mut bool;

    //~v NOTE writer census: `App.flag` may be written at 4 site(s), from the arm for `Key::Escape` in `Quiet::hush`. 1 other consumer(s) run on `App`, each with its own summary: `App::pump`
    fn hush(&mut self, key: Key) { //~ NOTE consumer census: `Quiet::hush` receives `Key` by value from `main`
        match key {
            Key::Enter => {}
            Key::Escape => *self.flag() = false,
        }
    }
}

impl Quiet for App {
    fn flag(&mut self) -> &mut bool {
        &mut self.flag //~ NOTE writer census: this takes a `&mut` of `App.flag`; reached from the arm for `Key::Escape` in `Quiet::hush`
    }
}

fn main() {
    let (wake_tx, wakes) = channel::<Wake>();
    let (key_tx, keys) = channel::<Key>();
    let (late_tx, late) = channel::<Key>();
    let _sender = std::thread::spawn(move || {
        let _ = wake_tx.send(Wake::Up);
        let _ = wake_tx.send(Wake::Down);
        let _ = key_tx.send(Key::Enter);
        let _ = key_tx.send(Key::Escape);
        let _ = late_tx.send(Key::Escape);
    });
    let mut app = App { flag: false, n: 0 };
    app.pump(wakes, keys);
    while let Ok(key) = late.recv() {
        app.hush(key);
    }
    let _ = (app.flag, app.n);
}

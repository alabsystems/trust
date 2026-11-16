//@ needs-trust-verify
//@ edition: 2021
//@ revisions: off unit
//@ aux-build: binding_wraps_dep.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@[unit] compile-flags: --test
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Each module is a protocol whose binding holds, in a shape that once failed
//! it. Every module has an `App` and a `Wake` of its own, so each binding
//! names its type and its variant with their module (`peek::App.harness`,
//! `peek::Wake::Observed`). A binding that held only for want of a write
//! would warn, and no warning is expected here.
//!
//! - `peek`: an undeclared arm takes a raw pointer to the field and only
//!   READS through it, directly and with `p.read()`. (A debug-assertions
//!   build casts the pointer to an integer for its alignment check, and
//!   `read` takes a `*const` and returns no pointer: neither is the pointer
//!   leaving.)
//! - `pair`: the body holds two messages. The write is in the arm for
//!   `Observed` of the first, after a switch over the second has ended.
//! - `item`: the handler is a fn item that a local generic pump runs through
//!   `FnMut::call_mut`.
//! - `arg`: the consumer is a closure that takes the `App` as a parameter.
//! - `captured`: the consumer is a closure in the fn that owns the `App`; it
//!   captures the fields it uses, not the `App`.
//! - `tick`: a message with one variant and no payload, named in the
//!   receive's own pattern.
//! - `tagged`: a filter that returns the message inside a tuple, or drops it.
//! - `logged`: a message with one variant whose handler counts it and keeps
//!   it in a log, never reading its payload. A `Vec::push` is not a hand-off
//!   to another consumer.
//! - `receiver`: the consumer takes `self: Box<Self>`. The box it is given
//!   holds the value it runs on, and its write through it is found: a
//!   binding that held for want of a write would warn.
//! - `adapters`: undeclared arms hand closures that capture `self` to std's
//!   adapters (`filter`, `map`, `is_some_and`, `catch_unwind` around an
//!   `AssertUnwindSafe`). A closure of the crate is read on its own: handing
//!   it over lends nothing. (This is most of what aterm-gui's handler does.)
//! - `looped`: a dependency's run loop is given the `App` and wraps it in a
//!   closure for its own driver, as winit's does. The closure's body is
//!   read: it calls the handler and writes nothing.
//! - `aside`: a closure captures a pointer the arm borrowed from a SIBLING of
//!   the same type and writes through it. What the pointer is comes from
//!   what the arm made it from, not from its type.
//! - `fresh`: an undeclared arm builds a new `Config` in a `Box::new`, sets
//!   its fields and stages it in a sibling. A value under construction is
//!   nobody's field yet.
//! - `tally`: an undeclared arm sums into a local of the field's own type
//!   inside a closure. A plain variable of the parent's is the parent's,
//!   whatever its type.
//! - `branchy`: the fn that owns the `App` gives it its first value on two
//!   ways (`if .. { A } else { B }`), and declares another inside a loop. A
//!   variable's first value is not a write, on any way to it.
//! - `owned`: the job of a thread owns the `App` and, beside it, another
//!   value of a type on the path, which it writes: that one is the
//!   closure's own.
//! - `spare`: the field's type again in a sibling `Box`: a write of the spare
//!   is not a write of the field.
//! - `reads`: the consumer is a closure that captures the field by
//!   reference, writes it in its declared arm, and after the match only
//!   READS it (`println!`). A `&` reborrow of the pointer it captured cannot
//!   be written through.
//! - `boxside`: closures write through a sibling `Box<Config>`, by the box's
//!   path and through a pointer the arm borrowed out of it. A pointer loaded
//!   out of a box is to what that box holds.
//! - `inplace`: two receives matched in place as one tuple. The write is in
//!   the arm for `Observed` of the first; the second, a `Tick` there, is
//!   another message.
//! - `cloned`: a worker thread is given a clone of the `App` and writes its
//!   clone; and a closure counts on a copy of the field. A value moved or
//!   copied into a closure no consumer runs in is the closure's own.
//! - `levels`: the field keeps a boxed slice, and an undeclared arm READS an
//!   element of it. Reading the slice's length off its pointer takes the
//!   pointer nowhere.
//! - `beside`: the `App` sits in a `Session` beside a backup `Config`, and
//!   the fn that owns the session writes the backup. A field of the holder
//!   that is not the way to the `App` is a sibling.
//! - `kept`: the job of a thread owns the `App` and a value of the field's
//!   type beside it, which it hands to `mem::replace`. That one is the
//!   closure's own, also by a pointer.
//!
//! The `unit` revision is what `targo test` compiles: `peek`'s unit test
//! writes the field of its own `App`, directly and through a helper. That is
//! test code, and the binding holds.

extern crate binding_wraps_dep;

mod peek {
    pub struct App {
        pub harness: u8,
        pub seen: u8,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        pub fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => {
                    let p = &raw const self.harness;
                    self.seen = unsafe { *p };
                    let q = std::ptr::addr_of!(self.harness);
                    self.seen = unsafe { q.read() };
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = std::sync::mpsc::channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, seen: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn with_level(app: &mut App, level: u8) {
            app.harness = level;
        }

        #[test]
        fn tick_keeps_the_level() {
            let mut app = App { harness: 0, seen: 0 };
            app.harness = 2;
            with_level(&mut app, 3);
            app.on_wake(Wake::Tick);
            assert_eq!(app.seen, 3);
        }
    }
}

mod pair {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
        pub theme: u8,
    }

    pub enum Wake {
        Observed(u8),
        Prepared,
        Tick,
    }

    impl App {
        fn on_pair(&mut self, first: Wake, second: Wake) {
            match first {
                Wake::Observed(level) => {
                    match second {
                        Wake::Tick => self.theme += 1,
                        _ => {}
                    }
                    self.harness = level;
                }
                _ => {}
            }
        }
    }

    fn pump(app: &mut App, rx: Receiver<Wake>) {
        loop {
            let Ok(first) = rx.recv() else { break };
            let Ok(second) = rx.recv() else { break };
            app.on_pair(first, second)
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
            let _ = tx.send(Wake::Prepared);
        });
        let mut app = App { harness: 0, theme: 0 };
        pump(&mut app, rx);
        sender.join().unwrap();
    }
}

mod item {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Policy(u8),
        Tick,
    }

    fn pump<F: FnMut(&mut App, Wake)>(app: &mut App, rx: Receiver<Wake>, mut f: F) {
        for wake in rx {
            f(app, wake)
        }
    }

    fn on(app: &mut App, wake: Wake) {
        match wake {
            Wake::Policy(level) => app.harness = level,
            Wake::Tick => app.n += 1,
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Policy(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, n: 0 };
        pump(&mut app, rx, on);
        sender.join().unwrap();
    }
}

mod arg {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Policy(u8),
        Tick,
    }

    fn pump<F: FnMut(&mut App, Wake)>(app: &mut App, rx: Receiver<Wake>, mut f: F) {
        for wake in rx {
            f(app, wake)
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Policy(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, n: 0 };
        pump(&mut app, rx, |app, wake| match wake {
            Wake::Policy(level) => app.harness = level,
            Wake::Tick => app.n += 1,
        });
        sender.join().unwrap();
    }
}

mod captured {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Policy(u8),
        Tick,
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Policy(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, n: 0 };
        rx.iter().for_each(|wake| match wake {
            Wake::Policy(level) => app.harness = level,
            Wake::Tick => app.n += 1,
        });
        sender.join().unwrap();
    }
}

mod tick {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub level: u8,
    }

    pub enum Wake {
        Tick,
    }

    impl App {
        fn pump(&mut self, rx: Receiver<Wake>) {
            while let Ok(Wake::Tick) = rx.recv() {
                self.level += 1;
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { level: 0 };
        app.pump(rx);
        sender.join().unwrap();
    }
}

mod tagged {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        A,
        B(u8),
    }

    fn tag(seq: u32, wake: Wake) -> (u32, Option<Wake>) {
        if seq > 9 { (seq, None) } else { (seq, Some(wake)) }
    }

    impl App {
        fn on(&mut self, seq: u32, wake: Wake) {
            let (_seq, Some(wake)) = tag(seq, wake) else { return };
            match wake {
                Wake::A => self.n += 1,
                Wake::B(level) => self.harness = level,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::A);
            let _ = tx.send(Wake::B(1));
        });
        let mut app = App { harness: 0, n: 0 };
        let mut seq = 0;
        for wake in rx {
            seq += 1;
            app.on(seq, wake);
        }
        sender.join().unwrap();
    }
}

mod logged {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
        pub log: Vec<Wake>,
    }

    pub enum Wake {
        Policy(u8),
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            self.harness += 1;
            self.log.push(wake);
        }

        fn pump(&mut self, rx: Receiver<Wake>) {
            for wake in rx {
                self.on_wake(wake)
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Policy(1));
        });
        let mut app = App { harness: 0, log: Vec::new() };
        app.pump(rx);
        sender.join().unwrap();
    }
}

mod receiver {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(mut self: Box<Self>, wake: Wake) -> Box<Self> {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => self.n += 1,
            }
            self
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = Box::new(App { harness: 0, n: 0 });
        while let Ok(wake) = rx.recv() {
            app = app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod adapters {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub items: Vec<u8>,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Count,
        Guarded,
    }

    impl App {
        fn wants(&mut self, item: u8) -> bool {
            self.n += 1;
            item > self.harness
        }

        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Count => {
                    let items = std::mem::take(&mut self.items);
                    let kept: Vec<u8> = items.into_iter().filter(|item| self.wants(*item)).collect();
                    let first = kept.first().copied().map(|item| self.wants(item));
                    self.n += first.is_some_and(|wanted| wanted && self.wants(0)) as u32;
                    self.items = kept;
                }
                Wake::Guarded => {
                    let _ = catch_unwind(AssertUnwindSafe(|| self.wants(1)));
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Count);
            let _ = tx.send(Wake::Guarded);
        });
        let mut app = App { harness: 0, items: vec![1, 2], n: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod looped {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl binding_wraps_dep::Handler<Wake> for App {
        fn user_event(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => self.n += 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, n: 0 };
        binding_wraps_dep::run_app(&mut app, rx);
        sender.join().unwrap();
    }
}

mod aside {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
    }

    pub enum Wake {
        Harness,
        Spare,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Harness => self.config.harness = 1,
                Wake::Spare => {
                    let spare = &mut self.spare;
                    let mut set = || spare.harness = 2;
                    set();
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::Spare);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod fresh {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub staged: Option<Box<Config>>,
    }

    pub enum Wake {
        Harness,
        Stage,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Harness => self.config.harness = 1,
                Wake::Stage => {
                    let mut next = Box::new(Config::default());
                    next.harness = 9;
                    next.theme = 2;
                    self.staged = Some(next);
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::Stage);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod tally {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub items: Vec<u8>,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Sum,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Sum => {
                    let mut sum = 0u8;
                    self.items.iter().for_each(|item| sum = sum.wrapping_add(*item));
                    self.n += sum as u32;
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Sum);
        });
        let mut app = App { harness: 0, items: vec![1, 2], n: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod branchy {
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => self.n += 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut first = if std::env::args().count() > 1 {
            App { harness: 1, n: 0 }
        } else {
            App { harness: 0, n: 0 }
        };
        if let Ok(wake) = rx.recv() {
            first.on_wake(wake);
        }
        for _round in 0..2 {
            let mut app = App { harness: 0, n: 0 };
            while let Ok(wake) = rx.try_recv() {
                app.on_wake(wake);
            }
        }
        sender.join().unwrap();
    }
}

mod owned {
    use std::sync::mpsc::channel;

    #[derive(Clone, Copy, Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = level,
                Wake::Tick => self.config.theme += 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let mut app = App::default();
        let mut last = Config::default();
        let worker = std::thread::spawn(move || {
            for wake in rx {
                app.on_wake(wake);
                last.harness = app.config.harness;
            }
            last.theme
        });
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Tick);
        drop(tx);
        let _ = worker.join().unwrap();
    }
}

mod reads {
    use std::sync::mpsc::channel;

    #[derive(Default, Debug)]
    pub struct App {
        pub harness: u8,
        pub theme: u8,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        rx.iter().for_each(|wake| {
            match wake {
                Wake::Observed(p) => app.harness = p,
                Wake::Tick => app.theme += 1,
            }
            println!("harness: {:?}", app.harness);
        });
        sender.join().unwrap();
    }
}

mod boxside {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub boxed: Box<Config>,
    }

    pub enum Wake {
        Harness,
        Path,
        Pointer,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Harness => self.config.harness = 1,
                Wake::Path => {
                    let mut set = || self.boxed.harness = 2;
                    set();
                }
                Wake::Pointer => {
                    let boxed = &mut self.boxed;
                    let mut set = |h: u8| boxed.harness = h;
                    set(3);
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::Path);
            let _ = tx.send(Wake::Pointer);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod inplace {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct App {
        pub harness: u8,
        pub ticks: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
        Swap,
    }

    impl App {
        pub fn pump(&mut self, rx: &std::sync::mpsc::Receiver<Wake>) {
            loop {
                match (rx.recv(), rx.recv()) {
                    (Ok(Wake::Observed(p)), Ok(Wake::Tick)) => self.harness = p,
                    (Ok(_), Ok(_)) => self.ticks += 1,
                    _ => break,
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
            let _ = tx.send(Wake::Swap);
            let _ = tx.send(Wake::Swap);
        });
        let mut app = App::default();
        app.pump(&rx);
        sender.join().unwrap();
    }
}

mod cloned {
    use std::sync::mpsc::channel;

    #[derive(Clone, Default)]
    pub struct App {
        pub harness: u8,
        pub ticks: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => {
                    let mut level = self.harness;
                    let mut bump = move || {
                        level += 1;
                        level
                    };
                    self.ticks += u32::from(bump());
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        let mut mine = app.clone();
        let worker = std::thread::spawn(move || {
            mine.harness = 7;
            mine.harness
        });
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        worker.join().unwrap();
        sender.join().unwrap();
    }
}

mod levels {
    use std::sync::mpsc::channel;

    pub struct Policy {
        pub levels: Box<[u8]>,
    }

    pub struct App {
        pub harness: Policy,
        pub seen: u8,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = Policy { levels: Box::new([level]) },
                Wake::Tick => self.seen = self.harness.levels[0],
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: Policy { levels: Box::new([0]) }, seen: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod beside {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
    }

    #[derive(Default)]
    pub struct Session {
        pub app: App,
        pub backup: Config,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = level,
                Wake::Tick => self.config.theme += 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut session = Session::default();
        while let Ok(wake) = rx.recv() {
            session.app.on_wake(wake);
            session.backup.harness = 9;
        }
        sender.join().unwrap();
    }
}

mod kept {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct App {
        pub harness: u8,
        pub ticks: u8,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => self.ticks += 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        let mut last = 0u8;
        let worker = std::thread::spawn(move || {
            let mut changes = 0;
            while let Ok(wake) = rx.recv() {
                app.on_wake(wake);
                if std::mem::replace(&mut last, app.ticks) != app.ticks {
                    changes += 1;
                }
            }
            changes
        });
        worker.join().unwrap();
        sender.join().unwrap();
    }
}

mod spare {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u16,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub spare: Box<Config>,
    }

    pub enum Wake {
        Take,
        Assign,
        SpareHarness,
        Harness,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Take => {
                    let _ = std::mem::take(&mut *self.spare);
                }
                Wake::Assign => *self.spare = Config { harness: 5, theme: 5 },
                Wake::SpareHarness => self.spare.harness = 6,
                Wake::Harness => self.config.harness = 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Take);
            let _ = tx.send(Wake::Assign);
            let _ = tx.send(Wake::SpareHarness);
            let _ = tx.send(Wake::Harness);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

fn main() {
    peek::run();
    pair::run();
    item::run();
    arg::run();
    captured::run();
    tick::run();
    tagged::run();
    logged::run();
    receiver::run();
    adapters::run();
    looped::run();
    aside::run();
    fresh::run();
    tally::run();
    branchy::run();
    owned::run();
    reads::run();
    boxside::run();
    inplace::run();
    cloned::run();
    levels::run();
    beside::run();
    kept::run();
    spare::run();
}

clean {
    import Trust.Binding
    namespace Shapes
    open Trust.Protocol
    def peek : Trust.Protocol.Binding := binds "peek::App.harness" ["peek::Wake::Observed"] []
    def pair : Trust.Protocol.Binding := binds "pair::App.harness" ["pair::Wake::Observed"] []
    def item : Trust.Protocol.Binding := binds "item::App.harness" ["item::Wake::Policy"] []
    def arg : Trust.Protocol.Binding := binds "arg::App.harness" ["arg::Wake::Policy"] []
    def captured : Trust.Protocol.Binding := binds "captured::App.harness" ["captured::Wake::Policy"] []
    def tick : Trust.Protocol.Binding := binds "tick::App.level" ["tick::Wake::Tick"] []
    def tagged : Trust.Protocol.Binding := binds "tagged::App.harness" ["tagged::Wake::B"] []
    def logged : Trust.Protocol.Binding := binds "logged::App.harness" ["logged::Wake::Policy"] []
    def receiver : Trust.Protocol.Binding := binds "receiver::App.harness" ["receiver::Wake::Observed"] []
    def adapters : Trust.Protocol.Binding := binds "adapters::App.harness" ["adapters::Wake::Observed"] []
    def looped : Trust.Protocol.Binding := binds "looped::App.harness" ["looped::Wake::Observed"] []
    def aside : Trust.Protocol.Binding := binds "aside::App.config.harness" ["aside::Wake::Harness"] []
    def fresh : Trust.Protocol.Binding := binds "fresh::App.config.harness" ["fresh::Wake::Harness"] []
    def tally : Trust.Protocol.Binding := binds "tally::App.harness" ["tally::Wake::Observed"] []
    def branchy : Trust.Protocol.Binding := binds "branchy::App.harness" ["branchy::Wake::Observed"] []
    def owned : Trust.Protocol.Binding := binds "owned::App.config.harness" ["owned::Wake::Observed"] []
    def reads : Trust.Protocol.Binding := binds "reads::App.harness" ["reads::Wake::Observed"] []
    def boxside : Trust.Protocol.Binding := binds "boxside::App.config.harness" ["boxside::Wake::Harness"] []
    def inplace : Trust.Protocol.Binding := binds "inplace::App.harness" ["inplace::Wake::Observed"] []
    def cloned : Trust.Protocol.Binding := binds "cloned::App.harness" ["cloned::Wake::Observed"] []
    def levels : Trust.Protocol.Binding := binds "levels::App.harness" ["levels::Wake::Observed"] []
    def beside : Trust.Protocol.Binding := binds "beside::App.config.harness" ["beside::Wake::Observed"] []
    def kept : Trust.Protocol.Binding := binds "kept::App.harness" ["kept::Wake::Observed"] []
    def spare : Trust.Protocol.Binding := binds "spare::App.config.harness" ["spare::Wake::Harness"] []
    end Shapes
}

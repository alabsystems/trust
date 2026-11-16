//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: binding_wraps_dep.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! More routes to a bound field that a binding once let through. Each module
//! has its own `App` and `Wake`:
//!
//! - `getter`: a `*const` of the struct comes back from a getter, is cast to
//!   `*mut` and handed to `ptr::write`. A pointer whose origin the body
//!   cannot see is matched by type, whatever kind of pointer it is.
//! - `head`: a message with one variant, and a write at the head of the
//!   drain loop: it runs before the first receive, with no message in hand.
//! - `pair`: the body holds two messages and the write runs when the first is
//!   `Prepared` or `Tick` and the second `Observed` or `Tick`. For the pair
//!   (`Prepared`, `Observed`) neither is the declared `Tick`.
//! - `wraps`: a dependency's generic fn wraps the pointer it is given
//!   (`Some(slot)`) and hands it to its own helper, or to `mem::take` through
//!   `Option::map`. Its body is read at the instance called.
//! - `wipes`: a dependency's generic fn calls a trait method on its type
//!   parameter, which at this instance is the dependency's blanket impl that
//!   writes a whole value. The arm that hands the same pointer to a closure
//!   that sets a sibling field (`with`) is not a writer.
//! - `boxed`: the fn that owns the `App` keeps it in a `Box`, and writes
//!   the field itself after every message. A box owns its value: this one
//!   owns the consumer's.
//! - `handed`: a closure in an undeclared arm captures a pointer to the
//!   field and hands it to `mem::replace`. The borrow is the parent's and the
//!   hand-off the closure's: the closure's is the site.
//! - `twice`: a pointer to the variable that holds the pointer (`&mut out`)
//!   goes to std's `impl Write for &mut W`.
//! - `reset`: the fn that owns the `App` assigns it a whole new value between
//!   messages.
//! - `job`: the `App` is moved into the job of a thread, a closure called
//!   once: its environment is where the value lives, and it writes the field
//!   itself after every message.
//! - `generic`: a generic helper writes through its `&mut T` inside a
//!   closure. The closure is read at the instance it is of.
//! - `setter`: the path passes a type of a dependency's, whose own setter an
//!   undeclared arm calls.
//! - `recast`: a pointer to the value holding the field, cast to a byte
//!   pointer and written through.
//! - `slice`: the fn that owns the `App` keeps it in a `Box<[App]>`.
//! - `pairs`: two receives in one tuple are two messages. The write runs
//!   with (`Observed`, `Tick`) in hand, and `Swap` is never sent.
//! - `viewed`: the cast pointer is turned back into a `&mut` before the
//!   write: a reborrow through a recast pointer is one.
//! - `repointed`: a pointer borrowed from a sibling is pointed at the value
//!   holding the field THROUGH a pointer to the variable (safe code). A
//!   pointer variable whose address is taken is judged by type.
//! - `shared`: the consumer takes `&self` and the field is a `Cell`: the fn
//!   that owns the value sets it between messages.
//! - `many`: a generic helper used at seventy types writes a whole `Config`
//!   at one of them. Every instance is read.
//! - `inbox`: the field's type keeps part of itself in a `Box`, and an
//!   undeclared arm writes into it (`self.config.harness.inner.x = 9`). A
//!   box owns its value: what a box in the field holds is the field's.
//! - `boxpart`: the field is a `Box`, and an undeclared arm takes a pointer
//!   to part of what it holds and hands it to `mem::replace`.
//! - `moved`: the consumer is a `move` closure that takes PART of the value
//!   by value (`app.config`): its environment is where that part lives, and
//!   an undeclared arm writes the field there.
//! - `twain`: two receives matched in place as one tuple are two messages.
//!   The write runs with (`Observed`, `Tick`) in hand; `Swap` is never sent.
//! - `inner`: the field keeps part of itself in an `Option<Box<_>>`, and an
//!   undeclared arm writes into the box through a pointer it took of the
//!   field (`if let Some(inner) = &mut self.config.harness.inner`).
//! - `celled`: the field owns a `Box<Cell<u8>>`, which an undeclared arm
//!   sets through `&self`: interior mutability a value owns is the value's.
//! - `fnptr`: a pointer to the value holding the field goes to `mem::take`
//!   through a fn pointer. What a fn pointer runs is not known where it is
//!   called.
//! - `stored`: the same pointer is stored into a field of a local tuple and
//!   unwrapped by `Option::map(mem::take)`.
//! - `param`: the consumer is generic over its `self` (`impl<S> App<S>`),
//!   and the fn that owns the `App<u8>` writes the field after every message.
//! - `nested`: the consumer is a `move` closure inside the `move` closure
//!   that is a thread's job, and holds the `App`'s fields by value.
//! - `batch`: an enum of the crate's holds one message or two; a switch over
//!   the second does not narrow the first.
//! - `tail`: a second message is stored into a field of a struct built with
//!   the first.
//! - `ptr`: the handler is reached only through a fn pointer, which the
//!   consumer census does not follow. The binding is refused, and the error
//!   says the consumer may be the thing that was not found.

extern crate binding_wraps_dep;

mod getter {
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
        Launder,
        Harness,
    }

    impl App {
        fn config_ptr(&mut self) -> *const Config {
            &raw const self.config
        }

        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Launder => {
                    let p = self.config_ptr() as *mut Config;
                    unsafe { std::ptr::write(p, Config { harness: 3, theme: 3 }) } //~ NOTE this lends `std::ptr::write` a `&mut` reaching `getter::App.config.harness`; reached from the arm for `getter::Wake::Launder` in `getter::App::on_wake`
                }
                Wake::Harness => self.config.harness = 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::Launder);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod head {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
        pub n: u32,
    }

    pub enum Wake {
        Policy(u8),
    }

    impl App {
        fn pump(&mut self, rx: Receiver<Wake>) {
            loop {
                self.harness = self.harness.wrapping_add(1); //~ NOTE this writes `head::App.harness`; reached from `head::App::pump` outside its arms
                match rx.recv() {
                    Ok(Wake::Policy(level)) => self.n += level as u32,
                    Err(_) => break,
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Policy(1));
        });
        let mut app = App { harness: 0, n: 0 };
        app.pump(rx);
        sender.join().unwrap();
    }
}

mod pair {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
    }

    pub enum Wake {
        Observed(u8),
        Prepared,
        Tick,
    }

    impl App {
        fn on_pair(&mut self, first: Wake, second: Wake) {
            match first {
                Wake::Observed(_) => {}
                _ => match second {
                    Wake::Prepared => {}
                    _ => self.harness = 9, //~ NOTE this writes `pair::App.harness`; reached from the arm for `pair::Wake::Observed` in `pair::App::on_pair`
                },
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
            let _ = tx.send(Wake::Prepared);
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0 };
        pump(&mut app, rx);
        sender.join().unwrap();
    }
}

mod wraps {
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

    pub enum Wake {
        ViaOpt,
        ViaMap,
        Harness,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::ViaOpt => binding_wraps_dep::reset_via_opt(&mut self.config), //~ NOTE this lends `reset_via_opt` a `&mut` reaching `wraps::App.config.harness`; reached from the arm for `wraps::Wake::ViaOpt` in `wraps::App::on_wake`
                Wake::ViaMap => binding_wraps_dep::take_via_map(&mut self.config), //~ NOTE this lends `take_via_map` a `&mut` reaching `wraps::App.config.harness`; reached from the arm for `wraps::Wake::ViaMap` in `wraps::App::on_wake`
                Wake::Harness => self.config.harness = 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::ViaOpt);
            let _ = tx.send(Wake::ViaMap);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod wipes {
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

    pub enum Wake {
        WipeIt,
        Theme,
        Harness,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::WipeIt => binding_wraps_dep::wipe_it(&mut self.config), //~ NOTE this lends `wipe_it` a `&mut` reaching `wipes::App.config.harness`; reached from the arm for `wipes::Wake::WipeIt` in `wipes::App::on_wake`
                Wake::Theme => binding_wraps_dep::with(&mut self.config, |config| config.theme += 1),
                Wake::Harness => self.config.harness = 1,
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Harness);
            let _ = tx.send(Wake::WipeIt);
            let _ = tx.send(Wake::Theme);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod boxed {
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
        let mut app = Box::new(App { harness: 0, n: 0 });
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
            app.harness = 9; //~ NOTE this writes `boxed::App.harness`; reached from `main`, the consumer's own thread, outside `boxed::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod handed {
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
                Wake::Tick => {
                    let mut reset = || std::mem::replace(&mut self.harness, 9); //~ NOTE this hands on a pointer it captured to `handed::App.harness`; reached from the arm for `handed::Wake::Tick` in `handed::App::on_wake`
                    self.n += reset() as u32;
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
        let mut app = App { harness: 0, n: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod twice {
    use std::io::Write;
    use std::sync::mpsc::channel;

    pub struct App {
        pub log: Vec<u8>,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.log = vec![level],
                Wake::Tick => {
                    let mut out = &mut self.log; //~ NOTE this takes a `&mut` of `twice::App.log`; reached from the arm for `twice::Wake::Tick` in `twice::App::on_wake`
                    let _ = (&mut out).write_all(b"tick");
                    self.n += 1;
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
        let mut app = App { log: Vec::new(), n: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod reset {
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
        let mut app = App { harness: 0, n: 0 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
            if app.n > 0 {
                app = App { harness: 9, n: 0 }; //~ NOTE this writes a whole `reset::App` holding `reset::App.harness`; reached from `main`, the consumer's own thread, outside `reset::App::on_wake`
            }
        }
        sender.join().unwrap();
    }
}

mod job {
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
        let mut app = App { harness: 0, n: 0 };
        let worker = std::thread::spawn(move || {
            for wake in rx {
                app.on_wake(wake);
                app.harness = 9; //~ NOTE this writes `job::App.harness`; reached from `job::run::{closure#0}`, the consumer's own thread, outside `job::App::on_wake`
            }
        });
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Tick);
        drop(tx);
        worker.join().unwrap();
    }
}

mod generic {
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

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    fn clear<T: Default>(slot: &mut T) {
        let mut wipe = || *slot = T::default(); //~ NOTE this writes a whole `generic::Config` holding `generic::App.config.harness`; reached from the arm for `generic::Wake::Tick` in `generic::App::on_wake`
        wipe();
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = level,
                Wake::Tick => clear(&mut self.config),
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod setter {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct App {
        pub cfg: binding_wraps_dep::Cfg,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.cfg.level = level,
                Wake::Tick => self.cfg.set_level(9), //~ NOTE this lends `Cfg::set_level` a `&mut` reaching `setter::App.cfg.level`; reached from the arm for `setter::Wake::Tick` in `setter::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod recast {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    #[repr(C)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
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
                Wake::Tick => {
                    let bytes = &mut self.config as *mut Config as *mut u8;
                    unsafe { *bytes = 9 }; //~ NOTE this writes, through a pointer cast to another type, into a value holding `recast::App.config.harness`; reached from the arm for `recast::Wake::Tick` in `recast::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod slice {
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

    fn apps() -> Box<[App]> {
        vec![App { harness: 0, n: 0 }].into_boxed_slice()
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut apps = apps();
        while let Ok(wake) = rx.recv() {
            apps[0].on_wake(wake);
            apps[0].harness = 9; //~ NOTE this writes `slice::App.harness`; reached from `main`, the consumer's own thread, outside `slice::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod pairs {
    use std::sync::mpsc::{Receiver, channel};

    pub struct App {
        pub harness: u8,
    }

    pub enum Wake {
        Tick,
        Observed(u8),
        Swap,
    }

    impl App {
        fn pump(&mut self, rx: Receiver<Wake>) {
            loop {
                let (Ok(first), Ok(second)) = (rx.recv(), rx.recv()) else { break };
                match (first, second) {
                    (Wake::Tick, _) => {}
                    (Wake::Observed(_), Wake::Observed(_)) => {}
                    _ => self.harness = 9, //~ NOTE this writes `pairs::App.harness`; reached from the arm for `pairs::Wake::Tick` in `pairs::App::pump`
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
        let mut app = App { harness: 0 };
        app.pump(rx);
        sender.join().unwrap();
    }
}

mod viewed {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    #[repr(C)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
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
                Wake::Tick => {
                    let bytes = unsafe { &mut *(&raw mut self.config as *mut u8) };
                    *bytes = 9; //~ NOTE this writes, through a pointer cast to another type, into a value holding `viewed::App.config.harness`; reached from the arm for `viewed::Wake::Tick` in `viewed::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod repointed {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = level,
                Wake::Tick => {
                    let mut slot = &mut self.spare;
                    let way = &mut slot;
                    *way = &mut self.config;
                    slot.harness = 9; //~ NOTE this writes `repointed::App.config.harness`; reached from the arm for `repointed::Wake::Tick` in `repointed::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod shared {
    use std::cell::Cell;
    use std::sync::mpsc::channel;

    pub struct App {
        pub harness: Cell<u8>,
        pub n: Cell<u32>,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness.set(level),
                Wake::Tick => self.n.set(self.n.get() + 1),
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let app = App { harness: Cell::new(0), n: Cell::new(0) };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
            app.harness.set(9); //~ NOTE this takes a `&` of the interior-mutable `shared::App.harness`; reached from `main`, the consumer's own thread, outside `shared::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod many {
    use std::sync::mpsc::channel;

    #[derive(Clone, Copy, Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    fn clear<T: Copy>(slot: &mut T, to: T) {
        *slot = to; //~ NOTE this writes a whole `many::Config` holding `many::App.config.harness`; reached from the arm for `many::Wake::Tick` in `many::App::on_wake`
    }

    macro_rules! clear_each {
        ($($len:literal)*) => { $( clear(&mut [1u8; $len], [0u8; $len]); )* };
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = level,
                Wake::Tick => clear(&mut self.config, Config::default()),
            }
        }
    }

    pub fn run() {
        clear_each!(
            1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
        );
        clear_each!(
            33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61
            62 63 64 65 66 67 68 69 70
        );
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod inbox {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Inner {
        pub x: u8,
    }

    #[derive(Default)]
    pub struct Policy {
        pub level: u8,
        pub inner: Box<Inner>,
    }

    #[derive(Default)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
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
                Wake::Observed(level) => {
                    self.config.harness = Policy { level, inner: Box::new(Inner { x: level }) }
                }
                Wake::Tick => self.config.harness.inner.x = 9, //~ NOTE this writes part of `inbox::App.config.harness`; reached from the arm for `inbox::Wake::Tick` in `inbox::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod boxpart {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Policy(pub u8, pub u8);

    #[derive(Default)]
    pub struct Config {
        pub harness: Box<Policy>,
        pub theme: u8,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
        Tock,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Box::new(Policy(level, 0)),
                Wake::Tick => {
                    let _ = std::mem::replace(&mut self.config.harness.0, 9); //~ NOTE this takes a `&mut` of part of `boxpart::App.config.harness`; reached from the arm for `boxpart::Wake::Tick` in `boxpart::App::on_wake`
                }
                Wake::Tock => {
                    let part = &mut self.config.harness.1;
                    *part = 9; //~ NOTE this writes part of `boxpart::App.config.harness`; reached from the arm for `boxpart::Wake::Tock` in `boxpart::App::on_wake`
                }
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
            let _ = tx.send(Wake::Tock);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod moved {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: String,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl Config {
        fn set(&mut self, level: u8) {
            self.harness = level;
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        let worker = std::thread::spawn(move || {
            for wake in rx {
                match wake {
                    Wake::Observed(level) => app.config.set(level),
                    Wake::Tick => app.config.harness = 9, //~ NOTE this writes `moved::App.config.harness`; reached from the arm for `moved::Wake::Tick` in `moved::run::{closure#1}`
                }
            }
        });
        worker.join().unwrap();
        sender.join().unwrap();
    }
}

mod twain {
    use std::sync::mpsc::{Receiver, channel};

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
        pub fn pump(&mut self, rx: &Receiver<Wake>) {
            loop {
                match (rx.recv(), rx.recv()) {
                    (Ok(Wake::Tick), _) => self.ticks += 1,
                    (_, Ok(Wake::Observed(_))) => self.ticks += 1,
                    (Ok(Wake::Observed(_)), Ok(Wake::Swap)) => self.ticks += 1,
                    (Ok(_), Ok(_)) => self.harness = 9, //~ NOTE this writes `twain::App.harness`; reached from the arm for `twain::Wake::Tick` in `twain::App::pump`
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
        });
        let mut app = App::default();
        app.pump(&rx);
        sender.join().unwrap();
    }
}

mod inner {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Inner {
        pub x: u8,
    }

    #[derive(Default)]
    pub struct Policy {
        pub level: u8,
        pub inner: Option<Box<Inner>>,
    }

    #[derive(Default)]
    pub struct App {
        pub harness: Policy,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => {
                    self.harness = Policy { level, inner: Some(Box::new(Inner { x: level })) }
                }
                Wake::Tick => {
                    if let Some(inner) = &mut self.harness.inner {
                        inner.x = 9; //~ NOTE this writes part of `inner::App.harness`; reached from the arm for `inner::Wake::Tick` in `inner::App::on_wake`
                    }
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod celled {
    use std::cell::Cell;
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Policy {
        pub level: Box<Cell<u8>>,
    }

    #[derive(Default)]
    pub struct App {
        pub harness: Policy,
        pub ticks: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = Policy { level: Box::new(Cell::new(level)) },
                Wake::Tick => self.poke(),
            }
        }

        fn poke(&self) {
            self.harness.level.set(9); //~ NOTE this takes a `&` of part of the interior-mutable `celled::App.harness`; reached from the arm for `celled::Wake::Tick` in `celled::App::on_wake`
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod fnptr {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
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
                Wake::Tick => {
                    let take: fn(&mut Config) -> Config = std::mem::take;
                    let _old = take(&mut self.config); //~ NOTE this lends a call through a fn pointer a `&mut` reaching `fnptr::App.config.harness`; reached from the arm for `fnptr::Wake::Tick` in `fnptr::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod stored {
    use std::sync::mpsc::channel;

    #[derive(Default)]
    pub struct Config {
        pub harness: u8,
        pub theme: u8,
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
                Wake::Tick => {
                    let mut slot = (None, 0u8);
                    slot.0 = Some(&mut self.config);
                    let _old = slot.0.map(std::mem::take); //~ NOTE this lends `Option::<T>::map` a `&mut` reaching `stored::App.config.harness`; reached from the arm for `stored::Wake::Tick` in `stored::App::on_wake`
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
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod param {
    use std::sync::mpsc::channel;

    pub struct App<S> {
        pub harness: u8,
        pub extra: S,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl<S> App<S> {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = level,
                Wake::Tick => {}
            }
        }
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App { harness: 0, extra: 0u8 };
        while let Ok(wake) = rx.recv() {
            app.on_wake(wake);
            app.harness = 9; //~ NOTE this writes `param::App<S>.harness`; reached from `main`, the consumer's own thread, outside `param::App::<S>::on_wake`
        }
        sender.join().unwrap();
    }
}

mod nested {
    use std::sync::mpsc::channel;

    #[derive(Clone, Copy, Default)]
    pub struct Policy(pub u8);

    #[derive(Default)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default)]
    pub struct App {
        pub config: Config,
    }

    pub enum Wake {
        Observed(u8),
        Reset,
        Tick,
    }

    fn set(harness: &mut Policy, level: u8) {
        *harness = Policy(level);
    }

    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Reset);
            let _ = tx.send(Wake::Tick);
        });
        let mut app = App::default();
        let ui = std::thread::spawn(move || {
            let mut on_wake = move |wake: Wake| {
                match wake {
                    Wake::Observed(level) => set(&mut app.config.harness, level),
                    Wake::Reset => app.config.harness = Policy(77), //~ NOTE this writes `nested::App.config.harness`; reached from the arm for `nested::Wake::Reset` in `nested::run::{closure#1}::{closure#0}`
                    Wake::Tick => app.config.theme += 1,
                }
                app.config.harness.0
            };
            let mut last = 0;
            while let Ok(wake) = rx.recv() {
                last = on_wake(wake);
            }
            last
        });
        ui.join().unwrap();
        sender.join().unwrap();
    }
}

mod batch {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Default)]
    pub struct App {
        pub harness: u8,
    }

    pub enum Wake {
        Tick,
        Observed(u8),
        Swap,
    }

    enum Batch {
        One(Wake),
        Two(Wake, Wake),
    }

    impl App {
        pub fn pump(&mut self, rx: &Receiver<Wake>) {
            loop {
                let Ok(first) = rx.recv() else { break };
                let batch = match rx.try_recv() {
                    Ok(second) => Batch::Two(first, second),
                    Err(_) => Batch::One(first),
                };
                match batch {
                    Batch::Two(Wake::Tick, _) => {}
                    Batch::Two(Wake::Observed(_), Wake::Observed(_)) => {}
                    Batch::Two(Wake::Observed(_), _) | Batch::Two(Wake::Swap, _) => {
                        self.harness = 9 //~ NOTE this writes `batch::App.harness`; reached from the arm for `batch::Wake::Tick` in `batch::App::pump`
                    }
                    _ => {}
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
        sender.join().unwrap();
        let mut app = App::default();
        app.pump(&rx);
    }
}

mod tail {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Default)]
    pub struct App {
        pub harness: u8,
    }

    #[derive(Clone)]
    pub enum Wake {
        Tick,
        Observed(u8),
        Swap,
    }

    struct Run {
        head: Wake,
        tail: Wake,
    }

    impl App {
        pub fn pump(&mut self, rx: &Receiver<Wake>) {
            loop {
                let Ok(first) = rx.recv() else { break };
                let mut run = Run { head: first.clone(), tail: first };
                if let Ok(next) = rx.try_recv() {
                    run.tail = next;
                }
                match (&run.head, &run.tail) {
                    (Wake::Tick, _) => {}
                    (Wake::Observed(_), Wake::Observed(_)) => {}
                    (Wake::Observed(_), _) | (Wake::Swap, _) => self.harness = 9, //~ NOTE this writes `tail::App.harness`; reached from the arm for `tail::Wake::Tick` in `tail::App::pump`
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
        sender.join().unwrap();
        let mut app = App::default();
        app.pump(&rx);
    }
}

mod ptr {
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
        let mut app = App { harness: 0, n: 0 };
        let handler: fn(&mut App, Wake) = App::on_wake;
        while let Ok(wake) = rx.recv() {
            handler(&mut app, wake);
        }
        sender.join().unwrap();
    }
}

fn main() {
    getter::run();
    head::run();
    pair::run();
    wraps::run();
    wipes::run();
    boxed::run();
    handed::run();
    twice::run();
    reset::run();
    job::run();
    generic::run();
    setter::run();
    recast::run();
    slice::run();
    pairs::run();
    viewed::run();
    repointed::run();
    shared::run();
    many::run();
    inbox::run();
    boxpart::run();
    moved::run();
    twain::run();
    inner::run();
    celled::run();
    fnptr::run();
    stored::run();
    param::run();
    nested::run();
    batch::run();
    tail::run();
    ptr::run();
}

clean {
    import Trust.Binding
    namespace More
    open Trust.Protocol
    def getter : Trust.Protocol.Binding := binds "getter::App.config.harness" ["getter::Wake::Harness"] []
    def head : Trust.Protocol.Binding := binds "head::App.harness" ["head::Wake::Policy"] []
    def pair : Trust.Protocol.Binding := binds "pair::App.harness" ["pair::Wake::Tick"] []
    def wraps : Trust.Protocol.Binding := binds "wraps::App.config.harness" ["wraps::Wake::Harness"] []
    def wipes : Trust.Protocol.Binding := binds "wipes::App.config.harness" ["wipes::Wake::Harness"] []
    def boxed : Trust.Protocol.Binding := binds "boxed::App.harness" ["boxed::Wake::Observed"] []
    def handed : Trust.Protocol.Binding := binds "handed::App.harness" ["handed::Wake::Observed"] []
    def twice : Trust.Protocol.Binding := binds "twice::App.log" ["twice::Wake::Observed"] []
    def reset : Trust.Protocol.Binding := binds "reset::App.harness" ["reset::Wake::Observed"] []
    def job : Trust.Protocol.Binding := binds "job::App.harness" ["job::Wake::Observed"] []
    def generic : Trust.Protocol.Binding := binds "generic::App.config.harness" ["generic::Wake::Observed"] []
    def setter : Trust.Protocol.Binding := binds "setter::App.cfg.level" ["setter::Wake::Observed"] []
    def recast : Trust.Protocol.Binding := binds "recast::App.config.harness" ["recast::Wake::Observed"] []
    def slice : Trust.Protocol.Binding := binds "slice::App.harness" ["slice::Wake::Observed"] []
    def pairs : Trust.Protocol.Binding := binds "pairs::App.harness" ["pairs::Wake::Swap"] []
    def viewed : Trust.Protocol.Binding := binds "viewed::App.config.harness" ["viewed::Wake::Observed"] []
    def repointed : Trust.Protocol.Binding := binds "repointed::App.config.harness" ["repointed::Wake::Observed"] []
    def shared : Trust.Protocol.Binding := binds "shared::App.harness" ["shared::Wake::Observed"] []
    def many : Trust.Protocol.Binding := binds "many::App.config.harness" ["many::Wake::Observed"] []
    def inbox : Trust.Protocol.Binding := binds "inbox::App.config.harness" ["inbox::Wake::Observed"] []
    def boxpart : Trust.Protocol.Binding := binds "boxpart::App.config.harness" ["boxpart::Wake::Observed"] []
    def moved : Trust.Protocol.Binding := binds "moved::App.config.harness" ["moved::Wake::Observed"] []
    def twain : Trust.Protocol.Binding := binds "twain::App.harness" ["twain::Wake::Swap"] []
    def inner : Trust.Protocol.Binding := binds "inner::App.harness" ["inner::Wake::Observed"] []
    def celled : Trust.Protocol.Binding := binds "celled::App.harness" ["celled::Wake::Observed"] []
    def fnptr : Trust.Protocol.Binding := binds "fnptr::App.config.harness" ["fnptr::Wake::Observed"] []
    def stored : Trust.Protocol.Binding := binds "stored::App.config.harness" ["stored::Wake::Observed"] []
    def param : Trust.Protocol.Binding := binds "param::App.harness" ["param::Wake::Observed"] []
    def nested : Trust.Protocol.Binding := binds "nested::App.config.harness" ["nested::Wake::Observed"] []
    def batch : Trust.Protocol.Binding := binds "batch::App.harness" ["batch::Wake::Swap"] []
    def tail : Trust.Protocol.Binding := binds "tail::App.harness" ["tail::Wake::Swap"] []
    def ptr : Trust.Protocol.Binding := binds "ptr::App.harness" ["ptr::Wake::Observed"] []
    end More
}
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.getter` binds `getter::App.config.harness` to the arm(s) for `getter::Wake::Harness`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.head` binds `head::App.harness` to the arm(s) for `head::Wake::Policy`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.pair` binds `pair::App.harness` to the arm(s) for `pair::Wake::Tick`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.wraps` binds `wraps::App.config.harness` to the arm(s) for `wraps::Wake::Harness`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.wipes` binds `wipes::App.config.harness` to the arm(s) for `wipes::Wake::Harness`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.boxed` binds `boxed::App.harness` to the arm(s) for `boxed::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.handed` binds `handed::App.harness` to the arm(s) for `handed::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.twice` binds `twice::App.log` to the arm(s) for `twice::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.reset` binds `reset::App.harness` to the arm(s) for `reset::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.job` binds `job::App.harness` to the arm(s) for `job::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.generic` binds `generic::App.config.harness` to the arm(s) for `generic::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.setter` binds `setter::App.cfg.level` to the arm(s) for `setter::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.recast` binds `recast::App.config.harness` to the arm(s) for `recast::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.slice` binds `slice::App.harness` to the arm(s) for `slice::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.pairs` binds `pairs::App.harness` to the arm(s) for `pairs::Wake::Swap`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.viewed` binds `viewed::App.config.harness` to the arm(s) for `viewed::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.repointed` binds `repointed::App.config.harness` to the arm(s) for `repointed::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.shared` binds `shared::App.harness` to the arm(s) for `shared::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.many` binds `many::App.config.harness` to the arm(s) for `many::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.inbox` binds `inbox::App.config.harness` to the arm(s) for `inbox::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.boxpart` binds `boxpart::App.config.harness` to the arm(s) for `boxpart::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.moved` binds `moved::App.config.harness` to the arm(s) for `moved::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.twain` binds `twain::App.harness` to the arm(s) for `twain::Wake::Swap`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.inner` binds `inner::App.harness` to the arm(s) for `inner::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.celled` binds `celled::App.harness` to the arm(s) for `celled::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.fnptr` binds `fnptr::App.config.harness` to the arm(s) for `fnptr::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.stored` binds `stored::App.config.harness` to the arm(s) for `stored::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.param` binds `param::App<S>.harness` to the arm(s) for `param::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.nested` binds `nested::App.config.harness` to the arm(s) for `nested::Wake::Observed`, and 1 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.batch` binds `batch::App.harness` to the arm(s) for `batch::Wake::Swap`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.tail` binds `tail::App.harness` to the arm(s) for `tail::Wake::Swap`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR `More.ptr` binds the field path `ptr::App.harness`, and no message consumer has an argument with that path
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ HELP A handler the drain loop calls through a fn pointer or a `dyn` is not found as one

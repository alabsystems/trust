//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! True bindings that a scan judging unknown pointers by type alone fails,
//! and that hold on the origin analysis. No warning is expected: a binding
//! that held for want of a write would warn.
//!
//! - `sibling`: an undeclared arm goes through std accessors on a SIBLING
//!   (`self.spare.as_mut().unwrap().harness = 2`). A std fn that is given no
//!   code to run hands back only what it was given, and a pointer to a
//!   sibling is not a pointer to the field.
//! - `guarded`: the consumer's value is in a `RefCell`. Reading it through
//!   `borrow()` and writing a sibling through `borrow_mut()` hand the guard
//!   to std's accessors, which hand it back.
//! - `stacked`: an undeclared arm builds a `vec![App::default()]` of its
//!   own. Storage still to be given a value is nobody's.
//! - `stepped`: a pointer variable that only ever points at a sibling has
//!   its address taken and is written through. The address does not leave.
//! - `flagged`: the field is an `AtomicBool`, and an `Arc<AtomicBool>`
//!   elsewhere is stored to. A `&` whose type alone says it may be the field
//!   is no pointer to it.
//! - `wrapped`: the value is handed by value to a fn that only wraps it.

mod sibling {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Clone, Copy, Default, Debug, PartialEq)]
    pub struct Policy(pub u8);

    #[derive(Default, Debug)]
    #[repr(C)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default, Debug)]
    pub struct App {
        pub config: Config,
        pub spare: Option<Config>,
        pub staged: Vec<Config>,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    self.spare.get_or_insert_with(Config::default).harness = Policy(2);
                    if let Some(spare) = self.spare.as_mut() {
                        spare.harness = Policy(3);
                    }
                    self.staged.push(Config::default());
                    for staged in self.staged.iter_mut() {
                        staged.harness = Policy(4);
                    }
                    if let Some(last) = self.staged.last_mut() {
                        last.harness = Policy(5);
                    }
                }
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let mut app = App::default();
        for wake in rx {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod guarded {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Clone, Copy, Default, Debug, PartialEq)]
    pub struct Policy(pub u8);

    #[derive(Default, Debug)]
    #[repr(C)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default, Debug)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    use std::cell::RefCell;

    fn count(cell: &RefCell<App>) {
        cell.borrow_mut().n += 1;
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    self.n += 1;
                }
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let cell = RefCell::new(App::default());
        for wake in rx {
            cell.borrow_mut().on_wake(wake);
            count(&cell);
            println!("harness: {:?} n: {}", cell.borrow().config.harness, cell.borrow().n);
        }
        sender.join().unwrap();
    }
}

mod stacked {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Clone, Copy, Default, Debug, PartialEq)]
    pub struct Policy(pub u8);

    #[derive(Default, Debug)]
    #[repr(C)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default, Debug)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    let mut scratch = vec![App::default(), App::default()];
                    scratch.truncate(1);
                    self.n = scratch.len() as u32;
                }
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let mut app = App::default();
        for wake in rx {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod stepped {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Clone, Copy, Default, Debug, PartialEq)]
    pub struct Policy(pub u8);

    #[derive(Default, Debug)]
    #[repr(C)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default, Debug)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    let mut spare = &mut self.spare;
                    let again = &mut spare;
                    again.theme = 1;
                    spare.harness = Policy(2);
                }
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let mut app = App::default();
        for wake in rx {
            app.on_wake(wake);
        }
        sender.join().unwrap();
    }
}

mod flagged {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::mpsc::{Receiver, channel};
    use std::sync::Arc;

    #[derive(Default)]
    pub struct App {
        pub harness: AtomicBool,
        pub stop: Arc<AtomicBool>,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.harness = AtomicBool::new(level > 0),
                Wake::Tick => self.stop.store(true, Ordering::Relaxed),
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let mut app = App::default();
        let stop = app.stop.clone();
        for wake in rx {
            app.on_wake(wake);
            if stop.load(Ordering::Relaxed) {
                stop.store(false, Ordering::Relaxed);
            }
        }
        sender.join().unwrap();
    }
}

mod wrapped {
    use std::sync::mpsc::{Receiver, channel};

    #[derive(Clone, Copy, Default, Debug, PartialEq)]
    pub struct Policy(pub u8);

    #[derive(Default, Debug)]
    #[repr(C)]
    pub struct Config {
        pub harness: Policy,
        pub theme: u8,
    }

    #[derive(Default, Debug)]
    pub struct App {
        pub config: Config,
        pub spare: Config,
        pub n: u32,
    }

    pub enum Wake {
        Observed(u8),
        Tick,
    }

    pub struct Host {
        app: App,
        runs: u32,
    }

    fn wrap(app: App) -> Host {
        Host { app, runs: 0 }
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    self.n += 1;
                }
            }
        }
    }

    pub fn feed() -> (std::thread::JoinHandle<()>, Receiver<Wake>) {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || {
            let _ = tx.send(Wake::Observed(1));
            let _ = tx.send(Wake::Tick);
        });
        (sender, rx)
    }

    pub fn run() {
        let (sender, rx) = feed();
        let mut host = wrap(App::default());
        for wake in rx {
            host.app.on_wake(wake);
            host.runs += 1;
        }
        sender.join().unwrap();
    }
}

fn main() {
    sibling::run();
    guarded::run();
    stacked::run();
    stepped::run();
    flagged::run();
    wrapped::run();
}

clean {
    import Trust.Binding
    namespace Kept
    open Trust.Protocol
    def sibling : Trust.Protocol.Binding := binds "sibling::App.config.harness" ["sibling::Wake::Observed"] []
    def guarded : Trust.Protocol.Binding := binds "guarded::App.config.harness" ["guarded::Wake::Observed"] []
    def stacked : Trust.Protocol.Binding := binds "stacked::App.config.harness" ["stacked::Wake::Observed"] []
    def stepped : Trust.Protocol.Binding := binds "stepped::App.config.harness" ["stepped::Wake::Observed"] []
    def flagged : Trust.Protocol.Binding := binds "flagged::App.harness" ["flagged::Wake::Observed"] []
    def wrapped : Trust.Protocol.Binding := binds "wrapped::App.config.harness" ["wrapped::Wake::Observed"] []
    end Kept
}

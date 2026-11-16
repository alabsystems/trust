//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Routes to a bound field that the writer scan missed until it was rebuilt
//! on one origin analysis per body. Each was found by attacking that design
//! on paper before it was written, and each module's binding must FAIL:
//!
//! - `guard`: a guard around a pointer to part of the field, whose `Drop`
//!   writes through it. Dropping a value whose drop runs code is handing it
//!   over.
//! - `cell`: the consumer's value is in a `RefCell`, and a helper replaces
//!   it through a `&`. A `&` of a cell can write what the cell holds.
//! - `audit`: a helper takes the value BY VALUE, writes the field and hands
//!   it back, between two messages. A value of the consumer's type that a
//!   body is given is one a consumer may run on.
//! - `parked`: the value is parked in a struct between messages and written
//!   there. A value moved in and out of a holder makes the holder one.
//! - `poked`: a pointer to the value holding the field, cast to a byte
//!   pointer and handed to a fn of the crate: no type tells that fn what it
//!   was given.
//! - `hooks`: a `const` table of fn pointers holds `mem::take`, and an
//!   undeclared arm calls through it.
//! - `deep`: a pointer to a pointer to a pointer to part of the field goes
//!   to a fn of the crate. What a leaving pointer points into leaves too.
//! - `carrier`: a pointer to part of the field is kept in a tuple beside a
//!   scratch value of the consumer's own type, and written through there.
//! - `opt`: a fn of the crate takes an `Option<&mut Config>` and lets
//!   `Option::map(mem::take)` write through it. A value of unknown origin
//!   reaches by its type, whatever carries the pointer.

mod guard {
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

    struct Guard<'a>(&'a mut u8);

    impl Drop for Guard<'_> {
        fn drop(&mut self) {
            *self.0 = 9;
        }
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    let _guard = Guard(&mut self.config.harness.0); //~ NOTE this takes a `&mut` of part of `guard::App.config.harness`; reached from the arm for `guard::Wake::Tick` in `guard::App::on_wake`
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

mod cell {
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

    fn reset(cell: &RefCell<App>) {
        cell.replace(App::default()); //~ NOTE this lends `RefCell::<T>::replace` a `&mut` reaching `cell::App.config.harness`; reached from `main`, the consumer's own thread, outside `cell::App::on_wake`
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
            reset(&cell);
        }
        sender.join().unwrap();
    }
}

mod audit {
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

    fn audit(mut app: App) -> App {
        app.config.harness = Policy(9); //~ NOTE this writes `audit::App.config.harness`; reached from `main`, the consumer's own thread, outside `audit::App::on_wake`
        app
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
        let app = rx.into_iter().fold(App::default(), |mut app, wake| {
            app.on_wake(wake);
            audit(app)
        });
        drop(app);
        sender.join().unwrap();
    }
}

mod parked {
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

    pub struct Parked {
        app: App,
        seen: u32,
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
        let mut parked = Parked { app: App::default(), seen: 0 };
        for wake in rx {
            let mut app = parked.app;
            app.on_wake(wake);
            parked = Parked { app, seen: parked.seen + 1 }; //~ NOTE this writes a whole `Parked` holding `parked::App.config.harness`; reached from `main`, the consumer's own thread, outside `parked::App::on_wake`
            parked.app.config.harness = Policy(9); //~ NOTE this writes `parked::App.config.harness`; reached from `main`, the consumer's own thread, outside `parked::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod poked {
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

    fn poke(byte: *mut u8) {
        unsafe { *byte = 9 }
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    poke(&mut self.config as *mut Config as *mut u8); //~ NOTE this lends `poked::poke` a `&mut` reaching `poked::App.config.harness`; reached from the arm for `poked::Wake::Tick` in `poked::App::on_wake`
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

mod hooks {
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

    const HOOKS: [fn(&mut Config) -> Config; 1] = [std::mem::take];

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    let hook = HOOKS[0];
                    let _old = hook(&mut self.config); //~ NOTE this lends a call through a fn pointer a `&mut` reaching `hooks::App.config.harness`; reached from the arm for `hooks::Wake::Tick` in `hooks::App::on_wake`
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

mod deep {
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

    fn poke(level: &mut &mut &mut u8) {
        ***level = 9;
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    let mut one: &mut u8 = &mut self.config.harness.0; //~ NOTE this takes a `&mut` of part of `deep::App.config.harness`; reached from the arm for `deep::Wake::Tick` in `deep::App::on_wake`
                    let mut two = &mut one;
                    let three = &mut two;
                    poke(three);
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

mod carrier {
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
                    let mut pair = (App::default(), &mut self.config.harness.0);
                    let scratch = &mut pair.0;
                    scratch.n = 1;
                    *pair.1 = 9; //~ NOTE this writes part of `carrier::App.config.harness`; reached from the arm for `carrier::Wake::Tick` in `carrier::App::on_wake`
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

mod opt {
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

    fn clear(slot: Option<&mut Config>) {
        let _old = slot.map(std::mem::take); //~ NOTE this lends `Option::<T>::map` a `&mut` reaching `opt::App.config.harness`; reached from the arm for `opt::Wake::Tick` in `opt::App::on_wake`
    }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(level) => self.config.harness = Policy(level),
                Wake::Tick => {
                    clear(Some(&mut self.config));
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

fn main() {
    guard::run();
    cell::run();
    audit::run();
    parked::run();
    poked::run();
    hooks::run();
    deep::run();
    carrier::run();
    opt::run();
}

clean {
    import Trust.Binding
    namespace Origins
    open Trust.Protocol
    def guard : Trust.Protocol.Binding := binds "guard::App.config.harness" ["guard::Wake::Observed"] []
    def cell : Trust.Protocol.Binding := binds "cell::App.config.harness" ["cell::Wake::Observed"] []
    def audit : Trust.Protocol.Binding := binds "audit::App.config.harness" ["audit::Wake::Observed"] []
    def parked : Trust.Protocol.Binding := binds "parked::App.config.harness" ["parked::Wake::Observed"] []
    def poked : Trust.Protocol.Binding := binds "poked::App.config.harness" ["poked::Wake::Observed"] []
    def hooks : Trust.Protocol.Binding := binds "hooks::App.config.harness" ["hooks::Wake::Observed"] []
    def deep : Trust.Protocol.Binding := binds "deep::App.config.harness" ["deep::Wake::Observed"] []
    def carrier : Trust.Protocol.Binding := binds "carrier::App.config.harness" ["carrier::Wake::Observed"] []
    def opt : Trust.Protocol.Binding := binds "opt::App.config.harness" ["opt::Wake::Observed"] []
    end Origins
}
//~^^^^^^^^^^^ ERROR `Origins.guard` binds `guard::App.config.harness` to the arm(s) for `guard::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.cell` binds `cell::App.config.harness` to the arm(s) for `cell::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.audit` binds `audit::App.config.harness` to the arm(s) for `audit::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.parked` binds `parked::App.config.harness` to the arm(s) for `parked::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.poked` binds `poked::App.config.harness` to the arm(s) for `poked::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.hooks` binds `hooks::App.config.harness` to the arm(s) for `hooks::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.deep` binds `deep::App.config.harness` to the arm(s) for `deep::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.carrier` binds `carrier::App.config.harness` to the arm(s) for `carrier::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^ ERROR `Origins.opt` binds `opt::App.config.harness` to the arm(s) for `opt::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere

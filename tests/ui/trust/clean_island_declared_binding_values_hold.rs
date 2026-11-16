//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! True bindings that the first build of the origin analysis refused, found
//! by its review by reproduction. Each must HOLD, with no warning: a binding
//! that held for want of a write would warn.
//!
//! - `locked`: the consumer's value is in an `Arc<Mutex<App>>`, and a field
//!   read through the guard is printed. A `&` got out of a guard writes
//!   nothing, and takes nothing out.
//! - `borrowed`: the same through an `Rc<RefCell<App>>`.
//! - `counted`: a sibling read through a lock guard goes to a std iterator
//!   adaptor.
//! - `asmut`: the value is in an `Option<App>` and reached with `.as_mut()`:
//!   a std fn that hands back a pointer, and is given nothing to put there,
//!   writes nothing.
//! - `boxfield`: the value is in a `Box<App>` field and the handler is called
//!   in a loop: the pointer the compiler loads to dereference the box is no
//!   new value.
//! - `strs`: a sibling map keyed by `&'static str` is reached with std
//!   accessors: a `&` that can write nothing is no pointer to follow.
//! - `unboxed`: `let mut app = *Box::new(App::default());`: the emptied box
//!   is dropped by the compiler's own call.
//! - `guardeddyn`: the consumer's type keeps a trait object and its value is
//!   behind a `Mutex`: the drop of a lock guard unlocks, and drops nothing of
//!   what the guard borrows, whatever that is made of. A sibling is written
//!   through the guard, and the field is read out of it before it is printed.
//! - `guarded`: a SIBLING `Vec<Config>` is reached through a lock guard and
//!   one of its elements written (`app.lock().unwrap().list.last_mut()`),
//!   where the consumer's type also keeps a box. A guard's variable owns
//!   none of what it borrows: what std hands back out of the sibling is no
//!   pointer of unknown origin.

#![allow(unused)]

mod locked {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    use std::sync::{Arc, Mutex};
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let app = Arc::new(Mutex::new(App::default()));
        for wake in rx {
            app.lock().unwrap().on_wake(wake);
            println!("harness: {:?}", app.lock().unwrap().config.harness);
        }
        sender.join().unwrap();
    }
}

mod borrowed {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    use std::rc::Rc; use std::cell::RefCell;
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let app = Rc::new(RefCell::new(App::default()));
        for wake in rx {
            app.borrow_mut().on_wake(wake);
            println!("harness: {:?}", app.borrow().config.harness);
        }
        sender.join().unwrap();
    }
}

mod counted {
    use std::sync::mpsc::channel;
    use std::sync::RwLock;
    #[derive(Default)]
    pub struct App { pub harness: u8, pub items: Vec<u32> }
    pub enum Wake { Observed(u8), Tick }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.harness = p,
                Wake::Tick => self.items.push(1),
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
        let app = RwLock::new(App::default());
        for wake in rx { app.write().unwrap().on_wake(wake); }
        let total: u32 = app.read().unwrap().items.iter().sum();
        println!("total: {total}");
        sender.join().unwrap();
    }
}

mod asmut {
    use std::sync::mpsc::{channel, Receiver};
    use std::collections::{HashMap, VecDeque, BTreeMap};
    use std::cell::{RefCell, Cell};
    use std::rc::Rc;
    use std::sync::{Arc, Mutex, RwLock};
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug, Clone, PartialEq)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug, Clone)]
    pub struct App { pub config: Config, pub spare: Config, pub other: Config, pub list: Vec<Config>, pub n: u32,  }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub struct Runner { app: Option<App>, runs: u32 }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut runner = Runner { app: Some(App::default()), runs: 0 }; for wake in rx { if let Some(app) = runner.app.as_mut() { app.on_wake(wake); } runner.runs += 1; }
        sender.join().unwrap();
    }
}

mod boxfield {
    use std::sync::mpsc::{channel, Receiver};
    use std::collections::{HashMap, VecDeque, BTreeMap};
    use std::cell::{RefCell, Cell};
    use std::rc::Rc;
    use std::sync::{Arc, Mutex, RwLock};
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug, Clone, PartialEq)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug, Clone)]
    pub struct App { pub config: Config, pub spare: Config, pub other: Config, pub list: Vec<Config>, pub n: u32,  }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub struct Runner { app: Box<App>, runs: u32 }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut runner = Runner { app: Box::new(App::default()), runs: 0 }; for wake in rx { runner.app.on_wake(wake); runner.runs += 1; }
        sender.join().unwrap();
    }
}

mod strs {
    use std::sync::mpsc::channel;
    use std::collections::{HashMap, VecDeque, BTreeMap};
    use std::cell::{RefCell, Cell};
    use std::rc::Rc;
    use std::borrow::Cow;
    use std::sync::{Arc, Mutex, RwLock};
    use std::sync::atomic::{AtomicBool, Ordering};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug, Clone)]
    pub struct Config { pub harness: Policy, pub theme: u8, pub name: &'static str }

    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Option<Config>, pub list: Vec<Config>, pub n: u32,  }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { if let Some(c) = self.spare.as_mut() { c.harness = Policy(3); } }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        app.spare = Some(Config::default()); app.list.push(Config::default());

        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod unboxed {
    use std::sync::mpsc::channel;
    use std::collections::{HashMap, VecDeque, BTreeMap};
    use std::cell::{RefCell, Cell};
    use std::rc::Rc;
    use std::sync::{Arc, Mutex, RwLock};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug, Clone, PartialEq)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug, Clone)]
    pub struct App { pub config: Config, pub spare: Config, pub list: Vec<Config>, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }

    impl App {

        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = *Box::new(App::default());
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();

    }
}

mod guardeddyn {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub cb: Option<Box<dyn Fn(u8)>>, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    use std::sync::Mutex;
    fn pump(app: &Mutex<App>, rx: Receiver<Wake>) {
        for wake in rx {
            app.lock().unwrap().on_wake(wake);
            let mut guard = app.lock().unwrap();
            guard.n += 1;
            guard.spare.theme = 2;
            let harness = guard.config.harness;
            println!("harness: {harness:?}");
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let app = Mutex::new(App::default());
        pump(&app, rx);
        sender.join().unwrap();
    }
}

mod guarded {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub staged: Option<Box<Config>>, pub list: Vec<Config>, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    use std::sync::Mutex;
    fn pump(app: &Mutex<App>, rx: Receiver<Wake>) {
        for wake in rx {
            app.lock().unwrap().on_wake(wake);
            if let Some(last) = app.lock().unwrap().list.last_mut() { last.harness = Policy(4); }
            for each in app.lock().unwrap().list.iter_mut() { each.harness = Policy(5); }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let app = Mutex::new(App::default());
        pump(&app, rx);
        sender.join().unwrap();
    }
}

fn main() {
    locked::run();
    borrowed::run();
    counted::run();
    asmut::run();
    boxfield::run();
    strs::run();
    unboxed::run();
    guardeddyn::run();
    guarded::run();
}

clean {
    import Trust.Binding
    namespace Held
    open Trust.Protocol
    def locked : Trust.Protocol.Binding := binds "locked::App.config.harness" ["locked::Wake::Observed"] []
    def borrowed : Trust.Protocol.Binding := binds "borrowed::App.config.harness" ["borrowed::Wake::Observed"] []
    def counted : Trust.Protocol.Binding := binds "counted::App.harness" ["counted::Wake::Observed"] []
    def asmut : Trust.Protocol.Binding := binds "asmut::App.config.harness" ["asmut::Wake::Observed"] []
    def boxfield : Trust.Protocol.Binding := binds "boxfield::App.config.harness" ["boxfield::Wake::Observed"] []
    def strs : Trust.Protocol.Binding := binds "strs::App.config.harness" ["strs::Wake::Observed"] []
    def unboxed : Trust.Protocol.Binding := binds "unboxed::App.config.harness" ["unboxed::Wake::Observed"] []
    def guardeddyn : Trust.Protocol.Binding := binds "guardeddyn::App.config.harness" ["guardeddyn::Wake::Observed"] []
    def guarded : Trust.Protocol.Binding := binds "guarded::App.config.harness" ["guarded::Wake::Observed"] []
    end Held
}

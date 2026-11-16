//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Routes to a bound field that the review of the origin analysis found by
//! reproduction (42 confirmed in its first review). Each module's binding
//! must FAIL. The first group lost a pointer that was in plain sight; the
//! second took a value of the consumer's type for nobody's, which the census
//! no longer does: every value of that type is one a consumer may run on.
//!
//! - `part`: a `&mut Config` is kept in an `Option` and reached with `if let
//!   Some(c) = &mut opt`. A pointer to PART of a variable reads back that
//!   part.
//! - `loaded`: a pointer to the field is read back through a pointer to the
//!   variable that holds it, and handed to `mem::take`. What is loaded out of
//!   a variable was made from it.
//! - `crossarm`: the pointer is borrowed in the declared arm, kept across
//!   messages, and handed to `mem::take` in another. A pointer is reported
//!   where it leaves, not only where it was made.
//! - `boxed`: `Box::new((&mut self.config, 0u8))`. A new box holds what it
//!   was given.
//! - `stored`: a pointer is stored through a pointer to part of a tuple, and
//!   written through from the tuple.
//! - `replaced`: `RefCell::replace` on the consumer's value, whose type has a
//!   pointer to its own type. A std fn that hands back a pointer and is ALSO
//!   given a value to put there writes.
//! - `beside`: a `Vec<App>` beside the consumer's value in a holder, on whose
//!   elements the consumer runs. A sibling that owns values of the consumer's
//!   type is no sibling.
//! - `channel`: `Some(&mut self.config)` is sent down a channel and written
//!   through at the other end.
//! - `twolevel`: `<&mut I as Iterator>::next` reads through two pointers to
//!   hand back the one that reaches.
//! - `handle`: a `&` of a struct with a raw pointer in a field goes to a fn
//!   that writes through it. A `&` takes out what can be copied out.
//! - `handed`: the value is handed by value to a fn and the one that comes
//!   back is written in place.
//! - `nested`: a closure in a closure in a generic fn writes the whole state
//!   through a `&mut S`. A closure's parent is read at the same instance,
//!   also when it is a closure.
//! - `job`: a thread job in a fn generic over its state replaces the state.
//! - `moved`: the consumer's value is moved to a second variable (`let mut
//!   live = app;`) and written there.
//! - `owned`: a closure that owns the value, and is no consumer itself, is
//!   called for both arms and writes it.
//! - `second`: an inline consumer runs on the second variable of the
//!   consumer's type in its body.
//! - `cloned`: a raw pointer kept in a `Copy` struct is written through after
//!   a std `clone()` of the `Option` that holds it.
//! - `fnitem`: `let take = std::mem::take::<Config>; take(&mut self.config)`:
//!   the callee is a variable whose type is the fn.
//! - `chain`: a loop-carried chain of 65 variables, longer than the old bound
//!   on the fixpoint's rounds.
//! - `guardwrite`: the twin of `guardeddyn` in the hold fixture. The drop of
//!   a lock guard is no site, but a write through the guard is one, and so
//!   is a pointer got out of it that a `Drop` impl of the crate writes
//!   through.

mod part {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let mut o = Some(&mut self.config);
                    if let Some(c) = &mut o { c.harness = Policy(9); } //~ NOTE this writes `part::App.config.harness`; reached from the arm for `part::Wake::Tick` in `part::App::on_wake`
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod loaded {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let mut one: &mut Policy = &mut self.config.harness; //~ NOTE this takes a `&mut` of `loaded::App.config.harness`; reached from the arm for `loaded::Wake::Tick` in `loaded::App::on_wake`
                    let two = &mut one;
                    std::mem::take(&mut **two);
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod crossarm {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        let mut held: Option<&mut Policy> = None;
        for wake in rx {
            match wake {
                Wake::Observed(p) => { let h = &mut app.config.harness; *h = Policy(p); held = Some(h); }
                Wake::Tick => { if let Some(h) = held.take() { std::mem::take(h); } } //~ NOTE this hands on a pointer to `crossarm::App.config.harness`; reached from the arm for `crossarm::Wake::Tick` in `crossarm::run`
                //~^ NOTE this hands on a pointer to `crossarm::App.config.harness`; reached from the arm for `crossarm::Wake::Tick` in `crossarm::run`
                Wake::Quit => {}
            }
        }
        drop(held);
        println!("harness at exit: {:?}", app.config.harness);
        sender.join().unwrap();
    }
}

mod boxed {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let b = Box::new((&mut self.config, 0u8));
                    b.0.harness = Policy(9); //~ NOTE this writes `boxed::App.config.harness`; reached from the arm for `boxed::Wake::Tick` in `boxed::App::on_wake`
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod stored {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let mut pair: (&mut Config, u8) = (&mut self.spare, 0);
                    let slot = &mut pair.0;
                    *slot = &mut self.config;
                    pair.0.harness = Policy(9); //~ NOTE this writes `stored::App.config.harness`; reached from the arm for `stored::Wake::Tick` in `stored::App::on_wake`
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod replaced {
    use std::cell::RefCell;
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    pub struct App { pub config: Config, pub spare: Config, pub parent: *const App }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn new(level: u8) -> App {
            App { config: Config { harness: Policy(level), theme: 0 }, spare: Config::default(), parent: std::ptr::null() }
        }
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {}
                Wake::Quit => {}
            }
        }
    }
    fn reset(cell: &RefCell<App>) { let _old = cell.replace(App::new(9)); } //~ NOTE this lends `RefCell::<T>::replace` a `&mut` reaching `replaced::App.config.harness`; reached from `main`, the consumer's own thread, outside `replaced::App::on_wake`
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let cell = RefCell::new(App::new(0));
        for wake in rx {
            cell.borrow_mut().on_wake(wake);
            reset(&cell);
            println!("harness: {:?}", cell.borrow().config.harness); //~ NOTE this lends `std::io::_print` a `&mut` reaching `replaced::App.config.harness`; reached from `main`, the consumer's own thread, outside `replaced::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod beside {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    #[derive(Default)]
    pub struct Session { pub app: App, pub extra: Vec<App> }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {}
                Wake::Quit => {}
            }
        }
    }
    fn poke(s: &mut Session) { s.extra[0].config.harness = Policy(9); } //~ NOTE this writes `beside::App.config.harness`; reached from `main`, the consumer's own thread, outside `beside::App::on_wake`
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut s = Session::default();
        s.extra.push(App::default());
        for wake in rx {
            s.extra[0].on_wake(wake);
            poke(&mut s);
            println!("harness: {:?}", s.extra[0].config.harness);
        }
        sender.join().unwrap();
    }
}

mod channel {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let (tx, rx) = channel::<Option<&mut Config>>();
                    let _ = tx.send(Some(&mut self.config)); //~ NOTE this lends `std::sync::mpsc::Sender::<T>::send` a `&mut` reaching `channel::App.config.harness`; reached from the arm for `channel::Wake::Tick` in `channel::App::on_wake`
                    if let Ok(Some(c)) = rx.recv() { c.harness = Policy(9); } //~ NOTE this lends `std::sync::mpsc::Receiver::<T>::recv` a `&mut` reaching `channel::App.config.harness`; reached from the arm for `channel::Wake::Tick` in `channel::App::on_wake`
                    //~^ NOTE this writes `channel::App.config.harness`; reached from the arm for `Option<&mut channel::Config>::Some` in `channel::App::on_wake` and the arm for `channel::Wake::Tick` in `channel::App::on_wake`
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod twolevel {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let arr = [&mut self.config];
                    let mut iter = arr.into_iter();
                    let mut r = &mut iter;
                    if let Some(c) = (&mut r).next() { c.harness = Policy(9); } //~ NOTE this writes `twolevel::App.config.harness`; reached from the arm for `twolevel::Wake::Tick` in `twolevel::App::on_wake`
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod handle {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    struct Handle { p: *mut u8 }
    fn poke(h: &Handle) { unsafe { *h.p = 9 } } //~ NOTE this writes a `u8` through a pointer, which may be `cloned::App.harness`; reached from `main`, the consumers' own thread, outside them
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => {
                    let h = Handle { p: &mut self.config.harness.0 }; //~ NOTE this takes a `&mut` of part of `handle::App.config.harness`; reached from the arm for `handle::Wake::Tick` in `handle::App::on_wake`
                    poke(&h);
                }
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod handed {
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
    fn turn(mut app: App, wake: Wake) -> App { app.on_wake(wake); app }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx {
            let mut next = turn(app, wake);
            next.config.harness = Policy(9); //~ NOTE this writes `handed::App.config.harness`; reached from `main`, the consumer's own thread, outside `handed::App::on_wake`
            println!("harness: {:?}", next.config.harness);
            app = next; //~ NOTE this writes a whole `handed::App` holding `handed::App.config.harness`; reached from `main`, the consumer's own thread, outside `handed::App::on_wake`
        }
        sender.join().unwrap();
    }
}

mod nested {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub trait Handler { fn fresh() -> Self; fn handle(&mut self, w: Wake); fn show(&self); }
    impl Handler for App {
        fn fresh() -> App { App { config: Config { harness: Policy(9), theme: 0 }, spare: Config::default(), n: 0 } }
        fn handle(&mut self, w: Wake) {
            match w { Wake::Observed(p) => self.config.harness = Policy(p), _ => {} }
        }
        fn show(&self) { println!("harness: {:?}", self.config.harness); }
    }
    fn drain<S: Handler>(rx: Receiver<Wake>, state: &mut S) {
        let mut run = || {
            rx.iter().for_each(|w| {
                if matches!(w, Wake::Tick) { *state = S::fresh(); } else { state.handle(w); } //~ NOTE this writes a whole `nested::App` holding `nested::App.config.harness`; reached from `main`, the consumer's own thread, outside `<nested::App as nested::Handler>::handle`
                state.show();
            });
        };
        run();
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        drain(rx, &mut app);
        sender.join().unwrap();
    }
}

mod job {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub trait Handler { fn fresh() -> Self; fn handle(&mut self, w: Wake); fn show(&self); }
    impl Handler for App {
        fn fresh() -> App { App { config: Config { harness: Policy(9), theme: 0 }, spare: Config::default(), n: 0 } }
        fn handle(&mut self, w: Wake) {
            match w { Wake::Observed(p) => self.config.harness = Policy(p), _ => {} }
        }
        fn show(&self) { println!("harness: {:?}", self.config.harness); }
    }
    fn serve<S: Handler + Send + 'static>(rx: Receiver<Wake>, mut state: S) -> std::thread::JoinHandle<S> {
        std::thread::spawn(move || {
            rx.iter().for_each(|w| {
                if matches!(w, Wake::Tick) { state = S::fresh(); } else { state.handle(w); } //~ NOTE this writes a whole `job::App` holding `job::App.config.harness`; reached from `job::serve::<job::App>::{closure#0}`, the consumer's own thread, outside `<job::App as job::Handler>::handle`
                state.show();
            });
            state
        })
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let app = serve(rx, App::default()).join().unwrap();
        sender.join().unwrap();
    }
}

mod moved {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        if let Ok(Wake::Observed(p)) = rx.recv() { app.config.harness = Policy(p); }
        println!("harness: {:?}", app.config.harness);
        let mut live = app;
        for wake in rx {
            match wake {
                Wake::Observed(p) => live.config.harness = Policy(p),
                Wake::Tick => live.config.harness = Policy(9), //~ NOTE this writes `moved::App.config.harness`; reached from the arm for `moved::Wake::Tick` in `moved::run`
                Wake::Quit => break,
            }
            println!("harness: {:?}", live.config.harness);
        }
        sender.join().unwrap();
    }
}

mod owned {
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
    fn show(app: &App) { println!("harness: {:?}", app.config.harness); }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut shadow = App::default();
        let mut app = App::default();
        let mut step = move |obs: Option<u8>| {
            match obs { Some(p) => app.config.harness = Policy(p), None => app.config.harness = Policy(9) } //~ NOTE this writes `owned::App.config.harness`; reached from the arm for `owned::Wake::Tick` in `owned::run`
            //~^ NOTE this writes `owned::App.config.harness`; reached from the arm for `owned::Wake::Tick` in `owned::run`
            show(&app);
        };
        for wake in rx {
            match wake {
                Wake::Observed(p) => { step(Some(p)); shadow.on_wake(Wake::Observed(p)); }
                Wake::Tick => step(None),
                Wake::Quit => break,
            }
        }
        sender.join().unwrap();
    }
}

mod second {
    use std::sync::mpsc::{channel, Receiver, Sender};
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default, Debug)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut template = App::default();
        let mut app = App { n: template.n + 1, ..App::default() };
        for wake in rx {
            match wake {
                Wake::Observed(p) => { template.config.harness = Policy(p); app.config.harness = Policy(p) }
                Wake::Tick => app.config.harness = Policy(9), //~ NOTE this writes `second::App.config.harness`; reached from the arm for `second::Wake::Tick` in `second::run`
                Wake::Quit => break,
            }
            println!("harness: {:?}", app.config.harness);
        }
        sender.join().unwrap();
    }
}

mod cloned {
    use std::sync::mpsc::channel;
    #[derive(Default)]
    pub struct App { pub harness: u8, pub n: u32 }
    pub enum Wake { Observed(u8), Tick }
    #[derive(Clone, Copy)]
    struct Handle { p: *mut App }
    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.harness = p,
                Wake::Tick => {
                    let o = Some(Handle { p: &raw mut *self });
                    if let Some(c) = o.clone() {
                        unsafe { (*c.p).harness = 9; } //~ NOTE this writes `cloned::App.harness`; reached from the arm for `cloned::Wake::Tick` in `cloned::App::on_wake`
                    }
                }
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); });
        let mut app = App::default();
        for wake in rx { let tick = matches!(wake, Wake::Tick); app.on_wake(wake); println!("after {}: harness={}", if tick { "Tick" } else { "Observed" }, app.harness); }
        sender.join().unwrap();
    }
}

mod fnitem {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { let take = std::mem::take::<Config>; let _ = take(&mut self.config); } //~ NOTE this lends `std::mem::take` a `&mut` reaching `fnitem::App.config.harness`; reached from the arm for `fnitem::Wake::Tick` in `fnitem::App::on_wake`
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod chain {
    use std::sync::mpsc::channel;
    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);
    #[derive(Default, Debug)]
    pub struct Config { pub harness: Policy, pub theme: u8 }
    #[derive(Default)]
    pub struct App { pub config: Config, pub spare: Config, pub n: u32 }
    pub enum Wake { Observed(u8), Tick, Quit }

    impl App {
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(p) => self.config.harness = Policy(p),
                Wake::Tick => { let mut a65: Option<&mut Config> = Some(&mut self.config);
    let mut a0: Option<&mut Config> = None;
    let mut a1: Option<&mut Config> = None;
    let mut a2: Option<&mut Config> = None;
    let mut a3: Option<&mut Config> = None;
    let mut a4: Option<&mut Config> = None;
    let mut a5: Option<&mut Config> = None;
    let mut a6: Option<&mut Config> = None;
    let mut a7: Option<&mut Config> = None;
    let mut a8: Option<&mut Config> = None;
    let mut a9: Option<&mut Config> = None;
    let mut a10: Option<&mut Config> = None;
    let mut a11: Option<&mut Config> = None;
    let mut a12: Option<&mut Config> = None;
    let mut a13: Option<&mut Config> = None;
    let mut a14: Option<&mut Config> = None;
    let mut a15: Option<&mut Config> = None;
    let mut a16: Option<&mut Config> = None;
    let mut a17: Option<&mut Config> = None;
    let mut a18: Option<&mut Config> = None;
    let mut a19: Option<&mut Config> = None;
    let mut a20: Option<&mut Config> = None;
    let mut a21: Option<&mut Config> = None;
    let mut a22: Option<&mut Config> = None;
    let mut a23: Option<&mut Config> = None;
    let mut a24: Option<&mut Config> = None;
    let mut a25: Option<&mut Config> = None;
    let mut a26: Option<&mut Config> = None;
    let mut a27: Option<&mut Config> = None;
    let mut a28: Option<&mut Config> = None;
    let mut a29: Option<&mut Config> = None;
    let mut a30: Option<&mut Config> = None;
    let mut a31: Option<&mut Config> = None;
    let mut a32: Option<&mut Config> = None;
    let mut a33: Option<&mut Config> = None;
    let mut a34: Option<&mut Config> = None;
    let mut a35: Option<&mut Config> = None;
    let mut a36: Option<&mut Config> = None;
    let mut a37: Option<&mut Config> = None;
    let mut a38: Option<&mut Config> = None;
    let mut a39: Option<&mut Config> = None;
    let mut a40: Option<&mut Config> = None;
    let mut a41: Option<&mut Config> = None;
    let mut a42: Option<&mut Config> = None;
    let mut a43: Option<&mut Config> = None;
    let mut a44: Option<&mut Config> = None;
    let mut a45: Option<&mut Config> = None;
    let mut a46: Option<&mut Config> = None;
    let mut a47: Option<&mut Config> = None;
    let mut a48: Option<&mut Config> = None;
    let mut a49: Option<&mut Config> = None;
    let mut a50: Option<&mut Config> = None;
    let mut a51: Option<&mut Config> = None;
    let mut a52: Option<&mut Config> = None;
    let mut a53: Option<&mut Config> = None;
    let mut a54: Option<&mut Config> = None;
    let mut a55: Option<&mut Config> = None;
    let mut a56: Option<&mut Config> = None;
    let mut a57: Option<&mut Config> = None;
    let mut a58: Option<&mut Config> = None;
    let mut a59: Option<&mut Config> = None;
    let mut a60: Option<&mut Config> = None;
    let mut a61: Option<&mut Config> = None;
    let mut a62: Option<&mut Config> = None;
    let mut a63: Option<&mut Config> = None;
    let mut a64: Option<&mut Config> = None;
    for _ in 0..65 { a0 = a1; a1 = a2; a2 = a3; a3 = a4; a4 = a5; a5 = a6; a6 = a7; a7 = a8; a8 = a9; a9 = a10; a10 = a11; a11 = a12; a12 = a13; a13 = a14; a14 = a15; a15 = a16; a16 = a17; a17 = a18; a18 = a19; a19 = a20; a20 = a21; a21 = a22; a22 = a23; a23 = a24; a24 = a25; a25 = a26; a26 = a27; a27 = a28; a28 = a29; a29 = a30; a30 = a31; a31 = a32; a32 = a33; a33 = a34; a34 = a35; a35 = a36; a36 = a37; a37 = a38; a38 = a39; a39 = a40; a40 = a41; a41 = a42; a42 = a43; a43 = a44; a44 = a45; a45 = a46; a46 = a47; a47 = a48; a48 = a49; a49 = a50; a50 = a51; a51 = a52; a52 = a53; a53 = a54; a54 = a55; a55 = a56; a56 = a57; a57 = a58; a58 = a59; a59 = a60; a60 = a61; a61 = a62; a62 = a63; a63 = a64; a64 = a65; a65 = None; }
    if let Some(c) = a0 { c.harness = Policy(9); } } //~ NOTE this writes `chain::App.config.harness`; reached from the arm for `chain::Wake::Tick` in `chain::App::on_wake`
                Wake::Quit => {}
            }
        }
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || { let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); let _ = tx.send(Wake::Quit); });
        let mut app = App::default();
        for wake in rx { app.on_wake(wake); println!("harness: {:?}", app.config.harness); }
        sender.join().unwrap();
    }
}

mod guardwrite {
    use std::sync::mpsc::{channel, Receiver};
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
    struct Reset<'a>(&'a mut Config);
    impl Drop for Reset<'_> {
        fn drop(&mut self) { self.0.harness = Policy(0); } //~ NOTE this writes `guardwrite::App.config.harness`; reached from `main`, the consumer's own thread, outside `guardwrite::App::on_wake`
    }
    fn pump(app: &Mutex<App>, rx: Receiver<Wake>) {
        for wake in rx {
            app.lock().unwrap().on_wake(wake);
            app.lock().unwrap().config.harness = Policy(9); //~ NOTE this writes `guardwrite::App.config.harness`; reached from `main`, the consumer's own thread, outside `guardwrite::App::on_wake`
            let mut guard = app.lock().unwrap();
            let _reset = Reset(&mut guard.config);
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
    part::run();
    loaded::run();
    crossarm::run();
    boxed::run();
    stored::run();
    replaced::run();
    beside::run();
    channel::run();
    twolevel::run();
    handle::run();
    handed::run();
    nested::run();
    job::run();
    moved::run();
    owned::run();
    second::run();
    cloned::run();
    fnitem::run();
    chain::run();
    guardwrite::run();
}

clean {
    import Trust.Binding
    namespace Values
    open Trust.Protocol
    def part : Trust.Protocol.Binding := binds "part::App.config.harness" ["part::Wake::Observed"] []
    def loaded : Trust.Protocol.Binding := binds "loaded::App.config.harness" ["loaded::Wake::Observed"] []
    def crossarm : Trust.Protocol.Binding := binds "crossarm::App.config.harness" ["crossarm::Wake::Observed"] []
    def boxed : Trust.Protocol.Binding := binds "boxed::App.config.harness" ["boxed::Wake::Observed"] []
    def stored : Trust.Protocol.Binding := binds "stored::App.config.harness" ["stored::Wake::Observed"] []
    def replaced : Trust.Protocol.Binding := binds "replaced::App.config.harness" ["replaced::Wake::Observed"] []
    def beside : Trust.Protocol.Binding := binds "beside::App.config.harness" ["beside::Wake::Observed"] []
    def channel : Trust.Protocol.Binding := binds "channel::App.config.harness" ["channel::Wake::Observed"] []
    def twolevel : Trust.Protocol.Binding := binds "twolevel::App.config.harness" ["twolevel::Wake::Observed"] []
    def handle : Trust.Protocol.Binding := binds "handle::App.config.harness" ["handle::Wake::Observed"] []
    def handed : Trust.Protocol.Binding := binds "handed::App.config.harness" ["handed::Wake::Observed"] []
    def nested : Trust.Protocol.Binding := binds "nested::App.config.harness" ["nested::Wake::Observed"] []
    def job : Trust.Protocol.Binding := binds "job::App.config.harness" ["job::Wake::Observed"] []
    def moved : Trust.Protocol.Binding := binds "moved::App.config.harness" ["moved::Wake::Observed"] []
    def owned : Trust.Protocol.Binding := binds "owned::App.config.harness" ["owned::Wake::Observed"] []
    def second : Trust.Protocol.Binding := binds "second::App.config.harness" ["second::Wake::Observed"] []
    def cloned : Trust.Protocol.Binding := binds "cloned::App.harness" ["cloned::Wake::Observed"] []
    def fnitem : Trust.Protocol.Binding := binds "fnitem::App.config.harness" ["fnitem::Wake::Observed"] []
    def chain : Trust.Protocol.Binding := binds "chain::App.config.harness" ["chain::Wake::Observed"] []
    def guardwrite : Trust.Protocol.Binding := binds "guardwrite::App.config.harness" ["guardwrite::Wake::Observed"] []
    end Values
}
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.part` binds `part::App.config.harness` to the arm(s) for `part::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.loaded` binds `loaded::App.config.harness` to the arm(s) for `loaded::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.crossarm` binds `crossarm::App.config.harness` to the arm(s) for `crossarm::Wake::Observed`, and 2 of its 4 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.boxed` binds `boxed::App.config.harness` to the arm(s) for `boxed::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.stored` binds `stored::App.config.harness` to the arm(s) for `stored::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.replaced` binds `replaced::App.config.harness` to the arm(s) for `replaced::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.beside` binds `beside::App.config.harness` to the arm(s) for `beside::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.channel` binds `channel::App.config.harness` to the arm(s) for `channel::Wake::Observed`, and 3 of its 4 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.twolevel` binds `twolevel::App.config.harness` to the arm(s) for `twolevel::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.handle` binds `handle::App.config.harness` to the arm(s) for `handle::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.handed` binds `handed::App.config.harness` to the arm(s) for `handed::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.nested` binds `nested::App.config.harness` to the arm(s) for `nested::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.job` binds `job::App.config.harness` to the arm(s) for `job::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.moved` binds `moved::App.config.harness` to the arm(s) for `moved::Wake::Observed`, and 1 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.owned` binds `owned::App.config.harness` to the arm(s) for `owned::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.second` binds `second::App.config.harness` to the arm(s) for `second::Wake::Observed`, and 1 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.cloned` binds `cloned::App.harness` to the arm(s) for `cloned::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.fnitem` binds `fnitem::App.config.harness` to the arm(s) for `fnitem::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.chain` binds `chain::App.config.harness` to the arm(s) for `chain::Wake::Observed`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^^^^^^^^^^^^^^^ ERROR `Values.guardwrite` binds `guardwrite::App.config.harness` to the arm(s) for `guardwrite::Wake::Observed`, and 2 of its 3 write site(s) can be reached from elsewhere

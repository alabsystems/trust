//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A binding fails when its field can be written by a route the declaration
//! does not name, however the write is reached. Each field here has one
//! declared arm and one more writer, of a kind that once passed:
//!
//! - `hook`: a fn pointer the consumer runs after every message calls the
//!   helper that writes. The census cannot say which arm makes that call.
//! - `owner`: `main` writes into the `App` it owns, between messages.
//! - `kept`: a `&mut` of the field is taken in the declared arm and written
//!   through in another (a second consumer, `keep`, so that the borrow may
//!   live across messages). The write is where it is made.
//! - `raw`: a `&raw const` of the field, cast to `*mut` and written through.
//! - `wiped`: a generic fn hands its pointer to a blanket impl that writes a
//!   whole value. The impl is read at the instance that runs.
//! - `opt`: the pointer goes to generic code inside an `Option`, and comes
//!   out of it there as a pointer whose origin that body cannot see.

use std::sync::mpsc::{Receiver, channel};

#[derive(Default)]
struct Config {
    wiped: u8,
    opt: u8,
}

struct App {
    hook: u8,
    owner: u8,
    kept: u8,
    raw: u8,
    config: Config,
    hooks: Vec<fn(&mut App)>,
    n: u32,
}

enum Wake {
    Declared(u8),
    Arm,
    Fire,
    Raw,
    Wipe,
    Opt,
    Tick,
}

trait Wipe {
    fn wipe(&mut self);
}

impl<T: Default> Wipe for T {
    fn wipe(&mut self) {
        *self = T::default(); //~ NOTE this writes a whole `Config` holding `App.config.wiped`; reached from the arm for `Wake::Wipe` in `App::run`
    }
}

fn wipe_it<T: Wipe>(slot: &mut T) {
    slot.wipe()
}

fn reset_opt<T: Default>(slot: Option<&mut T>) {
    if let Some(slot) = slot {
        *slot = T::default(); //~ NOTE this writes a whole `Config` holding `App.config.opt`; reached from the arm for `Wake::Opt` in `App::run`
    }
}

fn rehook(app: &mut App) {
    app.set_hook(0);
}

impl App {
    fn set_hook(&mut self, value: u8) {
        self.hook = value; //~ NOTE this writes `App.hook`; reached from an indirect call or a hand-off
    }

    fn keep(&mut self, rx: &Receiver<Wake>) {
        let mut scratch = 0u8;
        let mut slot: &mut u8 = &mut scratch;
        while let Ok(wake) = rx.try_recv() {
            match wake {
                Wake::Arm => slot = &mut self.kept,
                Wake::Fire => *slot = 7, //~ NOTE this writes `App.kept`; reached from the arm for `Wake::Fire` in `App::keep`
                _ => self.n += 1,
            }
        }
    }

    fn run(&mut self, rx: &Receiver<Wake>) {
        while let Ok(wake) = rx.try_recv() {
            match wake {
                Wake::Declared(value) => {
                    self.set_hook(value);
                    self.owner = value;
                    self.raw = value;
                    self.config.wiped = value;
                    self.config.opt = value;
                }
                Wake::Arm | Wake::Fire => self.n += 1,
                Wake::Raw => {
                    let p = &raw const self.raw; //~ NOTE this takes a raw pointer to `App.raw`; reached from the arm for `Wake::Raw` in `App::run`
                    unsafe { (p as *mut u8).write(9) }
                }
                Wake::Wipe => wipe_it(&mut self.config),
                Wake::Opt => reset_opt(Some(&mut self.config)),
                Wake::Tick => self.n += 1,
            }
            for hook in self.hooks.clone() {
                hook(self);
            }
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Declared(1));
        let _ = tx.send(Wake::Arm);
        let _ = tx.send(Wake::Fire);
        let _ = tx.send(Wake::Raw);
        let _ = tx.send(Wake::Wipe);
        let _ = tx.send(Wake::Opt);
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App {
        hook: 0,
        owner: 0,
        kept: 0,
        raw: 0,
        config: Config::default(),
        hooks: vec![rehook],
        n: 0,
    };
    sender.join().unwrap();
    app.run(&rx);
    app.owner = 9; //~ NOTE this writes `App.owner`; reached from `main`, the consumers' own thread, outside them
    app.keep(&rx);
}

clean {
    import Trust.Binding
    namespace Routes
    open Trust.Protocol
    def hook : Trust.Protocol.Binding := binds "hook" ["Declared"] []
    def owner : Trust.Protocol.Binding := binds "owner" ["Declared"] []
    def kept : Trust.Protocol.Binding := binds "kept" ["Arm"] []
    def raw : Trust.Protocol.Binding := binds "raw" ["Declared"] []
    def wiped : Trust.Protocol.Binding := binds "config.wiped" ["Declared"] []
    def opt : Trust.Protocol.Binding := binds "config.opt" ["Declared"] []
    end Routes
}
//~^^^^^^^^ ERROR `Routes.hook` binds `App.hook` to the arm(s) for `Declared`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^ ERROR `Routes.owner` binds `App.owner` to the arm(s) for `Declared`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^ ERROR `Routes.kept` binds `App.kept` to the arm(s) for `Arm`, and 1 of its 1 write site(s) can be reached from elsewhere
//~^^^^^^^^ ERROR `Routes.raw` binds `App.raw` to the arm(s) for `Declared`, and 1 of its 2 write site(s) can be reached from elsewhere
//~^^^^^^^^ ERROR `Routes.wiped` binds `App.config.wiped` to the arm(s) for `Declared`, and 2 of its 3 write site(s) can be reached from elsewhere
//~^^^^^^^^ ERROR `Routes.opt` binds `App.config.opt` to the arm(s) for `Declared`, and 2 of its 3 write site(s) can be reached from elsewhere

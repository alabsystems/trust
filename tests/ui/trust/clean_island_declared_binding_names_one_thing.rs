//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Every name in a binding names one thing, or the binding is an error. A
//! short name must not let a second definition through:
//!
//! - `twice`: `App::carry_over` is a fn in two modules. A longer path tells
//!   them apart (`exact`, which holds).
//! - `nobody`: a carried-by entry that names no fn is a typo.
//! - `either`: `Set` is a variant of both messages the field's consumers
//!   dispatch on. `Wake::Set` names one (`exact`).
//! - `where_`: `level` is a field of two consumer types. `App.level` names
//!   one (`rooted`, which holds).

use std::sync::mpsc::{Receiver, channel};

mod reload {
    impl super::App {
        pub(super) fn carry_over(&mut self, level: u8) {
            let kept = self.level;
            self.level = level;
            self.level = kept;
        }
    }
}

mod rogue {
    pub(super) struct App;

    impl App {
        pub(super) fn carry_over(&self, app: &mut super::App) {
            app.n += 1;
        }
    }
}

pub struct App {
    level: u8,
    n: u32,
}

struct Other {
    level: u8,
}

enum Wake {
    Set(u8),
    Reload(u8),
    Rogue,
}

enum Reply {
    Set(u8),
    Done,
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Set(level) => self.level = level,
            Wake::Reload(level) => self.carry_over(level),
            Wake::Rogue => self.n += 1,
        }
    }

    fn on_reply(&mut self, reply: Reply) {
        match reply {
            Reply::Set(_) => self.n += 1,
            Reply::Done => self.n += 2,
        }
    }
}

impl Other {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Set(level) => self.level = level,
            _ => {}
        }
    }
}

fn pump(app: &mut App, other: &mut Other, rx: Receiver<Wake>, replies: Receiver<Reply>) {
    for wake in rx {
        match wake {
            wake @ Wake::Rogue => other.on_wake(wake),
            wake => app.on_wake(wake),
        }
    }
    for reply in replies {
        app.on_reply(reply);
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let (reply_tx, replies) = channel::<Reply>();
    let sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Set(1));
        let _ = tx.send(Wake::Reload(2));
        let _ = tx.send(Wake::Rogue);
        let _ = reply_tx.send(Reply::Set(3));
        let _ = reply_tx.send(Reply::Done);
    });
    let mut app = App { level: 0, n: 0 };
    let mut other = Other { level: 0 };
    rogue::App.carry_over(&mut app);
    pump(&mut app, &mut other, rx, replies);
    sender.join().unwrap();
}

clean {
    import Trust.Binding
    namespace Names
    open Trust.Protocol
    def twice : Trust.Protocol.Binding := binds "App.level" ["Wake::Set"] ["App::carry_over"]
    def nobody : Trust.Protocol.Binding := binds "App.level" ["Wake::Set"] ["App::carry"]
    def either : Trust.Protocol.Binding := binds "App.level" ["Set"] ["reload::App::carry_over"]
    def where_ : Trust.Protocol.Binding := binds "level" ["Wake::Set"] ["reload::App::carry_over"]
    def exact : Trust.Protocol.Binding := binds "App.level" ["Wake::Set"] ["reload::App::carry_over"]
    end Names
}
//~^^^^^^^ ERROR `Names.twice` names `App::carry_over` as carrying the value over, which is 2 fns: `crate::reload::App::carry_over` and `crate::rogue::App::carry_over`
//~^^^^^^^ ERROR `Names.nobody` names `App::carry` as carrying the value over, which is no fn of this crate
//~^^^^^^^ ERROR `Names.either` names `Set` (`Reply` and `Wake`) as a writer of `App.level`, a variant of more than one message its consumers dispatch on
//~^^^^^^^ ERROR `Names.where_` binds the field path `level`, which is 2 fields: `App.level` and `Other.level`
//~^^^^^^^ NOTE binding `Names.exact` holds: `App.level` is written only from the arm(s) for `Wake::Set`; 1 write site(s) checked, and 2 more in the fn(s) it says carry the value over

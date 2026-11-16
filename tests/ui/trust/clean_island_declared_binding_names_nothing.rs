//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A binding that names nothing is an error, never one that holds vacuously.
//! `typo` names a writer that is no variant of the message the field's
//! consumer dispatches on, and `lost` names a field path no consumer has. So
//! is a write from another thread: `elsewhere` binds the field to the arm for
//! `Observed`, and the `reset` thread writes a `Config` through a pointer,
//! which by type may be the bound one.

use std::sync::mpsc::channel;

#[derive(Clone, Copy)]
struct Policy(u8);

struct Config {
    harness: Policy,
}

struct App {
    config: Config,
    level: u8,
}

enum Wake {
    Observed(u8),
    Tick,
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(level) => self.config.harness = Policy(level),
            Wake::Tick => self.level += 1,
        }
    }
}

fn reset(config: &mut Config) {
    *config = Config { harness: Policy(0) }; //~ NOTE this writes a whole `Config` holding `App.config.harness`; reached from the thread `main::{closure#0}`
}

clean {
    import Trust.Binding
    namespace HarnessPolicy
    open Trust.Protocol

    def typo : Trust.Protocol.Binding :=
      binds "level" ["Tik"] []

    def lost : Trust.Protocol.Binding :=
      binds "config.missing" ["Observed"] []

    def elsewhere : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []

    end HarnessPolicy
}
//~^^^^^^^^^^^ ERROR `HarnessPolicy.typo` names `Tik` as a writer of `App.level`, which is no variant of `Wake`
//~^^^^^^^^^ ERROR `HarnessPolicy.lost` binds the field path `config.missing`, and no message consumer has an argument with that path
//~^^^^^^^ ERROR `HarnessPolicy.elsewhere` binds `App.config.harness` to the arm(s) for `Observed`, and 1 of its 2 write site(s) can be reached from elsewhere

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _other = std::thread::spawn(move || {
        let mut own = Config { harness: Policy(2) };
        reset(&mut own);
        let _ = tx.send(Wake::Observed(own.harness.0));
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App { config: Config { harness: Policy(0) }, level: 0 };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = (app.config.harness.0, app.level);
}

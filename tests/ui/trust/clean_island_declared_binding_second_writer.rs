//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A second writer of a bound field fails the build. The island binds
//! `config.harness` to the arm for `Wake::Observed`. The code also writes it
//! from the arm for `Wake::Reset`, swaps the whole `Config` from the arm for
//! `Wake::Prepared` (not declared as a carry-over here), and writes it once
//! before the dispatch, for every message. Each is named at its own line, and
//! the error is at the binding. This is the shape of the race the binding is
//! for: a write of the policy that the model does not have. No flag asks for
//! the check: the binding does.

use std::sync::mpsc::channel;

#[derive(Clone, Copy)]
struct Policy(u8);

struct Config {
    harness: Policy,
    theme: u8,
}

struct App {
    config: Config,
    seen: u32,
}

enum Wake {
    Observed(u8),
    Prepared(Config),
    Reset,
    Tick,
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        if self.seen == 0 {
            self.config.harness = Policy(9); //~ NOTE this writes `App.config.harness`; reached from `App::on_wake` outside its arms
        }
        self.seen += 1;
        match wake {
            Wake::Observed(level) => self.adopt(level),
            Wake::Prepared(config) => self.config = config, //~ NOTE this writes a whole `Config` holding `App.config.harness`; reached from the arm for `Wake::Prepared` in `App::on_wake`
            Wake::Reset => self.config.harness = Policy(0), //~ NOTE this writes `App.config.harness`; reached from the arm for `Wake::Reset` in `App::on_wake`
            Wake::Tick => self.config.theme += 1,
        }
    }

    fn adopt(&mut self, level: u8) {
        self.config.harness = Policy(level);
    }
}

clean {
    import Trust.Binding
    namespace HarnessPolicy
    open Trust.Protocol

    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []

    end HarnessPolicy
}
//~^^^^^ ERROR `HarnessPolicy.policy` binds `App.config.harness` to the arm(s) for `Observed`, and 3 of its 4 write site(s) can be reached from elsewhere

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _watcher = std::thread::spawn(move || {
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Prepared(Config { harness: Policy(0), theme: 2 }));
        let _ = tx.send(Wake::Reset);
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App { config: Config { harness: Policy(0), theme: 0 }, seen: 0 };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = (app.config.harness.0, app.config.theme);
}

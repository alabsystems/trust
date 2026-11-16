//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off] compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A binding ties a model to the code beside it. The island declares that the
//! field `config.harness` (of the type the message consumer runs on) is
//! written only from the arm for `Wake::Observed`, and that `App::carry_over`
//! only carries the value over. The compiler finds the binding by its kernel
//! type, with no flag, finds every write of the field, and checks each against
//! it: `adopt` writes the field and is reached only from the arm for
//! `Observed`; `carry_over` swaps the whole `Config` and is the declared
//! carry-over; the arm for `Tick` writes a sibling field. So the binding
//! holds, and a note at its definition says what was checked. (The
//! expectations sit outside the island: its body is Clean text.)
//!
//! A binding that holds for want of a write is a warning: `loose` also allows
//! the arm for `Tick`, from which no write of the field is reached.

use std::sync::mpsc::channel;

#[derive(Clone, Copy)]
struct Policy(u8);

struct Config {
    harness: Policy,
    theme: u8,
}

struct App {
    config: Config,
}

enum Wake {
    Observed(u8),
    Prepared(Config),
    Tick,
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(level) => self.adopt(level),
            Wake::Prepared(config) => self.carry_over(config),
            Wake::Tick => self.config.theme += 1,
        }
    }

    fn adopt(&mut self, level: u8) {
        self.config.harness = Policy(level);
    }

    /// The config lane's whole-`Config` swap: it keeps the policy in force.
    fn carry_over(&mut self, mut config: Config) {
        config.harness = self.config.harness;
        self.config = config;
    }
}

clean {
    import Trust.Protocol
    namespace HarnessPolicy
    open Trust.Protocol

    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] ["App::carry_over"]

    def loose : Trust.Protocol.Binding :=
      binds "config.harness" ["Wake::Observed", "Tick"] ["carry_over"]

    end HarnessPolicy
}
//~^^^^^^^^ NOTE binding `HarnessPolicy.policy` holds: `App.config.harness` is written only from the arm(s) for `Observed`; 1 write site(s) checked, and 1 more in the fn(s) it says carry the value over (`App::carry_over`)
//~^^^^^^ WARN binding `HarnessPolicy.loose` holds: `App.config.harness` is written only from the arm(s) for `Wake::Observed` and `Tick`; 1 write site(s) checked, and 1 more in the fn(s) it says carry the value over (`App::carry_over`). No write of the field is reached from the arm(s) for `Tick`

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _watcher = std::thread::spawn(move || {
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Prepared(Config { harness: Policy(0), theme: 2 }));
        let _ = tx.send(Wake::Tick);
    });
    let mut app = App { config: Config { harness: Policy(0), theme: 0 } };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = (app.config.harness.0, app.config.theme);
}

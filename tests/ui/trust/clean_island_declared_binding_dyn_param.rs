//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The twin of `clean_island_declared_binding_dyn_param_holds.rs`: the
//! handler that `fn handlers<Req>` boxes as a `dyn Handler<Req>` WRITES the
//! bound field, and the arm for `Wake::Tick` runs it. The census reads that
//! vtable per instance (`handlers::<u8>`), finds the write, and the binding
//! FAILS: reading the vtable per instance, rather than asking the compiler
//! for a trait ref that names a parameter, loses none of it.

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

trait Handler<Req> {
    fn handle(&self, app: &mut App, r: &Req) -> u8;
}
struct Echo;
impl<Req> Handler<Req> for Echo {
    fn handle(&self, app: &mut App, _r: &Req) -> u8 {
        app.config.harness = Policy(9); //~ NOTE this writes `App.config.harness`; reached from an indirect call or a hand-off
        app.config.theme
    }
}
fn handlers<Req: 'static>() -> Vec<Box<dyn Handler<Req>>> {
    vec![Box::new(Echo)]
}

impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(level) => self.adopt(level),
            Wake::Prepared(config) => self.carry_over(config),
            Wake::Tick => {
                for h in handlers::<u8>() {
                    self.config.theme += h.handle(self, &1);
                }
            }
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

    end HarnessPolicy
}
//~^^^^^ ERROR `HarnessPolicy.policy` binds `App.config.harness` to the arm(s) for `Observed`, and 1 of its 2 write site(s) can be reached from elsewhere

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

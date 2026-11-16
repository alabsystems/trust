//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A declared binding in a crate whose generic code makes a CONCRETE type a
//! `dyn` of a trait generic at its parameter (`Box<Echo> as Box<dyn
//! Handler<Req>>` in `fn handlers<Req>`): the spawn census the binding runs
//! reads that vtable per instance, and the binding HOLDS. Review 4 of the
//! review-14 build: the census read it as concrete, because `Echo` names no
//! parameter, and asked the compiler for `<Echo as Handler<Req>>::handle`: a
//! compiler panic at every binding of such a crate. The handler here writes
//! nothing; in `_dyn_param.rs` it writes the bound field, from an arm the
//! binding does not allow, and the binding fails.

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

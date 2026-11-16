//@ needs-trust-verify
//@ revisions: off incr
//@ compile-flags: -Ztrust-verify=off
//@[incr] incremental
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A binding that holds must not fail for a write the field never gets. Each
//! of these once did:
//!
//! - `dirty`: `mem::take(&mut self.redraw)` is a `&mut` of a SIBLING of the
//!   same type. A pointer the body borrowed itself is judged by the place.
//! - `policy`: `pump` hands the message it holds on to `apply`, which
//!   dispatches it. The innermost dispatch decides the arm, also for the
//!   messages the `Replay` arm hands it again later.
//! - `id`: an `Id<App>` only names `App`; writing one replaces no `App`.
//! - `level`: the consumer is a closure that captures `self`.
//! - `solo`: a message with one variant, destructured through the receive's
//!   own wrapper.
//!
//! The `incr` revision is the same build under incremental compilation, where
//! HIR spans carry a parent: the binding is still found to be checked.

use std::marker::PhantomData;
use std::sync::mpsc::{Receiver, channel};

struct Id<T>(u32, PhantomData<fn() -> T>);

struct App {
    dirty: bool,
    redraw: bool,
    policy: u8,
    id: Id<App>,
    level: u8,
    solo: u8,
    deferred: Vec<Wake>,
    n: u32,
}

enum Wake {
    Dirty,
    Clear,
    Observed(u8),
    Rename,
    Replay,
    Defer,
    Quit,
}

enum Solo {
    Only(u8),
}

impl App {
    fn apply(&mut self, wake: Wake) {
        match wake {
            Wake::Dirty => self.dirty = true,
            Wake::Clear => {
                let _ = std::mem::take(&mut self.redraw);
            }
            Wake::Observed(policy) => self.policy = policy,
            Wake::Rename => self.id = Id(self.id.0 + 1, PhantomData),
            Wake::Replay => {
                for wake in std::mem::take(&mut self.deferred) {
                    self.apply(wake);
                }
            }
            Wake::Defer => self.deferred.push(Wake::Observed(7)),
            Wake::Quit => {}
        }
    }

    fn pump(&mut self, rx: &Receiver<Wake>) {
        while let Ok(wake) = rx.recv() {
            match wake {
                Wake::Quit => return,
                other => self.apply(other),
            }
        }
    }

    fn levels(&mut self, rx: &Receiver<Wake>) {
        rx.try_iter().for_each(|wake| match wake {
            Wake::Observed(level) => self.level = level,
            _ => self.n += 1,
        });
    }

    fn solos(&mut self, rx: &Receiver<Solo>) {
        while let Ok(Solo::Only(k)) = rx.recv() {
            self.solo = k;
        }
    }
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let (solo_tx, solo_rx) = channel::<Solo>();
    let sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Dirty);
        let _ = tx.send(Wake::Clear);
        let _ = tx.send(Wake::Observed(1));
        let _ = tx.send(Wake::Rename);
        let _ = tx.send(Wake::Defer);
        let _ = tx.send(Wake::Replay);
        let _ = tx.send(Wake::Quit);
        let _ = tx.send(Wake::Observed(2));
        let _ = solo_tx.send(Solo::Only(3));
    });
    let mut app = App {
        dirty: false,
        redraw: false,
        policy: 0,
        id: Id(0, PhantomData),
        level: 0,
        solo: 0,
        deferred: Vec::new(),
        n: 0,
    };
    app.pump(&rx);
    sender.join().unwrap();
    app.levels(&rx);
    app.solos(&solo_rx);
}

clean {
    import Trust.Binding
    namespace Precisely
    open Trust.Protocol
    def dirty : Trust.Protocol.Binding := binds "dirty" ["Wake::Dirty"] []
    def policy : Trust.Protocol.Binding := binds "policy" ["Wake::Observed"] []
    def id : Trust.Protocol.Binding := binds "id" ["Wake::Rename"] []
    def level : Trust.Protocol.Binding := binds "level" ["Wake::Observed"] []
    def solo : Trust.Protocol.Binding := binds "solo" ["Only"] []
    end Precisely
}

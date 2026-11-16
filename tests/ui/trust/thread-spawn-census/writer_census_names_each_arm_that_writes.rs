//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-writer-census=config.harness
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=config.harness
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Temporal P3, the writer census (`-Ztrust-writer-census=<field path>`): the
//! path names a field of a message consumer's `self`, here `App.config.harness`,
//! as aterm's harness policy is. Every write that may overlap it is named with
//! what reaches it: `adopt` writes the field itself and is called from the arm
//! for `Observed`; the arm for `Prepared` writes a whole `Config`, which holds
//! it (the lane's `self.config = config` that the design moves the field out of);
//! the arm for `Swap` lends `&mut self.config` to `std::mem::replace`, which can
//! write a whole value; the arm for `Tick` writes a sibling field, which is not
//! named. The summary at the consumer lists the arms: a protocol with one writer
//! would show one. A thread that writes its own `Config` through a pointer is
//! named too, since the census matches by type. The census runs the send and
//! consumer censuses it needs without their notes.

use std::sync::mpsc::channel;

#[derive(Clone, Copy)]
struct Policy(u8);

/// `name` gives `Config` drop glue, so `self.config = config` is elaborated
/// into a drop and an assignment repeated on the unwind path: one site.
struct Config {
    harness: Policy,
    theme: u8,
    name: String,
}

struct App {
    config: Config,
}

enum Wake {
    Observed(u8),
    Prepared(Config),
    Swap(Config),
    Tick,
}

impl App {
    fn on_wake(&mut self, wake: Wake) { //~ NOTE writer census: `App.config.harness` may be written at 4 site(s), from the 3 arms for `Wake::Observed`, `Wake::Prepared` and `Wake::Swap` in `App::on_wake` and the thread `main::{closure#1}`
        match wake {
            Wake::Observed(level) => self.adopt(level),
            Wake::Prepared(config) => self.config = config, //~ NOTE writer census: this writes a whole `Config` holding `App.config.harness`; reached from the arm for `Wake::Prepared` in `App::on_wake`
            Wake::Swap(config) => drop(std::mem::replace(&mut self.config, config)), //~ NOTE a `&mut` reaching `App.config.harness`; reached from the arm for `Wake::Swap` in `App::on_wake`
            Wake::Tick => self.config.theme += 1,
        }
    }

    fn adopt(&mut self, level: u8) {
        self.config.harness = Policy(level); //~ NOTE writer census: this writes `App.config.harness`; reached from the arm for `Wake::Observed` in `App::on_wake`
    }
}

fn reset(config: &mut Config) {
    *config = Config { harness: Policy(0), theme: 0, name: String::new() }; //~ NOTE writer census: this writes a whole `Config` holding `App.config.harness`; reached from the thread `main::{closure#1}`
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let watcher = tx.clone();
    let _watch = std::thread::spawn(move || {
        let _ = watcher.send(Wake::Observed(1));
        let _ = watcher.send(Wake::Tick);
    });
    let _lane = std::thread::spawn(move || {
        let mut own = Config { harness: Policy(2), theme: 1, name: String::from("lane") };
        reset(&mut own);
        let _ = tx.send(Wake::Prepared(own));
    });
    let mut app = App { config: Config { harness: Policy(0), theme: 0, name: String::new() } };
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    let _ = (app.config.harness.0, app.config.name.len());
}

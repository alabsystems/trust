//@ needs-trust-verify
//@ revisions: harness pair raw
//@[harness] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=config.harness
//@[pair] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=pair.0
//@[raw] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=r#type
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! What is and is not a site of the writer census, with a `Box` on the path
//! (`App.config` is a `Box<Config>`). A write of a sibling field of the boxed
//! `Config` is not one. Replacing the `Box` is. A `&mut` of the `Config` handed
//! to a local fn whose parameter is generic, or to a trait's provided method,
//! is no site at the call: the callee is read at the instance called, where
//! its `*slot = ..` writes a whole `Config`, and the site is there. A `&mut` of
//! the field itself is one site however it is then used: `mem::swap` with a
//! local is one site, not two, and the other argument, a pointer to the
//! body's own value, is none. A raw pointer to the `Config`, named first and
//! handed to `ptr::write` after, is found through the local. A whole value
//! that HOLDS the consumer's `self` (`Host`) is a site too. The path may also
//! name a tuple field (`pair.0`) or a raw identifier (`r#type`).

use std::sync::mpsc::channel;

#[derive(Clone, Copy, Default)]
struct Policy(u8);

#[derive(Default)]
struct Config {
    harness: Policy,
    theme: u16,
}

struct App {
    config: Box<Config>,
    pair: (u8, u8),
    r#type: u8,
}

struct Host {
    app: App,
    restarts: u32,
}

enum Wake {
    Theme,
    Boxed(Config),
    Reset,
    Put(Config),
    Swap(Policy),
    Raw(Config),
    Pair,
    Kind,
}

fn reset<T: Default>(slot: &mut T) {
    *slot = T::default(); //[harness]~ NOTE writer census: this writes a whole `Config` holding `App.config.harness`; reached from the arm for `Wake::Reset` in `App::on_wake`
}

trait Put: Sized {
    fn put(&mut self, new: Self) {
        *self = new; //[harness]~ NOTE writer census: this writes a whole `Config` holding `App.config.harness`; reached from the arm for `Wake::Put` in `App::on_wake`
    }
}

impl Put for Config {}

impl App {
    fn on_wake(&mut self, wake: Wake) { //[harness]~ NOTE writer census: `App.config.harness` may be written at 6 site(s), from the 5 arms for `Wake::Boxed`, `Wake::Reset`, `Wake::Put`, `Wake::Swap` and `Wake::Raw` in `App::on_wake` and `main`, the consumer's own thread, outside `App::on_wake`
        match wake {
            Wake::Theme => self.config.theme += 1,
            Wake::Boxed(config) => self.config = Box::new(config), //[harness]~ NOTE writer census: this writes a whole `Box<Config>` holding `App.config.harness`; reached from the arm for `Wake::Boxed` in `App::on_wake`
            Wake::Reset => reset(&mut *self.config),
            Wake::Put(config) => self.config.put(config),
            Wake::Swap(mut policy) => std::mem::swap(&mut self.config.harness, &mut policy), //[harness]~ NOTE writer census: this takes a `&mut` of `App.config.harness`; reached from the arm for `Wake::Swap` in `App::on_wake`
            Wake::Raw(config) => {
                let slot: *mut Config = &mut *self.config;
                unsafe { std::ptr::write(slot, config) } //[harness]~ NOTE writer census: this lends `std::ptr::write` a `&mut` reaching `App.config.harness`; reached from the arm for `Wake::Raw` in `App::on_wake`
            }
            Wake::Pair => self.pair.0 += 1, //[pair]~ NOTE writer census: this writes `App.pair.0`; reached from the arm for `Wake::Pair` in `App::on_wake`
            Wake::Kind => self.r#type += 1, //[raw]~ NOTE writer census: this writes `App.r#type`; reached from the arm for `Wake::Kind` in `App::on_wake`
        }
    }
}

fn restart(host: &mut Host) {
    host.restarts += 1;
    *host = Host { //[harness]~ NOTE writer census: this writes a whole `Host` holding `App.config.harness`; reached from `main`, the consumer's own thread, outside `App::on_wake`
        app: App { config: Box::default(), pair: (0, 0), r#type: 0 },
        restarts: host.restarts,
    };
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Theme);
        let _ = tx.send(Wake::Boxed(Config::default()));
        let _ = tx.send(Wake::Reset);
        let _ = tx.send(Wake::Put(Config::default()));
        let _ = tx.send(Wake::Swap(Policy(1)));
        let _ = tx.send(Wake::Raw(Config::default()));
        let _ = tx.send(Wake::Pair);
        let _ = tx.send(Wake::Kind);
    });
    let mut host =
        Host { app: App { config: Box::default(), pair: (0, 0), r#type: 0 }, restarts: 0 };
    restart(&mut host);
    while let Ok(wake) = rx.recv() {
        host.app.on_wake(wake);
    }
    let _ = (host.app.config.harness.0, host.app.config.theme, host.app.pair, host.app.r#type);
}

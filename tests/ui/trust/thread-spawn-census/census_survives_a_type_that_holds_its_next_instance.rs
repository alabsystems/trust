//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-writer-census=config.harness
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=config.harness
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `Nest<T>` holds a `Nest<Option<T>>` BY VALUE (a `ManuallyDrop<Box<..>>`
//! is what makes rustc accept an owning polymorphic recursion). The writer
//! census asks of every type written whole whether it holds the consumer's
//! type by value, and its walk went one native frame per instantiation: the
//! compiler died of a stack overflow, also on a declared binding with no
//! flag. The walk is a worklist with a bound now.

use std::mem::ManuallyDrop;
use std::sync::mpsc::channel;

#[derive(Default)]
struct Config {
    harness: u8,
    theme: u16,
}

#[derive(Default)]
struct App {
    config: Config,
}

struct Nest<T: 'static> {
    next: Option<ManuallyDrop<Box<Nest<Option<T>>>>>,
    v: Option<T>,
}

enum Wake {
    Harness,
    Theme,
}

impl App {
    fn on_wake(&mut self, wake: Wake) { //~ NOTE writer census: `App.config.harness` may be written at 1 site(s), from the arm for `Wake::Harness` in `App::on_wake`
        match wake {
            Wake::Harness => self.config.harness = 1, //~ NOTE writer census: this writes `App.config.harness`; reached from the arm for `Wake::Harness` in `App::on_wake`
            Wake::Theme => self.config.theme += 1,
        }
    }
}

fn clear(nest: &mut Nest<u8>) {
    *nest = Nest { next: None, v: None };
}

fn main() {
    let (tx, rx) = channel::<Wake>();
    let sender = std::thread::spawn(move || {
        let _ = tx.send(Wake::Harness);
        let _ = tx.send(Wake::Theme);
    });
    let mut nest = Nest::<u8> { next: None, v: None };
    clear(&mut nest);
    let _ = (&nest.next, &nest.v);
    let mut app = App::default();
    while let Ok(wake) = rx.recv() {
        app.on_wake(wake);
    }
    sender.join().unwrap();
}

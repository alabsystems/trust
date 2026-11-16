//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-writer-census=flag
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-writer-census=flag
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The writer census attributes a write to the arm it is in when the consumer
//! is a drain loop with a `self`: the loop's back edge carries every arm back
//! to the switch, so arms are told apart by which variants the message can be
//! at a block, not by which blocks an arm can reach. The consumer here takes
//! `self` by value, so a write into that local is a write of the field. A
//! `&mut` of the field handed to a local generic helper is a site where it is
//! taken. A write before the loop is outside the arms. `main` runs the
//! consumer, and its own write of the field before the call is reached by the
//! consumer's own thread, outside the consumer.

use std::sync::mpsc::{Receiver, channel};

struct App {
    flag: bool,
    n: u32,
}

enum Msg {
    Set,
    Clear,
    Bump,
    Tick,
}

fn set<T>(slot: &mut T, value: T) {
    *slot = value; //~ NOTE writer census: this writes a `bool` through a pointer, which may be `App.flag`; reached from the arm for `Msg::Clear` in `App::pump`
}

fn prepare(app: &mut App) {
    app.flag = true; //~ NOTE writer census: this writes `App.flag`; reached from `main`, the consumer's own thread, outside `App::pump`
}

impl App {
    fn pump(mut self, rx: Receiver<Msg>) -> u32 { //~ NOTE writer census: `App.flag` may be written at 5 site(s), from the 2 arms for `Msg::Set` and `Msg::Clear` in `App::pump`, `App::pump` outside its arms and `main`, the consumer's own thread, outside `App::pump`
        self.flag = false; //~ NOTE writer census: this writes `App.flag`; reached from `App::pump` outside its arms
        while let Ok(msg) = rx.recv() {
            match msg {
                Msg::Set => self.flag = true, //~ NOTE writer census: this writes `App.flag`; reached from the arm for `Msg::Set` in `App::pump`
                Msg::Clear => set(&mut self.flag, false), //~ NOTE writer census: this takes a `&mut` of `App.flag`; reached from the arm for `Msg::Clear` in `App::pump`
                Msg::Bump | Msg::Tick => self.n += 1,
            }
        }
        self.n
    }
}

fn main() {
    let (tx, rx) = channel::<Msg>();
    let _sender = std::thread::spawn(move || {
        let _ = tx.send(Msg::Set);
        let _ = tx.send(Msg::Clear);
        let _ = tx.send(Msg::Bump);
        let _ = tx.send(Msg::Tick);
    });
    let mut app = App { flag: false, n: 0 };
    prepare(&mut app);
    let _ = app.pump(rx);
}

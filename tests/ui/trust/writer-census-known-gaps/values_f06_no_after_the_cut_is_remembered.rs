//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//! KNOWN GAP of the writer census (review 11, 2026-10-05; lens: values).
//! The binding below HOLDS, and the bound field is written outside the
//! declared arm. When a fix makes this file fail, that is the win: move the
//! program to a must-fail fixture and delete this file.
//! Root, as its skeptic put it: writer_origins.rs `Frame::asked`, the cut at
//! 432-436 together with 450-455: the cut returns without lowering
//! `walks.low`, so `if answer || low >= at { walks.known.insert(key, answer);
//! }` keeps every enclosing NO for the whole scan. Wrong sentence (doc of
//! `Walks`, 283-288): "A type met again on its own way round answers no, ..

use std::sync::mpsc::channel;
#[derive(Default, Debug)]
pub struct Policy(pub u8);
#[derive(Default)]
pub struct Config { pub harness: Policy }
#[derive(Default)]
pub struct App { pub config: Config }
pub enum Wake { Observed(u8), Tick }
impl App {
    fn on_wake(&mut self, wake: Wake) {
        match wake {
            Wake::Observed(p) => { self.config.harness = Policy(p); }
            Wake::Tick => {}
        }
    }
}
pub struct List<T> { pub items: Vec<T> }
pub struct Workspace { pub windows: List<Window> }
pub struct Window { pub tabs: List<Tab> }
pub struct Tab { pub splits: List<Split> }
pub struct Split { pub panes: List<Pane> }
pub struct Pane { pub views: List<View> }
pub struct View { pub sheets: List<Sheet> }
pub struct Sheet { pub apps: List<App> }
fn main() {
    let (tx, rx) = channel::<Wake>();
    let _ = tx.send(Wake::Observed(1)); let _ = tx.send(Wake::Tick); drop(tx);
    let ws = Workspace { windows: List { items: Vec::new() } };
    let _windows = ws.windows.items.len();
    let mut sheet = Sheet { apps: List { items: Vec::from([App::default()]) } };
    for wake in rx {
        sheet.apps.items[0].on_wake(wake);
        println!("after the handler: {:?}", sheet.apps.items[0].config.harness);
        sheet.apps.items[0].config.harness = Policy(9);
        println!("after main:        {:?}", sheet.apps.items[0].config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}

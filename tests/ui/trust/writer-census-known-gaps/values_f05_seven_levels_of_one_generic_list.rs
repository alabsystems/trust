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
//! Root, as its skeptic put it: writer_origins.rs `Frame::asked` 425-436:
//! `growing = own.is_some_and(|own| walks.grown.get(&own).is_some_and(|open|
//! *open >= 6))`, then `return !matches!(question, ASK_REACHES | ASK_OWNS)`.
//! Wrong sentence: "A type that GROWS as it is walked (it holds its next
//! instantiation ...) is read six instantiations down, and what is below ..

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
fn one<T>(t: T) -> List<T> { List { items: Vec::from([t]) } }
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
    let mut ws = Workspace { windows: one(Window { tabs: one(Tab { splits: one(Split { panes: one(Pane { views: one(View { sheets: one(Sheet { apps: one(App::default()) }) }) }) }) }) }) };
    for wake in rx {
        ws.windows.items[0].tabs.items[0].splits.items[0].panes.items[0].views.items[0].sheets.items[0].apps.items[0].on_wake(wake);
        println!("after the handler: {:?}", ws.windows.items[0].tabs.items[0].splits.items[0].panes.items[0].views.items[0].sheets.items[0].apps.items[0].config.harness);
        ws.windows.items[0].tabs.items[0].splits.items[0].panes.items[0].views.items[0].sheets.items[0].apps.items[0].config.harness = Policy(9);
        println!("after main:        {:?}", ws.windows.items[0].tabs.items[0].splits.items[0].panes.items[0].views.items[0].sheets.items[0].apps.items[0].config.harness);
    }
}
clean {
    import Trust.Binding
    open Trust.Protocol
    def policy : Trust.Protocol.Binding :=
      binds "config.harness" ["Observed"] []
}

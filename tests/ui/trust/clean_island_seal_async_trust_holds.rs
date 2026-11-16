//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_svc.rs
//@ aux-build: seal_dep_exec.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The body of an `async fn` is the fn's own, and a `trusts` entry that
//! names the fn covers it wherever its future is polled
//! (`Trust.Protocol.Seal`): every seal HOLDS. `seal_dep_svc::relay` keeps
//! what it is handed (`t = step(t)`) as `relay_sync` does; its future is
//! handed to a trusted executor of a third crate, polled by this crate's own
//! (`pin!`, `poll`; with std's `deref_mut`, run at the future's type, named
//! as every fn run at a holder's type is). Review 3 of
//! the review-14 build found the three `async` seals refused, for the
//! store in `relay`'s own body, with no entry offered: the future's body,
//! met among the type arguments of `block_on`, `Pin::new_unchecked` or
//! `into_future`, was read with no trust at all. (`sync`: the plain fns, on
//! the same entries. The same future `.await`ed in this crate's `async fn`
//! is read on the same trust, and refused for the listed cost of a holder
//! kept across an `.await`.) Untrusted, the same bodies are refused:
//! `_async_trust.rs`.

#![allow(unused)]

extern crate seal_dep_exec;
extern crate seal_dep_svc;

mod sync {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut app = App::new();
        app.cell.bump();
        let log = seal_dep_svc::serve_sync(app);
        let app = seal_dep_svc::relay_sync(App::new(), 3);
        log[0].cell.get() + app.cell.get()
    }
}

mod executor {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub fn run() -> u32 {
        let mut app = App::new();
        app.cell.bump();
        let log = seal_dep_exec::block_on(seal_dep_svc::serve(app));
        let app = seal_dep_exec::block_on(seal_dep_svc::relay(App::new(), 3));
        log[0].cell.get() + app.cell.get()
    }
}

mod local_executor {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    fn block_on<F: std::future::Future>(f: F) -> F::Output {
        let mut f = std::pin::pin!(f);
        let mut cx = std::task::Context::from_waker(std::task::Waker::noop());
        loop {
            if let std::task::Poll::Ready(v) = f.as_mut().poll(&mut cx) {
                return v;
            }
        }
    }
    pub fn run() -> u32 {
        let app = block_on(seal_dep_svc::relay(App::new(), 3));
        app.cell.get()
    }
}

fn main() {
    println!("{}", sync::run());
    println!("{}", executor::run());
    println!("{}", local_executor::run());
}

clean {
    import Trust.Binding
    namespace AsyncTrustHolds
    open Trust.Protocol
    def sync : Trust.Protocol.Seal := seals "sync::Cell" ["sync::Cell::bump"] ["sync::Cell::new"] ["sync::App::new"] ["seal_dep_svc::serve_sync", "seal_dep_svc::relay_sync", "vec::Vec::drop", "vec::Vec::index", "RawVec::drop"]
    def executor : Trust.Protocol.Seal := seals "executor::Cell" ["executor::Cell::bump"] ["executor::Cell::new"] ["executor::App::new"] ["seal_dep_svc::serve", "seal_dep_svc::relay", "seal_dep_exec::block_on", "vec::Vec::drop", "vec::Vec::index", "RawVec::drop"]
    def local_executor : Trust.Protocol.Seal := seals "local_executor::Cell" ["local_executor::Cell::bump"] ["local_executor::Cell::new"] ["local_executor::App::new"] ["seal_dep_svc::relay", "DerefMut::deref_mut"]
    end AsyncTrustHolds
}

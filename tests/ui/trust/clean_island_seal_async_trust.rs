//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_svc.rs
//@ aux-build: seal_dep_exec.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_async_trust_holds.rs`
//! (`Trust.Protocol.Seal`): the same `async fn`s of `seal_dep_svc`, with no
//! `trusts` entry that names them. Each seal must FAIL: the future's body
//! keeps the holder it is handed, and puts one value over another
//! (`t = step(t)`), on no one's word.

#![allow(unused)]

extern crate seal_dep_exec;
extern crate seal_dep_svc;

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
        let app = seal_dep_exec::block_on(seal_dep_svc::relay(App::new(), 3)); //~ NOTE `relay`, named here in `executor::run`, runs code of another crate that puts a value of type
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
        let mut f = std::pin::pin!(f); //~ NOTE `relay`, named here in `local_executor::block_on`, runs code of another crate that puts a value of type
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

mod awaited {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    async fn local(app: App) -> App { seal_dep_svc::relay(app, 3).await } //~ NOTE `relay`, named here in `awaited::local`, runs code of another crate that puts a value of type
    pub fn run() -> u32 {
        let app = seal_dep_exec::block_on(local(App::new()));
        app.cell.get()
    }
}

fn main() {
    println!("{}", executor::run());
    println!("{}", local_executor::run());
    println!("{}", awaited::run());
}

clean {
    import Trust.Binding
    namespace AsyncTrust
    open Trust.Protocol
    def executor : Trust.Protocol.Seal := seals "executor::Cell" ["executor::Cell::bump"] ["executor::Cell::new"] ["executor::App::new"] ["seal_dep_exec::block_on", "vec::Vec::drop", "vec::Vec::index", "RawVec::drop"]
    def local_executor : Trust.Protocol.Seal := seals "local_executor::Cell" ["local_executor::Cell::bump"] ["local_executor::Cell::new"] ["local_executor::App::new"] ["DerefMut::deref_mut"]
    def awaited : Trust.Protocol.Seal := seals "awaited::Cell" ["awaited::Cell::bump"] ["awaited::Cell::new"] ["awaited::App::new"] ["seal_dep_exec::block_on"]
    end AsyncTrust
}
//~^^^^^ ERROR seal `AsyncTrust.executor` on `Cell` does not hold
//~^^^^^ ERROR seal `AsyncTrust.local_executor` on `Cell` does not hold
//~^^^^^ ERROR seal `AsyncTrust.awaited` on `Cell` does not hold

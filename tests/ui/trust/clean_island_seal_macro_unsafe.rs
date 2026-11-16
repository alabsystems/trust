//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_macro_unsafe.rs
//@ aux-build: seal_dep_macro_unsafe0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! The twin of `clean_island_seal_macro_unsafe_holds.rs`
//! (`Trust.Protocol.Seal`): a dependency fn whose source holds `pin!` (so
//! its source fact says `unsafe`) is asked about what only `unsafe` code
//! can do. Each seal must FAIL: `pin_raw`'s author reads a holder's bytes
//! through a raw pointer; `pin_unbox` moves out of a `Box` and `pin_async`
//! is an `async fn`, whose lowering (a transmute no call wrote) is read as
//! the fn's own `unsafe` (a listed cost: trust the fn, or move the `pin!`
//! into a fn of its own).

#![allow(unused)]

extern crate seal_dep_macro_unsafe;
extern crate seal_dep_macro_unsafe0;

mod pin_unbox_o {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_macro_unsafe::pin_unbox::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_macro_unsafe::pin_unbox`, a fn of a crate outside the standard library, which gives a
        println!("pin_unbox_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_raw_o {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_macro_unsafe::pin_raw::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_macro_unsafe::pin_raw`, a fn of a crate outside the standard library, which calls an
        println!("pin_raw_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_async_o {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe::Make for Mark { type Out = App; }
    fn block_on<F: ::std::future::Future>(f: F) -> F::Output {
        let mut f = ::std::pin::pin!(f);
        let mut cx = ::std::task::Context::from_waker(::std::task::Waker::noop());
        loop { if let ::std::task::Poll::Ready(v) = f.as_mut().poll(&mut cx) { return v; } } //~ NOTE this runs `seal_dep_macro_unsafe::pin_async`, a fn of a crate outside the standard library, which gives a
    }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = block_on(seal_dep_macro_unsafe::pin_async::<Mark>(&mut x, &mut y));
        println!("pin_async_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_unbox_z {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe0::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_macro_unsafe0::pin_unbox::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_macro_unsafe0::pin_unbox`, a fn of a crate outside the standard library, which gives a
        println!("pin_unbox_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_raw_z {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe0::Make for Mark { type Out = App; }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = seal_dep_macro_unsafe0::pin_raw::<Mark>(&mut x, &mut y); //~ NOTE this runs `seal_dep_macro_unsafe0::pin_raw`, a fn of a crate outside the standard library, which gives a
        println!("pin_raw_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_async_z {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    impl App { pub fn new() -> Self { App { cell: Cell::new() } } }
    pub struct Mark;
    impl seal_dep_macro_unsafe0::Make for Mark { type Out = App; }
    fn block_on<F: ::std::future::Future>(f: F) -> F::Output {
        let mut f = ::std::pin::pin!(f);
        let mut cx = ::std::task::Context::from_waker(::std::task::Waker::noop());
        loop { if let ::std::task::Poll::Ready(v) = f.as_mut().poll(&mut cx) { return v; } } //~ NOTE this runs `seal_dep_macro_unsafe0::pin_async`, a fn of a crate outside the standard library, which gives a
    }
    pub fn run() {
        let mut x = App::new();
        let mut y = App::new();
        x.cell.bump();
        let _ = block_on(seal_dep_macro_unsafe0::pin_async::<Mark>(&mut x, &mut y));
        println!("pin_async_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

fn main() {
    pin_unbox_o::run();
    pin_raw_o::run();
    pin_async_o::run();
    pin_unbox_z::run();
    pin_raw_z::run();
    pin_async_z::run();
}

clean {
    import Trust.Binding
    namespace MacroUnsafe
    open Trust.Protocol
    def pin_unbox_o : Trust.Protocol.Seal := seals "pin_unbox_o::Cell" ["pin_unbox_o::Cell::bump"] ["pin_unbox_o::Cell::new"] ["pin_unbox_o::App::new"] []
    def pin_raw_o : Trust.Protocol.Seal := seals "pin_raw_o::Cell" ["pin_raw_o::Cell::bump"] ["pin_raw_o::Cell::new"] ["pin_raw_o::App::new"] []
    def pin_async_o : Trust.Protocol.Seal := seals "pin_async_o::Cell" ["pin_async_o::Cell::bump"] ["pin_async_o::Cell::new"] ["pin_async_o::App::new"] []
    def pin_unbox_z : Trust.Protocol.Seal := seals "pin_unbox_z::Cell" ["pin_unbox_z::Cell::bump"] ["pin_unbox_z::Cell::new"] ["pin_unbox_z::App::new"] []
    def pin_raw_z : Trust.Protocol.Seal := seals "pin_raw_z::Cell" ["pin_raw_z::Cell::bump"] ["pin_raw_z::Cell::new"] ["pin_raw_z::App::new"] []
    def pin_async_z : Trust.Protocol.Seal := seals "pin_async_z::Cell" ["pin_async_z::Cell::bump"] ["pin_async_z::Cell::new"] ["pin_async_z::App::new"] []
    end MacroUnsafe
}
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_unbox_o` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_raw_o` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_async_o` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_unbox_z` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_raw_z` on `Cell` does not hold
//~^^^^^^^^ ERROR seal `MacroUnsafe.pin_async_z` on `Cell` does not hold

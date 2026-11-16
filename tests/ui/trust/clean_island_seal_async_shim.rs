//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! An `async` closure that is `Fn`, called once in generic code
//! (`Trust.Protocol.Seal`): the call runs the shim the compiler writes for it
//! (`ConstructCoroutineInClosure`, which moves the captures into a new
//! coroutine), read from its own MIR, and the coroutine's body where it is
//! polled and where it stands. The seal must FAIL: the body puts one `(T, App)`
//! over another. (Written for this fixture: review 4 of the review-14 build
//! found every seal of a crate with such a closure refused, the shim unread; the
//! twin, `_async_shim_holds.rs`, has the closures that write nothing.)

#![allow(unused)]

pub mod overwrite {
    pub(crate) struct Cell { n: u32 }
    impl Cell {
        pub(crate) fn new() -> Self { Cell { n: 0 } }
        pub(crate) fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl App {
        pub fn new() -> Self { App { cell: Cell::new() } }
        pub fn tick(&mut self) { self.cell.bump() }
    }
    fn go<F: AsyncFnOnce() -> u8>(f: F) -> u8 { let _ = f(); 0 }
    pub fn churn<T: Clone>(t: T) -> u8 {
        let c = async || { let mut x = (t.clone(), App::new()); x = (t.clone(), App::new()); 1u8 }; //~ NOTE this puts a value of type `(T, App)`, which holds a `Cell`, where one may already be, in
        go(c)
    }
}

clean {
    import Trust.Binding
    namespace AsyncShim
    open Trust.Protocol
    def overwrite : Trust.Protocol.Seal := seals "overwrite::Cell" ["overwrite::Cell::bump"] ["overwrite::Cell::new"] ["overwrite::App::new"] []
    end AsyncShim
}
//~^^^ ERROR seal `AsyncShim.overwrite` on `Cell` does not hold

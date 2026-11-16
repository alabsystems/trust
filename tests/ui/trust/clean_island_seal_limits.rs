//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! What refuses EVERY seal of a crate (`Trust.Protocol.Seal`): where the
//! check gives up it says so, and no seal holds. Review 12 found the first
//! and the last of these: the first build of the check died of a stack
//! overflow on the one and never came back from the other.
//!
//! - `growing`: a field of the sealed type has a type that grows as it is
//!   read (`Grow<T>` points to a `Grow<(T,)>`). The question "is it plain
//!   data" opens a bounded number of types and then answers no.
//! - `unbounded`: an `unsafe impl` for every `Wrap<T>`: `T` may be a type
//!   that holds a sealed value, of any seal, and code of another crate may
//!   build or change one on the strength of the impl.
//! - `assembled`: the crate has a `global_asm!` item. Assembly needs no
//!   `unsafe` there, can name a fn of the crate for the loader to run, and
//!   is no code the check reads.
//! - `recursive`: a fn instantiates itself at an ever larger type. The
//!   compiler stops such a program where it makes the instances, at the
//!   recursion limit; the check, which reads the instances first, stops at
//!   the same limit, and refuses every seal of the crate.
//! - `externfn`: the crate declares a fn in an `extern` block as `safe` to
//!   call, and calls it with a `&mut` of the sealed value: no `unsafe` block
//!   anywhere, no body to read, and what runs is not Rust. What makes the
//!   call safe is the author's word, which the check cannot read: every
//!   seal of the crate is refused until its `trusts` names the fn. (Review
//!   14. So is an `unsafe impl` of another crate's trait, for the same
//!   reason: `clean_island_seal_dependency.rs`.)

#![allow(unused)]

mod growing {
    pub struct Grow<T: 'static> { next: Option<&'static Grow<(T,)>>, here: T }
    pub struct Cell { n: u32, tree: Option<&'static Grow<u8>> }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0, tree: None } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); }
}

mod unbounded {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub unsafe trait Zeroable {}
    pub struct Wrap<T>(T);
    unsafe impl<T> Zeroable for Wrap<T> {}
    pub fn run() { let mut cell = Cell::new(); cell.bump(); }
}

mod assembled {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    std::arch::global_asm!("");
    pub fn run() { let mut cell = Cell::new(); cell.bump(); }
}

mod recursive {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    fn nest<T>(value: T, depth: u32) -> usize {
        if depth == 0 { std::mem::size_of_val(&value) } else { nest((value,), depth - 1) }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); nest(0u8, 3); }
}

mod externfn {
    #[repr(C)]
    pub struct Cell { n: i64 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 1 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    unsafe extern "C" { safe fn time(to: &mut Cell) -> i64; }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); time(&mut cell); }
}

fn main() {
    growing::run();
    unbounded::run();
    assembled::run();
    recursive::run();
    externfn::run();
}

clean {
    import Trust.Binding
    namespace Limits
    open Trust.Protocol
    def growing : Trust.Protocol.Seal := seals "growing::Cell" ["growing::Cell::bump"] ["growing::Cell::new"] ["growing::run"] []
    def unbounded : Trust.Protocol.Seal := seals "unbounded::Cell" ["unbounded::Cell::bump"] ["unbounded::Cell::new"] ["unbounded::run"] []
    def assembled : Trust.Protocol.Seal := seals "assembled::Cell" ["assembled::Cell::bump"] ["assembled::Cell::new"] ["assembled::run"] []
    def recursive : Trust.Protocol.Seal := seals "recursive::Cell" ["recursive::Cell::bump"] ["recursive::Cell::new"] ["recursive::run"] []
    def externfn : Trust.Protocol.Seal := seals "externfn::Cell" ["externfn::Cell::bump"] ["externfn::Cell::new"] ["externfn::run"] []
    end Limits
}
//~^^^^^^^ ERROR seal `Limits.growing` on `Cell` does not hold
//~^^^^^^^ ERROR seal `Limits.unbounded` on `Cell` does not hold
//~^^^^^^^ ERROR seal `Limits.assembled` on `Cell` does not hold
//~^^^^^^^ ERROR seal `Limits.recursive` on `Cell` does not hold
//~^^^^^^^ ERROR seal `Limits.externfn` on `Cell` does not hold

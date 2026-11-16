//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_macro_unsafe.rs
//@ aux-build: seal_dep_macro_unsafe0.rs
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A call the compiler writes is no `unsafe` of the fn's author
//! (`Trust.Protocol.Seal`): in a dependency fn whose source holds a std
//! macro's own `unsafe` block (`pin!`, a `thread_local!` declared in the
//! fn), the `fmt::Arguments::new` that `eprintln!`'s `format_args!` calls,
//! and what `.await` lowers into, are std's, as `pin!`'s `Pin::new_unchecked`
//! is. Every seal HOLDS, with the dependency built with optimization (`_o`)
//! and without (`_z`). Review 3 of the review-14 build found `pin_print`,
//! `pin_closure_print` and `tl_inner` refused: the fn's source fact counts
//! `pin!`'s block, so the call `eprintln!` wrote was read as the author's.
//! (What the compiler lowers into code no call wrote, a move out of a `Box`
//! or an `async` body's resume, is still read as such a fn's `unsafe`, a
//! listed cost; and so is the author's own: `_macro_unsafe.rs`.)

#![allow(unused)]

extern crate seal_dep_macro_unsafe;
extern crate seal_dep_macro_unsafe0;

mod pin_only_o {
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
        let _ = seal_dep_macro_unsafe::pin_only::<Mark>(&mut x, &mut y);
        println!("pin_only_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod print_only_o {
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
        let _ = seal_dep_macro_unsafe::print_only::<Mark>(&mut x, &mut y);
        println!("print_only_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_print_o {
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
        let _ = seal_dep_macro_unsafe::pin_print::<Mark>(&mut x, &mut y);
        println!("pin_print_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_closure_print_o {
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
        let _ = seal_dep_macro_unsafe::pin_closure_print::<Mark>(&mut x, &mut y);
        println!("pin_closure_print_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod tl_inner_o {
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
        let _ = seal_dep_macro_unsafe::tl_inner::<Mark>(&mut x, &mut y);
        println!("tl_inner_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod tl_inner_quiet_o {
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
        let _ = seal_dep_macro_unsafe::tl_inner_quiet::<Mark>(&mut x, &mut y);
        println!("tl_inner_quiet_o: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_only_z {
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
        let _ = seal_dep_macro_unsafe0::pin_only::<Mark>(&mut x, &mut y);
        println!("pin_only_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod print_only_z {
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
        let _ = seal_dep_macro_unsafe0::print_only::<Mark>(&mut x, &mut y);
        println!("print_only_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_print_z {
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
        let _ = seal_dep_macro_unsafe0::pin_print::<Mark>(&mut x, &mut y);
        println!("pin_print_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod pin_closure_print_z {
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
        let _ = seal_dep_macro_unsafe0::pin_closure_print::<Mark>(&mut x, &mut y);
        println!("pin_closure_print_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod tl_inner_z {
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
        let _ = seal_dep_macro_unsafe0::tl_inner::<Mark>(&mut x, &mut y);
        println!("tl_inner_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

mod tl_inner_quiet_z {
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
        let _ = seal_dep_macro_unsafe0::tl_inner_quiet::<Mark>(&mut x, &mut y);
        println!("tl_inner_quiet_z: x={} y={}", x.cell.get(), y.cell.get());
    }
}

fn main() {
    pin_only_o::run();
    print_only_o::run();
    pin_print_o::run();
    pin_closure_print_o::run();
    tl_inner_o::run();
    tl_inner_quiet_o::run();
    pin_only_z::run();
    print_only_z::run();
    pin_print_z::run();
    pin_closure_print_z::run();
    tl_inner_z::run();
    tl_inner_quiet_z::run();
}

clean {
    import Trust.Binding
    namespace MacroUnsafeHolds
    open Trust.Protocol
    def pin_only_o : Trust.Protocol.Seal := seals "pin_only_o::Cell" ["pin_only_o::Cell::bump"] ["pin_only_o::Cell::new"] ["pin_only_o::App::new"] []
    def print_only_o : Trust.Protocol.Seal := seals "print_only_o::Cell" ["print_only_o::Cell::bump"] ["print_only_o::Cell::new"] ["print_only_o::App::new"] []
    def pin_print_o : Trust.Protocol.Seal := seals "pin_print_o::Cell" ["pin_print_o::Cell::bump"] ["pin_print_o::Cell::new"] ["pin_print_o::App::new"] []
    def pin_closure_print_o : Trust.Protocol.Seal := seals "pin_closure_print_o::Cell" ["pin_closure_print_o::Cell::bump"] ["pin_closure_print_o::Cell::new"] ["pin_closure_print_o::App::new"] []
    def tl_inner_o : Trust.Protocol.Seal := seals "tl_inner_o::Cell" ["tl_inner_o::Cell::bump"] ["tl_inner_o::Cell::new"] ["tl_inner_o::App::new"] []
    def tl_inner_quiet_o : Trust.Protocol.Seal := seals "tl_inner_quiet_o::Cell" ["tl_inner_quiet_o::Cell::bump"] ["tl_inner_quiet_o::Cell::new"] ["tl_inner_quiet_o::App::new"] []
    def pin_only_z : Trust.Protocol.Seal := seals "pin_only_z::Cell" ["pin_only_z::Cell::bump"] ["pin_only_z::Cell::new"] ["pin_only_z::App::new"] []
    def print_only_z : Trust.Protocol.Seal := seals "print_only_z::Cell" ["print_only_z::Cell::bump"] ["print_only_z::Cell::new"] ["print_only_z::App::new"] []
    def pin_print_z : Trust.Protocol.Seal := seals "pin_print_z::Cell" ["pin_print_z::Cell::bump"] ["pin_print_z::Cell::new"] ["pin_print_z::App::new"] []
    def pin_closure_print_z : Trust.Protocol.Seal := seals "pin_closure_print_z::Cell" ["pin_closure_print_z::Cell::bump"] ["pin_closure_print_z::Cell::new"] ["pin_closure_print_z::App::new"] []
    def tl_inner_z : Trust.Protocol.Seal := seals "tl_inner_z::Cell" ["tl_inner_z::Cell::bump"] ["tl_inner_z::Cell::new"] ["tl_inner_z::App::new"] []
    def tl_inner_quiet_z : Trust.Protocol.Seal := seals "tl_inner_quiet_z::Cell" ["tl_inner_quiet_z::Cell::bump"] ["tl_inner_quiet_z::Cell::new"] ["tl_inner_quiet_z::App::new"] []
    end MacroUnsafeHolds
}

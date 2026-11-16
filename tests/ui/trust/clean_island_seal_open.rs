//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: seal_dep_open.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A LIBRARY's generic code, read where it stands, is read OPEN
//! (`Trust.Protocol.Seal`): what it names at a type that mentions its own
//! parameters is followed as an instance is (a fn of this crate or of
//! another, a constant, a vtable's method, a drop), and judged whatever the
//! parameters stand for. Each seal must FAIL: whatever `T` is, the code
//! puts one `(T, App)` over another, or hands one to a `dyn` of another
//! crate's trait, or writes another field of a union that holds one. Review
//! 3 of the review-14 build found every one but `vtable` and `dropped`
//! passing (the reading where the body stood judged a store and a call of a
//! fn of another crate, and followed nothing), and a crate that depends on
//! the library swapped or overwrote two holders through it. (`vtable` and
//! `dropped` were written for this fixture: a blanket impl's method put in a
//! vtable at `(T, App)`, and a `Vec<(T, App)>` dropped, which its `Drop`
//! impl does at a type that holds one, as at any instance; so was `picked`,
//! a method of another crate's trait whose impl the parameter picks, at a
//! holder: that crate's blanket impl, chosen whatever `V` is, overwrites it.)
//!
//! With the same shapes at types that hold none, or code that only reads,
//! the seals hold: `_open_holds.rs`.

#![allow(unused)]

extern crate seal_dep_open;

pub mod helper {
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
    fn local_put<T>(slot: &mut T, v: T) { *slot = v; } //~ NOTE this puts a value of type `(T, helper::App)`, which holds a `Cell`, where one may already be, in
    pub fn churn<T>(a: &mut (T, App), b: (T, App)) { local_put(a, b) }
}

pub mod swap_helper {
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
    fn local_swap<T>(a: &mut T, b: &mut T) { core::mem::swap(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, swap_helper::App)`, which holds a
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { local_swap(a, b) }
}

pub mod method {
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
    pub struct Slot<T>(pub T);
    impl<T> Slot<T> { pub fn set(&mut self, v: T) { self.0 = v; } } //~ NOTE this puts a value of type `(T, method::App)`, which holds a `Cell`, where one may already be, in
    pub fn churn<T>(a: &mut Slot<(T, App)>, b: (T, App)) { a.set(b) }
}

pub mod blanket {
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
    pub trait Put: Sized { fn put(&mut self, v: Self) { *self = v; } } //~ NOTE this puts a value of type `(T, blanket::App)`, which holds a `Cell`, where one may already be, in
    impl<T> Put for T {}
    pub fn churn<T>(a: &mut (T, App), b: (T, App)) { a.put(b) }
}

pub mod dep_const {
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
    use seal_dep_open::Tab;
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { (Tab::<(T, App)>::SWAP)(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, dep_const::App)`, which holds a `Cell`,
}

pub mod local_const {
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
    pub struct Local<T>(core::marker::PhantomData<T>);
    impl<T> Local<T> { pub const SW: fn(&mut T, &mut T) = core::mem::swap::<T>; } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, local_const::App)`, which holds a
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { (Local::<(T, App)>::SW)(a, b) }
}

pub mod dyn_const {
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
    use seal_dep_open::Tab;
    pub fn churn<T: 'static>(a: &mut (T, App), b: &mut (T, App)) { (Tab::<(T, App)>::DSWAP)(a, b) } //~ NOTE this runs a closure (or an `async` block) in `seal_dep_open::Tab::DSWAP`, of another crate, at the type `(T,
}

pub mod provided {
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
    use seal_dep_open::Ops;
    pub fn churn<T>(a: &mut (T, App), b: (T, App)) { (<(T, App) as Ops>::PUT)(a, b) } //~ NOTE this runs `seal_dep_open::put`, a fn of another crate, at the type `(T, provided::App)`, which holds a
}

pub mod inline_const {
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
    use seal_dep_open::Tab;
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { (const { Tab::<(T, App)>::SWAP })(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, inline_const::App)`, which holds a
}

pub mod pub_const {
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
    pub struct Tools<T>(core::marker::PhantomData<T>);
    impl<T> Tools<T> { pub const SW: fn(&mut (T, App), &mut (T, App)) = seal_dep_open::Tab::<(T, App)>::SWAP; } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, pub_const::App)`, which holds a `Cell`,
}

pub mod swapper {
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
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { (seal_dep_open::swapper::<(T, App)>())(a, b) } //~ NOTE this runs `core::mem::swap`, a fn of another crate, at the type `(T, swapper::App)`, which holds a `Cell`, in
}

pub mod unsize {
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
    pub fn hide<T: 'static>(x: Box<(T, App)>) -> Box<dyn core::any::Any> { x } //~ NOTE this hands a value of type `(T, unsize::App)`, which holds a `Cell` or points to one, to a `dyn Any`, in
}

pub mod union {
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
    pub union U<T> { pub a: core::mem::ManuallyDrop<(T, App)>, pub b: u64 }
    pub fn clobber<T>(u: &mut U<T>) { u.b = 5; } //~ NOTE this writes a field of the union `U<T>`, another field of which holds a `Cell`, in
}

pub mod dep_trait {
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
    use seal_dep_open::SwapTr;
    pub fn churn<T>(a: &mut (T, App), b: &mut (T, App)) { <(T, App) as SwapTr>::swap_tr(a, b) } //~ NOTE this runs `seal_dep_open::SwapTr::swap_tr`, a fn of another crate, at the type `(T, dep_trait::App)`, which holds a
}

pub mod vtable {
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
    impl Default for App { fn default() -> Self { App::new() } }
    pub trait Reset { fn reset(&mut self); }
    impl<X: Default> Reset for X { fn reset(&mut self) { *self = X::default(); } } //~ NOTE this puts a value of type `(T, vtable::App)`, which holds a `Cell`, where one may already be, in
    pub fn hide<T: Default + 'static>(x: &mut (T, App)) -> &mut dyn Reset { x }
}

pub mod dropped {
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
    pub fn sink<T>(v: Vec<(T, App)>) {} //~ NOTE this runs `alloc::raw_vec::RawVec::drop`, a fn of another crate, at the type `(T, dropped::App)`, which holds
}

pub mod picked {
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
    impl Default for App { fn default() -> Self { App::new() } }
    pub fn go<V: seal_dep_open::Visit<App>>(v: &V, a: &mut App) { v.visit(a) } //~ NOTE this runs `seal_dep_open::Visit::visit`, a fn of another crate, at the type `picked::App`, which holds a
}

clean {
    import Trust.Binding
    namespace Open
    open Trust.Protocol
    def helper : Trust.Protocol.Seal := seals "helper::Cell" ["helper::Cell::bump"] ["helper::Cell::new"] ["helper::App::new"] []
    def swap_helper : Trust.Protocol.Seal := seals "swap_helper::Cell" ["swap_helper::Cell::bump"] ["swap_helper::Cell::new"] ["swap_helper::App::new"] []
    def method : Trust.Protocol.Seal := seals "method::Cell" ["method::Cell::bump"] ["method::Cell::new"] ["method::App::new"] []
    def blanket : Trust.Protocol.Seal := seals "blanket::Cell" ["blanket::Cell::bump"] ["blanket::Cell::new"] ["blanket::App::new"] []
    def dep_const : Trust.Protocol.Seal := seals "dep_const::Cell" ["dep_const::Cell::bump"] ["dep_const::Cell::new"] ["dep_const::App::new"] []
    def local_const : Trust.Protocol.Seal := seals "local_const::Cell" ["local_const::Cell::bump"] ["local_const::Cell::new"] ["local_const::App::new"] []
    def dyn_const : Trust.Protocol.Seal := seals "dyn_const::Cell" ["dyn_const::Cell::bump"] ["dyn_const::Cell::new"] ["dyn_const::App::new"] []
    def provided : Trust.Protocol.Seal := seals "provided::Cell" ["provided::Cell::bump"] ["provided::Cell::new"] ["provided::App::new"] []
    def inline_const : Trust.Protocol.Seal := seals "inline_const::Cell" ["inline_const::Cell::bump"] ["inline_const::Cell::new"] ["inline_const::App::new"] []
    def pub_const : Trust.Protocol.Seal := seals "pub_const::Cell" ["pub_const::Cell::bump"] ["pub_const::Cell::new"] ["pub_const::App::new"] []
    def swapper : Trust.Protocol.Seal := seals "swapper::Cell" ["swapper::Cell::bump"] ["swapper::Cell::new"] ["swapper::App::new"] []
    def unsize : Trust.Protocol.Seal := seals "unsize::Cell" ["unsize::Cell::bump"] ["unsize::Cell::new"] ["unsize::App::new"] []
    def union : Trust.Protocol.Seal := seals "union::Cell" ["union::Cell::bump"] ["union::Cell::new"] ["union::App::new"] []
    def dep_trait : Trust.Protocol.Seal := seals "dep_trait::Cell" ["dep_trait::Cell::bump"] ["dep_trait::Cell::new"] ["dep_trait::App::new"] []
    def vtable : Trust.Protocol.Seal := seals "vtable::Cell" ["vtable::Cell::bump"] ["vtable::Cell::new"] ["vtable::App::new"] []
    def dropped : Trust.Protocol.Seal := seals "dropped::Cell" ["dropped::Cell::bump"] ["dropped::Cell::new"] ["dropped::App::new"] []
    def picked : Trust.Protocol.Seal := seals "picked::Cell" ["picked::Cell::bump"] ["picked::Cell::new"] ["picked::App::new"] []
    end Open
}
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.helper` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.swap_helper` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.method` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.blanket` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.dep_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.local_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.dyn_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.provided` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.inline_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.pub_const` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.swapper` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.unsize` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.union` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.dep_trait` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.vtable` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.dropped` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^ ERROR seal `Open.picked` on `Cell` does not hold

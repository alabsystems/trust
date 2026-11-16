//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! Seals that do NOT hold, one condition a module (`Trust.Protocol.Seal`).
//! Each module's seal must FAIL at the seal. Most are findings of the paper
//! attack on the design, made before the check was written.
//!
//! S2, fields:
//! - `field`: a fn that is not a writer assigns a field.
//! - `borrowed`: a fn that is not a writer hands out a `&mut` of a field.
//! - `inclosure`: a closure written in a writer writes a field; it can be
//!   kept and run when the writer is not.
//! - `lent`: a writer whose `&mut self` shares its lifetime with another
//!   parameter leaves a borrow of a field in it.
//! - `harvested`: a writer handed a struct of two borrows does the same.
//! - `rawptr`: a raw pointer to a field.
//! S3, making:
//! - `built`: a struct expression outside the makers.
//! - `called`: a maker called from a fn the seal does not name.
//! - `valued`: a maker used as a fn value.
//! - `makerclosure`: a maker hands back a closure that builds.
//! - `ctor`: a tuple struct's constructor used as a fn value.
//! - `constant`: a `const` of the sealed type, a new value at each use.
//! S4, no value over another:
//! - `over`: one holder assigned over another.
//! - `refilled`: a variable moved out of and given another value.
//! - `swapped`: `mem::swap` of two holders.
//! - `generic`: a generic fn of the crate that writes its parameter, at the
//!   holder's type.
//! - `assoc`: the same, with the holder hidden behind an associated type.
//! - `pinned`: `Pin::set`, a fn of another crate that writes through a
//!   pointer type.
//! - `dropswap`: a generic `Drop` impl of the crate swaps two holders.
//! - `vtable`: a generic impl of the crate's own trait swaps two holders,
//!   reached only through a `dyn`.
//! - `counted`: `Iterator::count`, a fn of another crate, runs a generic
//!   `next` of this crate that swaps two holders.
//! - `erased`: the holder made a `dyn Any`.
//! - `shell`: a holder behind a `Box<dyn Trait>` replaced.
//! - `unioned`: the other field of a union that holds the cell is written.
//! - `awaited`: a holder kept in an `async` body.
//! S1 and S5, shape:
//! - `nonplain`: a field that is a `Box`.
//! - `unsafeimpl`: an `unsafe impl` for the sealed type.
//!
//! Review 12 measured the first build of the check and found these, which
//! held (one module a root cause; `Make`, with `Mark`, hides the holder's
//! type behind an associated type, so that only reading the INSTANCE the
//! compiler makes can find the second value):
//! - `lifetimed`: one holder over another in a method of `impl<'a>` that no
//!   body calls. A lifetime parameter is no type still to be known.
//! - `standing`: the same in a generic fn the crate never makes concrete (a
//!   crate that depends on this one would). What mentions no parameter is
//!   judged where it stands.
//! - `whatever`: a store to `(T, App)`, which holds one whatever `T` is.
//! - `reported`: `Termination::report` of what `main` hands back, which only
//!   the compiler's start-up code calls.
//! - `asyncdrop`, `asyncclone`: the drop, and the built-in `clone`, of an
//!   `async` closure run those of what it captured.
//! - `fnitem`: `sort_unstable` hands its comparison on as a fn item, which
//!   an optimized body of another crate names only as a TYPE.
//! - `promoted`: `Waker::from` keeps `wake` in a table that is a constant
//!   promoted in another body, inlined.
//! - `dynsend`, `foreigndyn`: a holder boxed as a `dyn Send`, and as a `dyn`
//!   of another crate's trait: code that names no type of this crate can
//!   replace it.
//! - `repeated`: an inline `const { }` of the sealed type in an array
//!   expression, in a fn that may call the maker: one call, three values.
//! - `twice`: a second seal on a type (every site is laid to the first: the
//!   second would be asked nothing).
//! - `celllent`: a writer hands back a `&Cell` made of a `&mut` of a field.
//!
//! Review 13 measured the rebuild, and found these in the rules that had
//! just been made to refuse less:
//! - `projected`: a constant of a generic impl typed `Self::Out`, which the
//!   impl makes the token, filled by a `const fn` that may call the maker.
//!   Its type is read as the constant sees it.
//! - `equated`: a constant typed by a bare parameter that the impl's bounds
//!   make the token itself. No reading of the declared type sees that: the
//!   constant is judged again where it is used at a concrete type.
//! - `related`: a writer whose return type `&'y &'x ()` makes its `&'x mut
//!   self` outlive `'y` (an implied bound), so a borrow of the field fits a
//!   `'y` place the caller keeps.
//! - `projout`, `wrapout`: a writer hands back `<&'x () as Lend>::Out`, and
//!   a `Lent<&'x ()>` whose field is that projection: a `&'x mut u8`.
//! - `assumed`: "is it plain data" answered yes for a type while a type
//!   that holds it was still being asked, and the answer kept.
//! - `whateverfn`: `mem::swap` at `(T, App)` in a generic fn nothing in the
//!   crate makes concrete.
//! - `shimmed`: a `#[track_caller]` method of a blanket impl, reached only
//!   through the vtable of a `dyn` made of a `u8`: the compiler puts a shim
//!   around it there, and the shim's arguments name no type of this crate.
//! - `anymut`: a holder lent as a `&mut dyn Any`. A fn of another crate that
//!   is not generic is never read, and sound code there can copy one such
//!   value's bytes over another's.
//! (`clean_island_seal_dependency.rs` has those that need another crate;
//! `clean_island_seal_limits.rs` has those whose refusal is of every seal
//! of the crate, `clean_island_seal_library.rs` those that need a library.)

#![allow(unused)]

mod field {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn reset(&mut self) { self.n = 0; }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); cell.reset(); }
}

mod borrowed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn n_mut(&mut self) -> &mut u32 { &mut self.n }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); *cell.n_mut() = 9; }
}

mod inclosure {
    use std::sync::Mutex;
    pub struct Cell { n: u32 }
    static BACK_DOOR: Mutex<Option<fn(&mut Cell, u32)>> = Mutex::new(None);
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) {
            *BACK_DOOR.lock().unwrap() = Some(|cell, to| cell.n = to);
            self.n += 1;
        }
    }
    pub fn run() {
        let mut cell = Cell::new();
        cell.bump();
        let set = BACK_DOOR.lock().unwrap().unwrap();
        set(&mut cell, 99);
    }
}

mod lent {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn lend<'a>(&'a mut self, out: &mut Vec<&'a mut u32>) { out.push(&mut self.n); }
    }
    pub fn run() {
        let mut cell = Cell::new();
        let mut out = Vec::new();
        cell.lend(&mut out);
        *out.pop().unwrap() = 99;
    }
}

mod harvested {
    pub struct Cell { n: u32 }
    impl Cell { pub fn new() -> Self { Cell { n: 0 } } }
    pub struct Job<'k, 'a> { cell: &'a mut Cell, out: &'k mut Vec<&'a mut u32> }
    pub fn harvest(job: Job<'_, '_>) { job.out.push(&mut job.cell.n); }
    pub fn run() {
        let mut cell = Cell::new();
        let mut out = Vec::new();
        harvest(Job { cell: &mut cell, out: &mut out });
        *out.pop().unwrap() = 99;
    }
}

mod rawptr {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn addr(&self) -> *const u32 { &raw const self.n }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); let p = cell.addr(); }
}

mod built {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn forged(n: u32) -> Self { Cell { n } }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); let other = Cell::forged(9); }
}

mod called {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    fn elsewhere() -> Cell { Cell::new() }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); let other = elsewhere(); }
}

mod valued {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new(n: u32) -> Self { Cell { n } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() { let cells: Vec<Cell> = [1u32, 2].into_iter().map(Cell::new).collect(); }
}

mod makerclosure {
    pub struct Stamped { generation: u64 }
    pub fn stamper() -> fn(u64) -> Stamped { |generation| Stamped { generation } }
    pub fn run() { let forge = stamper(); let one = forge(1); let two = forge(2); }
}

mod ctor {
    pub struct Token(u32);
    fn mint(n: u32) -> Token { Token(n) }
    pub fn run() { let one = mint(1); let more: Vec<Token> = [1u32, 2].into_iter().map(Token).collect(); }
}

mod constant {
    pub struct Cell { n: u32 }
    impl Cell {
        pub const fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    const FRESH: Cell = Cell::new();
    pub fn run() { let mut cell = FRESH; cell.bump(); let other = FRESH; }
}

mod over {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell, name: u8 }
    pub fn run() {
        let mut app = App { cell: Cell::new(), name: 1 };
        let other = App { cell: Cell::new(), name: 2 };
        app.cell.bump();
        app = other;
    }
}

mod refilled {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    fn rebuild(old: Cell, spare: Cell) -> Cell { spare }
    pub fn run() {
        let mut cell = Cell::new();
        let spare = Cell::new();
        cell.bump();
        cell = rebuild(cell, spare);
    }
}

mod swapped {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let mut b = App { cell: Cell::new() };
        a.cell.bump();
        std::mem::swap(&mut a, &mut b);
    }
}

mod generic {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    fn put<T>(slot: &mut T, value: T) { *slot = value; }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let b = App { cell: Cell::new() };
        a.cell.bump();
        put(&mut a, b);
    }
}

mod assoc {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    trait Has { type Slot; }
    impl Has for () { type Slot = App; }
    fn put<M: Has>(slot: &mut M::Slot, value: M::Slot) { *slot = value; }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let b = App { cell: Cell::new() };
        a.cell.bump();
        put::<()>(&mut a, b);
    }
}

mod pinned {
    use std::pin::Pin;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let b = App { cell: Cell::new() };
        a.cell.bump();
        Pin::new(&mut a).set(b);
    }
}

mod dropswap {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    struct SwapOnDrop<'a, T> { x: &'a mut T, y: &'a mut T }
    impl<'a, T> Drop for SwapOnDrop<'a, T> {
        fn drop(&mut self) { std::mem::swap(&mut *self.x, &mut *self.y); }
    }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let mut b = App { cell: Cell::new() };
        a.cell.bump();
        let _swap = SwapOnDrop { x: &mut a, y: &mut b };
    }
}

mod vtable {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    trait Flip { fn flip(&mut self); }
    struct Pair<'a, T> { x: &'a mut T, y: &'a mut T }
    impl<'a, T> Flip for Pair<'a, T> {
        fn flip(&mut self) { std::mem::swap(&mut *self.x, &mut *self.y); }
    }
    fn through(flip: &mut dyn Flip) { flip.flip(); }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let mut b = App { cell: Cell::new() };
        a.cell.bump();
        through(&mut Pair { x: &mut a, y: &mut b });
    }
}

mod counted {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    struct Swapper<'a, T> { x: &'a mut T, y: &'a mut T, done: bool }
    impl<'a, T> Iterator for Swapper<'a, T> {
        type Item = ();
        fn next(&mut self) -> Option<()> {
            if self.done { return None; }
            self.done = true;
            std::mem::swap(&mut *self.x, &mut *self.y);
            Some(())
        }
    }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let mut b = App { cell: Cell::new() };
        a.cell.bump();
        let steps = Swapper { x: &mut a, y: &mut b, done: false }.count();
    }
}

mod erased {
    use std::any::Any;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn run() {
        let mut app = App { cell: Cell::new() };
        app.cell.bump();
        let any: &mut dyn Any = &mut app;
    }
}

mod shell {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { cell: Cell }
    trait Holder { fn level(&self) -> u32; }
    impl Holder for App { fn level(&self) -> u32 { self.cell.get() } }
    struct Shell { app: Box<dyn Holder> }
    fn handle(shell: &mut Shell, other: Box<dyn Holder>) { shell.app = other; }
    pub fn run() {
        let mut shell = Shell { app: Box::new(App { cell: Cell::new() }) };
        let other: Box<dyn Holder> = Box::new(App { cell: Cell::new() });
        handle(&mut shell, other);
    }
}

mod unioned {
    use std::mem::ManuallyDrop;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    union Overlay { cell: ManuallyDrop<Cell>, raw: [u8; 4] }
    pub fn run() {
        let mut overlay = Overlay { cell: ManuallyDrop::new(Cell::new()) };
        overlay.raw = [9; 4];
    }
}

mod awaited {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    async fn tick() {}
    pub async fn work() {
        let mut cell = Cell::new();
        tick().await;
        cell.bump();
    }
    pub fn run() { let future = work(); }
}

mod nonplain {
    pub struct Cell { n: Box<u32> }
    impl Cell {
        pub fn new() -> Self { Cell { n: Box::new(0) } }
        pub fn get(&self) -> u32 { *self.n }
        pub fn poke(&mut self) { *self.n = 9; }
    }
    pub fn run() { let mut cell = Cell::new(); cell.poke(); }
}

mod unsafeimpl {
    pub unsafe trait Zeroable {}
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    unsafe impl Zeroable for Cell {}
    pub fn run() { let mut cell = Cell::new(); cell.bump(); }
}

mod lifetimed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct View<'a> { app: &'a mut App }
    impl<'a> View<'a> {
        pub fn reset(&mut self) { *self.app = App { cell: Cell::new() }; }
    }
    pub fn run() { let mut a = App { cell: Cell::new() }; a.cell.bump(); }
}

mod standing {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn each(mut with: impl FnMut(&App)) {
        let mut app = App { cell: Cell::new() };
        app.cell.bump();
        with(&app);
        app = App { cell: Cell::new() };
        with(&app);
    }
    pub fn run() {}
}

mod whatever {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn pair<T: Default>() -> u32 {
        let mut both = (T::default(), App { cell: Cell::new() });
        both.1.cell.bump();
        both = (T::default(), App { cell: Cell::new() });
        both.1.cell.n
    }
    pub fn run() {}
}

mod reported {
    use std::marker::PhantomData;
    use std::process::{ExitCode, Termination};
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Make { type Out; fn make() -> Self::Out; }
    pub struct Mark;
    impl Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    pub struct Finish<M>(pub PhantomData<M>);
    impl<M: Make> Termination for Finish<M> {
        fn report(self) -> ExitCode {
            let mut a = M::make();
            a = M::make();
            ExitCode::SUCCESS
        }
    }
    pub fn run() { let mut a = Mark::make(); a.cell.bump(); }
}

mod asyncdrop {
    use std::marker::PhantomData;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Make { type Out; fn make() -> Self::Out; }
    pub struct Mark;
    impl Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    struct Guard<M: Make>(PhantomData<M>);
    impl<M: Make> Drop for Guard<M> {
        fn drop(&mut self) { let mut a = M::make(); a = M::make(); }
    }
    fn hold<M: Make>() {
        let guard = Guard::<M>(PhantomData);
        let later = async move || { let _kept = &guard; };
        drop(later);
    }
    pub fn run() { let mut a = Mark::make(); a.cell.bump(); hold::<Mark>(); }
}

mod asyncclone {
    use std::marker::PhantomData;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Make { type Out; fn make() -> Self::Out; }
    pub struct Mark;
    impl Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    struct Token<M: Make>(PhantomData<M>);
    impl<M: Make> Clone for Token<M> {
        fn clone(&self) -> Self { let mut a = M::make(); a = M::make(); Token(PhantomData) }
    }
    fn hold<M: Make>() {
        let token = Token::<M>(PhantomData);
        let later = async move || { let _kept = &token; };
        let again = later.clone();
        std::mem::forget((later, again));
    }
    pub fn run() { let mut a = Mark::make(); a.cell.bump(); hold::<Mark>(); }
}

mod fnitem {
    use std::cmp::Ordering;
    use std::marker::PhantomData;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Make { type Out; fn make() -> Self::Out; }
    pub struct Mark;
    impl Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    struct Key<M: Make>(u8, PhantomData<M>);
    impl<M: Make> PartialEq for Key<M> { fn eq(&self, other: &Self) -> bool { self.0 == other.0 } }
    impl<M: Make> Eq for Key<M> {}
    impl<M: Make> PartialOrd for Key<M> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            let mut a = M::make();
            a = M::make();
            self.0.partial_cmp(&other.0)
        }
    }
    impl<M: Make> Ord for Key<M> {
        fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
    }
    pub fn run() {
        let mut a = Mark::make();
        a.cell.bump();
        let mut keys = [Key::<Mark>(2, PhantomData), Key::<Mark>(1, PhantomData)];
        keys.sort_unstable();
    }
}

mod promoted {
    use std::marker::PhantomData;
    use std::sync::Arc;
    use std::task::{Wake, Waker};
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Make { type Out; fn make() -> Self::Out; }
    pub struct Mark;
    impl Make for Mark { type Out = App; fn make() -> App { App { cell: Cell::new() } } }
    struct Flip<M>(PhantomData<M>);
    impl<M: Make + Send + Sync + 'static> Wake for Flip<M> {
        fn wake(self: Arc<Self>) { let mut a = M::make(); a = M::make(); }
    }
    pub fn run() {
        let mut a = Mark::make();
        a.cell.bump();
        Waker::from(Arc::new(Flip::<Mark>(PhantomData))).wake();
    }
}

mod dynsend {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        a.cell.bump();
        let mut slot: Box<dyn Send> = Box::new(a);
        slot = Box::new(App { cell: Cell::new() });
    }
}

mod foreigndyn {
    use std::fmt;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    impl fmt::Debug for App {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.cell.n) }
    }
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        a.cell.bump();
        let mut shown: Box<dyn fmt::Debug> = Box::new(a);
        std::pin::Pin::new(&mut shown).set(Box::new(App { cell: Cell::new() }));
    }
}

mod repeated {
    pub struct Cell { n: u32 }
    impl Cell {
        pub const fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub fn run() {
        let mut cells = [const { Cell::new() }; 3];
        cells[1].bump();
    }
}

mod twice {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn reset(&mut self) { self.n = 0; }
    }
    pub fn run() { let mut cell = Cell::new(); cell.bump(); cell.reset(); }
}

mod celllent {
    use std::cell::Cell;
    pub struct Level { level: u8 }
    impl Level {
        pub fn new() -> Self { Level { level: 0 } }
        pub fn raise(&mut self) -> &Cell<u8> {
            self.level += 1;
            Cell::from_mut(&mut self.level)
        }
    }
    pub fn run() { let mut level = Level::new(); let later = level.raise(); later.set(9); }
}

mod projected {
    pub struct Tok { serial: u32 }
    const fn new() -> Tok { Tok { serial: 7 } }
    pub const fn mint() -> Tok { new() }
    pub trait Mk { type Out; const K: Self::Out; }
    impl<T> Mk for Vec<T> { type Out = Tok; const K: Self::Out = mint(); }
    pub fn run() { let (a, b) = (<Vec<u8> as Mk>::K, <Vec<u8> as Mk>::K); }
}

mod equated {
    pub struct Tok { serial: u32 }
    const fn new() -> Tok { Tok { serial: 7 } }
    pub const fn mint() -> Tok { new() }
    pub trait Is { type Ty; }
    impl<X> Is for X { type Ty = X; }
    const fn same<X>(x: <X as Is>::Ty) -> X { x }
    pub struct H<T>(std::marker::PhantomData<T>);
    impl<T: Is<Ty = Tok>> H<T> { pub const K: T = same::<T>(mint()); }
    pub fn run() { let (a, b) = (H::<Tok>::K, H::<Tok>::K); }
}

mod related {
    pub struct Cell { n: u8 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump<'x, 'y>(&'x mut self, sink: &mut Vec<&'y mut u8>) -> &'y &'x () {
            self.n += 1;
            sink.push(&mut self.n);
            &&()
        }
    }
    pub fn run() {
        let mut cell = Cell::new();
        let mut sink = Vec::new();
        cell.bump(&mut sink);
        *sink.pop().unwrap() = 99;
    }
}

mod projout {
    pub trait Lend { type Out; }
    impl<'a> Lend for &'a () { type Out = &'a mut u8; }
    pub struct Cell { n: u8 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump<'x>(&'x mut self) -> <&'x () as Lend>::Out { self.n += 1; &mut self.n }
    }
    pub fn run() { let mut cell = Cell::new(); *cell.bump() = 99; }
}

mod wrapout {
    pub trait Lend { type Out; }
    impl<'a> Lend for &'a () { type Out = &'a mut u8; }
    pub struct Lent<T: Lend>(pub T::Out);
    pub struct Cell { n: u8 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump<'x>(&'x mut self) -> Lent<&'x ()> { self.n += 1; Lent(&mut self.n) }
    }
    pub fn run() { let mut cell = Cell::new(); *cell.bump().0 = 99; }
}

mod assumed {
    use std::cell::Cell;
    pub struct Node { up: Option<&'static Tree>, hits: Cell<u8> }
    pub struct Tree { root: Node }
    pub fn touch(node: &mut Node) -> &Node { node }
    pub struct Seen { tree: Tree }
    impl Seen {
        pub fn new() -> Self { Seen { tree: Tree { root: Node { up: None, hits: Cell::new(0) } } } }
    }
    pub fn run() { let seen = Seen::new(); seen.tree.root.hits.set(99); }
}

mod whateverfn {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub fn pair<T: Default>() -> u32 {
        let mut one = (T::default(), App { cell: Cell::new() });
        let mut two = (T::default(), App { cell: Cell::new() });
        one.1.cell.bump();
        std::mem::swap(&mut one, &mut two);
        one.1.cell.n
    }
    pub fn run() {}
}

mod shimmed {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub trait Has { type Slot; fn pair() -> (Self::Slot, Self::Slot); }
    impl Has for u8 {
        type Slot = App;
        fn pair() -> (App, App) { (App { cell: Cell::new() }, App { cell: Cell::new() }) }
    }
    pub trait Flip { fn flip(&mut self); }
    impl<T: Has> Flip for T {
        #[track_caller]
        fn flip(&mut self) { let (mut a, b) = T::pair(); a = b; }
    }
    pub fn run() {
        let (mut a, _b) = <u8 as Has>::pair();
        a.cell.bump();
        let flip: &mut dyn Flip = &mut 0u8;
        flip.flip();
    }
}

// Review 14: a constant is judged by what its initializer RUNS. Read by its
// type, this one held nothing: the where-clause only repeats the impl, but
// trait selection prefers it, and it says nothing of `Out`, so the field's
// type stayed a projection.
mod shadowed {
    pub struct Tok { serial: u32 }
    const fn new() -> Tok { Tok { serial: 7 } }
    pub trait Fam { type Out; }
    impl<'a> Fam for &'a () { type Out = Tok; }
    pub struct Wrap<'a>(<&'a () as Fam>::Out);
    pub const fn wrap<'a>() -> Wrap<'a> { Wrap(new()) }
    impl<'a> Wrap<'a> where &'a (): Fam { pub const K: Wrap<'a> = wrap(); }
    pub fn run() { let (a, b) = (Wrap::K.0, Wrap::K.0); }
}

mod anymut {
    use std::any::Any;
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    fn handed(_one: &mut dyn Any, _other: &mut dyn Any) {}
    pub fn run() {
        let mut a = App { cell: Cell::new() };
        let mut b = App { cell: Cell::new() };
        a.cell.bump();
        handed(&mut a, &mut b);
    }
}

fn main() -> reported::Finish<reported::Mark> {
    field::run();
    borrowed::run();
    inclosure::run();
    lent::run();
    harvested::run();
    rawptr::run();
    built::run();
    called::run();
    valued::run();
    makerclosure::run();
    ctor::run();
    constant::run();
    over::run();
    refilled::run();
    swapped::run();
    generic::run();
    assoc::run();
    pinned::run();
    dropswap::run();
    vtable::run();
    counted::run();
    erased::run();
    shell::run();
    unioned::run();
    awaited::run();
    nonplain::run();
    unsafeimpl::run();
    lifetimed::run();
    standing::run();
    whatever::run();
    reported::run();
    asyncdrop::run();
    asyncclone::run();
    fnitem::run();
    promoted::run();
    dynsend::run();
    foreigndyn::run();
    repeated::run();
    twice::run();
    celllent::run();
    projected::run();
    equated::run();
    related::run();
    projout::run();
    wrapout::run();
    assumed::run();
    whateverfn::run();
    shimmed::run();
    anymut::run();
    shadowed::run();
    reported::Finish(std::marker::PhantomData)
}

clean {
    import Trust.Binding
    namespace Broken
    open Trust.Protocol
    def field : Trust.Protocol.Seal := seals "field::Cell" ["field::Cell::bump"] ["field::Cell::new"] ["field::run"] []
    def borrowed : Trust.Protocol.Seal := seals "borrowed::Cell" ["borrowed::Cell::bump"] ["borrowed::Cell::new"] ["borrowed::run"] []
    def inclosure : Trust.Protocol.Seal := seals "inclosure::Cell" ["inclosure::Cell::bump"] ["inclosure::Cell::new"] ["inclosure::run"] []
    def lent : Trust.Protocol.Seal := seals "lent::Cell" ["lent::Cell::lend"] ["lent::Cell::new"] ["lent::run"] []
    def harvested : Trust.Protocol.Seal := seals "harvested::Cell" ["harvest"] ["harvested::Cell::new"] ["harvested::run"] []
    def rawptr : Trust.Protocol.Seal := seals "rawptr::Cell" ["rawptr::Cell::bump"] ["rawptr::Cell::new"] ["rawptr::run"] []
    def built : Trust.Protocol.Seal := seals "built::Cell" ["built::Cell::bump"] ["built::Cell::new"] ["built::run"] []
    def called : Trust.Protocol.Seal := seals "called::Cell" ["called::Cell::bump"] ["called::Cell::new"] ["called::run"] []
    def valued : Trust.Protocol.Seal := seals "valued::Cell" ["valued::Cell::bump"] ["valued::Cell::new"] ["valued::run"] []
    def makerclosure : Trust.Protocol.Seal := seals "makerclosure::Stamped" [] ["stamper"] ["makerclosure::run"] []
    def ctor : Trust.Protocol.Seal := seals "ctor::Token" [] ["ctor::mint"] ["ctor::run"] []
    def constant : Trust.Protocol.Seal := seals "constant::Cell" ["constant::Cell::bump"] ["constant::Cell::new"] ["constant::run"] []
    def over : Trust.Protocol.Seal := seals "over::Cell" ["over::Cell::bump"] ["over::Cell::new"] ["over::run"] []
    def refilled : Trust.Protocol.Seal := seals "refilled::Cell" ["refilled::Cell::bump"] ["refilled::Cell::new"] ["refilled::run"] []
    def swapped : Trust.Protocol.Seal := seals "swapped::Cell" ["swapped::Cell::bump"] ["swapped::Cell::new"] ["swapped::run"] []
    def generic : Trust.Protocol.Seal := seals "generic::Cell" ["generic::Cell::bump"] ["generic::Cell::new"] ["generic::run"] []
    def assoc : Trust.Protocol.Seal := seals "assoc::Cell" ["assoc::Cell::bump"] ["assoc::Cell::new"] ["assoc::run"] []
    def pinned : Trust.Protocol.Seal := seals "pinned::Cell" ["pinned::Cell::bump"] ["pinned::Cell::new"] ["pinned::run"] []
    def dropswap : Trust.Protocol.Seal := seals "dropswap::Cell" ["dropswap::Cell::bump"] ["dropswap::Cell::new"] ["dropswap::run"] []
    def vtable : Trust.Protocol.Seal := seals "vtable::Cell" ["vtable::Cell::bump"] ["vtable::Cell::new"] ["vtable::run"] []
    def counted : Trust.Protocol.Seal := seals "counted::Cell" ["counted::Cell::bump"] ["counted::Cell::new"] ["counted::run"] []
    def erased : Trust.Protocol.Seal := seals "erased::Cell" ["erased::Cell::bump"] ["erased::Cell::new"] ["erased::run"] []
    def shell : Trust.Protocol.Seal := seals "shell::Cell" ["shell::Cell::bump"] ["shell::Cell::new"] ["shell::run"] ["Box::new", "Box::drop"]
    def unioned : Trust.Protocol.Seal := seals "unioned::Cell" ["unioned::Cell::bump"] ["unioned::Cell::new"] ["unioned::run"] ["ManuallyDrop::new"]
    def awaited : Trust.Protocol.Seal := seals "awaited::Cell" ["awaited::Cell::bump"] ["awaited::Cell::new"] ["work"] []
    def nonplain : Trust.Protocol.Seal := seals "nonplain::Cell" ["poke"] ["nonplain::Cell::new"] ["nonplain::run"] []
    def unsafeimpl : Trust.Protocol.Seal := seals "unsafeimpl::Cell" ["unsafeimpl::Cell::bump"] ["unsafeimpl::Cell::new"] ["unsafeimpl::run"] []
    def lifetimed : Trust.Protocol.Seal := seals "lifetimed::Cell" ["lifetimed::Cell::bump"] ["lifetimed::Cell::new"] ["lifetimed::run", "lifetimed::View::reset"] []
    def standing : Trust.Protocol.Seal := seals "standing::Cell" ["standing::Cell::bump"] ["standing::Cell::new"] ["standing::each"] []
    def whatever : Trust.Protocol.Seal := seals "whatever::Cell" ["whatever::Cell::bump"] ["whatever::Cell::new"] ["whatever::pair"] []
    def reported : Trust.Protocol.Seal := seals "reported::Cell" ["reported::Cell::bump"] ["reported::Cell::new"] ["reported::Mark::make"] []
    def asyncdrop : Trust.Protocol.Seal := seals "asyncdrop::Cell" ["asyncdrop::Cell::bump"] ["asyncdrop::Cell::new"] ["asyncdrop::Mark::make"] []
    def asyncclone : Trust.Protocol.Seal := seals "asyncclone::Cell" ["asyncclone::Cell::bump"] ["asyncclone::Cell::new"] ["asyncclone::Mark::make"] []
    def fnitem : Trust.Protocol.Seal := seals "fnitem::Cell" ["fnitem::Cell::bump"] ["fnitem::Cell::new"] ["fnitem::Mark::make"] []
    def promoted : Trust.Protocol.Seal := seals "promoted::Cell" ["promoted::Cell::bump"] ["promoted::Cell::new"] ["promoted::Mark::make"] []
    def dynsend : Trust.Protocol.Seal := seals "dynsend::Cell" ["dynsend::Cell::bump"] ["dynsend::Cell::new"] ["dynsend::run"] ["Box::new", "Box::drop"]
    def foreigndyn : Trust.Protocol.Seal := seals "foreigndyn::Cell" ["foreigndyn::Cell::bump"] ["foreigndyn::Cell::new"] ["foreigndyn::run"] ["Box::new", "Box::drop"]
    def repeated : Trust.Protocol.Seal := seals "repeated::Cell" ["repeated::Cell::bump"] ["repeated::Cell::new"] ["repeated::run"] []
    def twice : Trust.Protocol.Seal := seals "twice::Cell" ["twice::Cell::bump", "twice::Cell::reset"] ["twice::Cell::new"] ["twice::run"] []
    def twiceagain : Trust.Protocol.Seal := seals "twice::Cell" ["twice::Cell::bump"] ["twice::Cell::new"] ["twice::run"] []
    def celllent : Trust.Protocol.Seal := seals "celllent::Level" ["celllent::Level::raise"] ["celllent::Level::new"] ["celllent::run"] []
    def projected : Trust.Protocol.Seal := seals "projected::Tok" [] ["projected::new"] ["projected::mint"] []
    def equated : Trust.Protocol.Seal := seals "equated::Tok" [] ["equated::new"] ["equated::mint"] []
    def related : Trust.Protocol.Seal := seals "related::Cell" ["related::Cell::bump"] ["related::Cell::new"] ["related::run"] []
    def projout : Trust.Protocol.Seal := seals "projout::Cell" ["projout::Cell::bump"] ["projout::Cell::new"] ["projout::run"] []
    def wrapout : Trust.Protocol.Seal := seals "wrapout::Cell" ["wrapout::Cell::bump"] ["wrapout::Cell::new"] ["wrapout::run"] []
    def assumed : Trust.Protocol.Seal := seals "assumed::Seen" [] ["assumed::Seen::new"] ["assumed::run"] []
    def whateverfn : Trust.Protocol.Seal := seals "whateverfn::Cell" ["whateverfn::Cell::bump"] ["whateverfn::Cell::new"] ["whateverfn::pair"] []
    def shimmed : Trust.Protocol.Seal := seals "shimmed::Cell" ["shimmed::Cell::bump"] ["shimmed::Cell::new"] ["shimmed::pair"] []
    def anymut : Trust.Protocol.Seal := seals "anymut::Cell" ["anymut::Cell::bump"] ["anymut::Cell::new"] ["anymut::run"] ["Any::type_id"]
    def shadowed : Trust.Protocol.Seal := seals "shadowed::Tok" [] ["shadowed::new"] ["shadowed::wrap"] []
    end Broken
}
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.field` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.borrowed` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.inclosure` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.lent` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.harvested` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.rawptr` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.built` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.called` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.valued` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.makerclosure` on `Stamped` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.ctor` on `Token` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.constant` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.over` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.refilled` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.swapped` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.generic` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.assoc` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.pinned` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.dropswap` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.vtable` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.counted` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.erased` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.shell` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.unioned` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.awaited` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.nonplain` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.unsafeimpl` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.lifetimed` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.standing` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.whatever` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.reported` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.asyncdrop` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.asyncclone` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.fnitem` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.promoted` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.dynsend` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.foreigndyn` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.repeated` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.twiceagain` is on `Cell`, which seal `Broken.twice` already seals: 
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.celllent` on `Level` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.projected` on `Tok` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.equated` on `Tok` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.related` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.projout` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.wrapout` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.assumed` on `Seen` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.whateverfn` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.shimmed` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.anymut` on `Cell` does not hold
//~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ERROR seal `Broken.shadowed` on `Tok` does not hold

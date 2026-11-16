//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Seals that HOLD (`Trust.Protocol.Seal`): the state a model speaks of, kept
//! in a struct of its own, so that Rust's own rules carry the claim and the
//! compiler follows no pointer to check it.
//!
//! - `policy`: the design's shape. A cell whose only write is `offer`, which
//!   takes a stamp; a stamp only `stamp` makes; a stamp source only the
//!   watcher makes. The stamps cross a channel, a `Vec` and a thread: a
//!   sealed type with no writer is a token, and where a token sits is no
//!   one's concern.
//! - `boxed`: the holder is kept in a `Box` and behind a `Mutex`. Each fn of
//!   another crate that runs at a type holding the cell is one the seal
//!   names in its `trusts`.
//! - `generic`: generic fns of the crate that read their parameter, hand it
//!   back, or call a closure on it, at the holder's type: judged at that
//!   instance, where they put nothing over anything.
//! - `consumed`: a value the body owns is taken apart (`into_parts`).
//! - `matched`: a writer changes a field that is an enum, and a field
//!   through a pattern.
//! - `derived`: beside the sealed type, a `derive(Clone, Copy)` view with a
//!   lifetime. The derive writes an `unsafe impl` of a marker of the
//!   compiler's own, for a type that is `Copy`: it holds no sealed value.
//!
//! True programs the first build of the check refused (review 12):
//! - `waited`: a maker that is an `async fn`, and a holder that an `async`
//!   body builds and ends between two `.await`s: it keeps none across one.
//! - `lent`: a writer that hands back a `&` of plain data, alone, in an
//!   `Option`, and as a trait method's `&Self::View`.
//! - `tokens`: tokens in an array built by `map` and in a thread-local.
//!   Neither std's `const { MaybeUninit::uninit() }` at the token's type nor
//!   a `LocalKey` of it holds a token in its value.
//! - `shapes`: field types of std that are plain data with no pointer in
//!   them; an `unsafe impl` whose parameter is bounded by `Copy`; a `&dyn
//!   Debug` of the cell beside boxes of `dyn Debug` that hold none.
//! - `Dial`, at the crate's root and `pub`: no crate can depend on a
//!   program, so nothing outside can name it.
//!
//! And what the rebuild refused (review 13):
//! - `uncalled`: a closure that is made and never called names a deeper
//!   instance of its own fn. The compiler never makes that instance, and
//!   neither does the check: a closure's body is read where it is called.

#![allow(unused)]

mod policy {
    use std::sync::mpsc::{channel, Sender};

    #[derive(Default, Debug, Clone, Copy, PartialEq)]
    pub struct Policy(u8);

    pub mod order {
        use super::Policy;
        pub struct StampSource { last: u64 }
        pub struct Stamped { generation: u64, value: Policy }
        pub struct PolicyCell { in_force: u64, value: Policy }
        impl StampSource {
            pub fn new() -> Self { StampSource { last: 0 } }
            pub fn stamp(&mut self, value: Policy) -> Stamped {
                self.last += 1;
                Stamped { generation: self.last, value }
            }
        }
        impl PolicyCell {
            pub fn new(initial: Policy) -> Self { PolicyCell { in_force: 0, value: initial } }
            /// The join: the only write.
            pub fn offer(&mut self, stamped: Stamped) -> bool {
                if self.in_force < stamped.generation {
                    self.in_force = stamped.generation;
                    self.value = stamped.value;
                    true
                } else {
                    false
                }
            }
            pub fn get(&self) -> &Policy { &self.value }
            pub fn in_force(&self) -> u64 { self.in_force }
        }
    }
    use order::{PolicyCell, StampSource, Stamped};

    pub enum Wake { Observed(Stamped), Tick, Quit }
    pub struct App { policy: PolicyCell, n: u32 }
    impl App {
        fn new() -> Self { App { policy: PolicyCell::new(Policy(0)), n: 0 } }
        fn on_wake(&mut self, wake: Wake) {
            match wake {
                Wake::Observed(stamped) => { self.policy.offer(stamped); }
                Wake::Tick => { self.n += 1; }
                Wake::Quit => {}
            }
        }
    }
    fn watcher(tx: Sender<Wake>) {
        let mut source = StampSource::new();
        let mut kept: Vec<Stamped> = Vec::new();
        for level in [1u8, 2, 3] {
            kept.push(source.stamp(Policy(level)));
        }
        // Delivered out of order: the join does not care.
        kept.reverse();
        for stamped in kept {
            let _ = tx.send(Wake::Observed(stamped));
            let _ = tx.send(Wake::Tick);
        }
        let _ = tx.send(Wake::Quit);
    }
    pub fn run() {
        let (tx, rx) = channel::<Wake>();
        let sender = std::thread::spawn(move || watcher(tx));
        let mut app = App::new();
        for wake in rx {
            app.on_wake(wake);
            println!("policy: {:?} at {}", app.policy.get(), app.policy.in_force());
        }
        sender.join().unwrap();
    }
}

mod boxed {
    use std::sync::Mutex;

    pub struct Counter { n: u32 }
    impl Counter {
        pub fn new() -> Self { Counter { n: 0 } }
        pub fn bump(&mut self) { self.n += 1; }
        pub fn get(&self) -> u32 { self.n }
    }
    pub struct App { counter: Counter, name: String }
    fn make() -> Box<App> { Box::new(App { counter: Counter::new(), name: String::new() }) }
    pub fn run() {
        let mut app = make();
        app.counter.bump();
        app.name.push('x');
        let shared = Mutex::new(make());
        shared.lock().unwrap().counter.bump();
        println!("{} {}", app.counter.get(), shared.lock().unwrap().counter.get());
    }
}

mod generic {
    pub struct Level { n: u8 }
    impl Level {
        pub fn new() -> Self { Level { n: 0 } }
        pub fn raise(&mut self) { self.n += 1; }
        pub fn get(&self) -> u8 { self.n }
    }
    pub struct App { level: Level }
    fn describe<T>(value: &T, with: impl Fn(&T) -> u8) -> u8 { with(value) }
    fn pass<T>(value: T) -> T { value }
    fn each<T>(value: &mut T, mut with: impl FnMut(&mut T)) { with(value) }
    pub fn run() {
        let mut app = pass(App { level: Level::new() });
        app.level.raise();
        each(&mut app, |app| app.level.raise());
        println!("{}", describe(&app, |app| app.level.get()));
    }
}

mod consumed {
    pub struct Total { sum: u64, parts: Vec<u64> }
    impl Total {
        pub fn new() -> Self { Total { sum: 0, parts: Vec::new() } }
        pub fn add(&mut self, part: u64) { self.sum += part; self.parts.push(part); }
        pub fn into_parts(self) -> Vec<u64> { self.parts }
    }
    pub fn run() {
        let mut total = Total::new();
        total.add(2);
        total.add(3);
        println!("{:?}", total.into_parts());
    }
}

mod matched {
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum Phase { Idle, Busy { job: u32 } }
    pub struct Machine { phase: Phase, done: Vec<u32> }
    impl Machine {
        pub fn new() -> Self { Machine { phase: Phase::Idle, done: Vec::new() } }
        pub fn step(&mut self, job: u32) {
            match &mut self.phase {
                Phase::Busy { job: running } => { self.done.push(*running); *running = job; }
                Phase::Idle => { self.phase = Phase::Busy { job }; }
            }
        }
        pub fn phase(&self) -> Phase { self.phase }
    }
    pub fn run() {
        let mut machine = Machine::new();
        machine.step(1);
        machine.step(2);
        println!("{:?}", machine.phase());
    }
}

mod derived {
    pub struct Tally { n: u32 }
    impl Tally {
        pub fn new() -> Self { Tally { n: 0 } }
        pub fn add(&mut self, by: u32) { self.n += by; }
        pub fn get(&self) -> u32 { self.n }
    }
    #[derive(Clone, Copy, Debug)]
    pub struct View<'a> { label: &'a str, n: u32 }
    #[derive(Clone, Copy, Debug)]
    pub struct Pair<T> { left: T, right: T }
    pub fn run() {
        let mut tally = Tally::new();
        tally.add(2);
        let view = View { label: "tally", n: tally.get() };
        let pair = Pair { left: view, right: view };
        println!("{:?} {:?}", pair.left, pair.right.n);
    }
}

mod waited {
    use std::future::Future;
    use std::pin::pin;
    use std::task::{Context, Poll, Waker};

    pub struct Session { id: u32, seen: u32 }
    impl Session {
        pub async fn open(id: u32) -> Session { Session { id, seen: 0 } }
        pub fn note(&mut self) { self.seen += 1; }
        pub fn seen(&self) -> u32 { self.seen + self.id }
    }
    async fn tick() {}
    async fn work() -> u32 {
        tick().await;
        let seen = {
            let mut session = Session::open(7).await;
            session.note();
            session.seen()
        };
        tick().await;
        seen
    }
    pub fn run() {
        let mut work = pin!(work());
        let mut context = Context::from_waker(Waker::noop());
        while let Poll::Pending = work.as_mut().poll(&mut context) {}
    }
}

mod lent {
    pub struct Meter { total: u32 }
    pub trait Update { type View; fn update(&mut self) -> &Self::View; }
    impl Meter {
        pub fn new() -> Self { Meter { total: 0 } }
        pub fn add(&mut self, by: u32) -> &u32 { self.total += by; &self.total }
        pub fn add_some(&mut self, by: u32) -> Option<&u32> {
            self.total += by;
            (self.total > 0).then_some(&self.total)
        }
    }
    impl Update for Meter {
        type View = u32;
        fn update(&mut self) -> &u32 { self.total += 1; &self.total }
    }
    pub fn run() {
        let mut meter = Meter::new();
        println!("{}", meter.add(2));
        println!("{:?} {}", meter.add_some(1).copied(), meter.update());
    }
}

mod tokens {
    use std::cell::RefCell;

    pub struct Ticket { n: u8 }
    pub fn mint(n: u8) -> Ticket { Ticket { n } }
    thread_local! { static SEEN: RefCell<Vec<Ticket>> = RefCell::new(Vec::new()); }
    pub fn run() {
        // (Minted in the fn's own body: a closure that calls the maker can
        // be handed on and run where no `madeBy` fn is. Review 1 of the
        // review-14 build.)
        let pair = [mint(1), mint(2)].map(|ticket| ticket);
        SEEN.with(|seen| seen.borrow_mut().extend(pair));
        println!("{}", SEEN.with(|seen| seen.borrow().iter().map(|ticket| ticket.n).sum::<u8>()));
    }
}

mod shapes {
    use std::fmt;
    use std::marker::PhantomData;
    use std::time::Duration;

    pub struct Link {
        last_error: Option<std::io::ErrorKind>,
        tries: std::cmp::Reverse<u32>,
        waited: Duration,
        unit: PhantomData<()>,
    }
    impl Link {
        pub fn new() -> Self {
            Link { last_error: None, tries: std::cmp::Reverse(0), waited: Duration::ZERO, unit: PhantomData }
        }
        pub fn fail(&mut self, kind: std::io::ErrorKind) {
            self.last_error = Some(kind);
            self.tries.0 += 1;
        }
    }
    impl fmt::Debug for Link {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Link").field("tries", &self.tries.0).field("last", &self.last_error).finish()
        }
    }
    pub struct App { link: Link }
    impl fmt::Debug for App {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("App").field("link", &self.link).finish()
        }
    }
    pub unsafe trait Pod: Copy {}
    unsafe impl Pod for u8 {}
    #[derive(Clone, Copy)]
    pub struct Rgba<T>([T; 4]);
    unsafe impl<T: Pod> Pod for Rgba<T> {}
    pub fn run() {
        let mut app = App { link: Link::new() };
        app.link.fail(std::io::ErrorKind::TimedOut);
        let shown: [Box<dyn fmt::Debug>; 2] = [Box::new(7u8), Box::new("x")];
        println!("{app:?} {shown:?}");
    }
}

// Review 14: a constant is judged by what its initializer RUNS, not by its
// type. None of these runs a maker, so none holds a stamp: the everyday
// table that starts empty, a named `None`, a generic container's `EMPTY`
// used at the token's type, and the `thread_local!` form its documentation
// recommends. (Read by type, each was refused.)
mod empties {
    use std::cell::RefCell;
    pub struct Stamped { value: u32 }
    impl Stamped {
        pub fn new(value: u32) -> Self { Stamped { value } }
        pub fn value(&self) -> u32 { self.value }
    }
    const NONE: Option<Stamped> = None;
    pub struct Slots<T, const N: usize> { items: [Option<T>; N] }
    impl<T, const N: usize> Slots<T, N> {
        const EMPTY: Option<T> = None;
        pub fn new() -> Self { Slots { items: [Self::EMPTY; N] } }
    }
    thread_local! { static LATEST: RefCell<Option<Stamped>> = const { RefCell::new(None) }; }
    pub fn run() {
        let mut pending: [Option<Stamped>; 4] = [const { None }; 4];
        pending[0] = Some(Stamped::new(1));
        let mut named = [NONE, NONE];
        named[1] = Some(Stamped::new(2));
        let mut slots: Slots<Stamped, 2> = Slots::new();
        slots.items[0] = Some(Stamped::new(3));
        let fourth = Stamped::new(4);
        LATEST.with(move |latest| *latest.borrow_mut() = Some(fourth));
        let seen = LATEST.with(|latest| latest.borrow().as_ref().map(Stamped::value));
        println!("{:?} {:?}", pending[0].as_ref().map(Stamped::value), seen);
    }
}

// Review 14: a fn whose where-clause holds for no lifetime (so nothing can
// call it) names instances the compiler never makes. Asked what one of those
// uses, the compiler panics: the check asks only of instances whose own
// bounds hold.
mod unmet {
    pub struct Cell { n: u32 }
    impl Cell {
        pub fn new() -> Self { Cell { n: 0 } }
        pub fn tick(&mut self) { self.n += 1; }
    }
    pub struct App { cell: Cell }
    pub struct View<'a> { app: &'a App, row: u16 }
    fn twice<'a>(app: &'a mut App) -> Vec<&'a mut App> where &'a mut App: Clone { vec![app; 2] }
    fn dump<'a>(view: &View<'a>) where View<'a>: std::fmt::Debug { eprintln!("{view:?}"); }
    pub fn run() { let mut app = App { cell: Cell::new() }; app.cell.tick(); }
}

mod uncalled {
    pub struct Depth { n: u32 }
    impl Depth {
        pub fn new() -> Self { Depth { n: 0 } }
        pub fn note(&mut self) { self.n += 1; }
    }
    fn grow<T>(depth: &mut Depth) -> usize {
        let _never = |depth: &mut Depth| grow::<(T,)>(depth);
        depth.note();
        std::mem::size_of::<T>()
    }
    pub fn run() {
        let mut depth = Depth::new();
        println!("{}", grow::<u8>(&mut depth));
    }
}

pub struct Dial { at: u8 }
impl Dial {
    pub fn new() -> Self { Dial { at: 0 } }
    pub fn turn(&mut self) { self.at += 1; }
}

fn main() {
    let mut dial = Dial::new();
    dial.turn();
    waited::run();
    lent::run();
    tokens::run();
    shapes::run();
    uncalled::run();
    empties::run();
    unmet::run();
    derived::run();
    policy::run();
    boxed::run();
    generic::run();
    consumed::run();
    matched::run();
}

clean {
    import Trust.Binding
    namespace Sealed
    open Trust.Protocol
    def cell : Trust.Protocol.Seal :=
      seals "policy::order::PolicyCell" ["PolicyCell::offer"] ["PolicyCell::new"] ["policy::App::new"] []
    def stamp : Trust.Protocol.Seal :=
      seals "policy::order::Stamped" [] ["StampSource::stamp"] ["watcher"] []
    def source : Trust.Protocol.Seal :=
      seals "policy::order::StampSource" ["StampSource::stamp"] ["StampSource::new"] ["watcher"] []
    def counter : Trust.Protocol.Seal :=
      seals "boxed::Counter" ["bump"] ["Counter::new"] ["make"] ["Box::new", "Box::drop", "Mutex::new", "Mutex::lock", "Result::unwrap", "MutexGuard::deref_mut", "MutexGuard::deref", "MutexGuard::drop"]
    def level : Trust.Protocol.Seal :=
      seals "generic::Level" ["raise"] ["Level::new"] ["generic::run"] []
    def total : Trust.Protocol.Seal :=
      seals "consumed::Total" ["Total::add"] ["Total::new"] ["consumed::run"] []
    def machine : Trust.Protocol.Seal :=
      seals "matched::Machine" ["step"] ["Machine::new"] ["matched::run"] []
    def tally : Trust.Protocol.Seal :=
      seals "derived::Tally" ["Tally::add"] ["Tally::new"] ["derived::run"] []
    def session : Trust.Protocol.Seal :=
      seals "waited::Session" ["Session::note"] ["Session::open"] ["work"] []
    def meter : Trust.Protocol.Seal :=
      seals "lent::Meter" ["Meter::add", "Meter::add_some", "Meter::update"] ["Meter::new"] ["lent::run"] []
    def ticket : Trust.Protocol.Seal :=
      seals "tokens::Ticket" [] ["mint"] ["tokens::run"] []
    def link : Trust.Protocol.Seal :=
      seals "shapes::Link" ["Link::fail"] ["Link::new"] ["shapes::run"] ["Argument::new_debug"]
    def depth : Trust.Protocol.Seal :=
      seals "uncalled::Depth" ["Depth::note"] ["Depth::new"] ["uncalled::run"] []
    def stamped : Trust.Protocol.Seal :=
      seals "empties::Stamped" [] ["empties::Stamped::new"] ["empties::run"] []
    def unmet : Trust.Protocol.Seal :=
      seals "unmet::Cell" ["unmet::Cell::tick"] ["unmet::Cell::new"] ["unmet::run"] []
    def dial : Trust.Protocol.Seal :=
      seals "Dial" ["Dial::turn"] ["Dial::new"] ["main"] []
    end Sealed
}

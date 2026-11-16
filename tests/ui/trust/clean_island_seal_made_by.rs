//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! A maker called in a closure, or an `async` block, of a `madeBy` fn
//! (`Trust.Protocol.Seal`): each seal must FAIL. The closure is a value the
//! fn can hand on, and code the seal does not name can run it when no
//! `madeBy` fn is running: `.map(mint)` spelt `|g| mint(g)`. Review 1 of the
//! review-14 build found `pointer` and `boxed` passing, and `forger` minting
//! two stamps after `watcher` returned.
//!
//! - `pointer`: `watcher` hands out `|g| mint(g)` as a `fn(u64) -> Stamped`.
//! - `boxed`: the same closure as a `Box<dyn Fn(u64) -> Stamped>`.
//! - `spawned`: the maker called in the closure a thread runs.
//! - `deferred`: the maker called in an `async` block the fn hands back.
//!
//! The maker called in the fn's own body, its value moved into the
//! closure, holds: `_made_by_holds.rs`.

#![allow(unused)]

mod pointer {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn watcher() -> fn(u64) -> Stamped {
        |g| mint(g) //~ NOTE this calls the maker `pointer::mint` in a closure (or an `async` block) in `pointer::watcher`
    }
    pub fn forger(by_pointer: fn(u64) -> Stamped) -> u64 {
        by_pointer(99).generation
    }
}

mod boxed {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn watcher() -> Box<dyn Fn(u64) -> Stamped> {
        Box::new(|g| mint(g)) //~ NOTE this calls the maker `boxed::mint` in a closure (or an `async` block) in `boxed::watcher`
    }
    pub fn forger(boxed: &dyn Fn(u64) -> Stamped) -> u64 {
        boxed(100).generation
    }
}

mod spawned {
    pub struct Source { next: u64 }
    impl Source {
        pub fn new() -> Self { Source { next: 0 } }
        pub fn stamp(&mut self) -> u64 { self.next += 1; self.next }
    }
    pub fn spawn() -> std::thread::JoinHandle<u64> {
        std::thread::spawn(move || {
            let mut source = Source::new(); //~ NOTE this calls the maker `spawned::Source::new` in a closure (or an `async` block) in `spawned::spawn`
            source.stamp()
        })
    }
}

mod deferred {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn watcher() -> impl std::future::Future<Output = Stamped> {
        async move { mint(1) } //~ NOTE this calls the maker `deferred::mint` in a closure (or an `async` block) in `deferred::watcher`
    }
}

fn main() {
    println!("{}", pointer::forger(pointer::watcher()));
    println!("{}", boxed::forger(&*boxed::watcher()));
    println!("{}", spawned::spawn().join().unwrap());
    let _ = deferred::watcher();
}

clean {
    import Trust.Binding
    namespace MadeBy
    open Trust.Protocol
    def pointer : Trust.Protocol.Seal := seals "pointer::Stamped" [] ["pointer::mint"] ["pointer::watcher"] []
    def boxed : Trust.Protocol.Seal := seals "boxed::Stamped" [] ["boxed::mint"] ["boxed::watcher"] ["Box::new", "Box::drop"]
    def spawned : Trust.Protocol.Seal := seals "spawned::Source" ["spawned::Source::stamp"] ["spawned::Source::new"] ["spawned::spawn"] []
    def deferred : Trust.Protocol.Seal := seals "deferred::Stamped" [] ["deferred::mint"] ["deferred::watcher"] []
    end MadeBy
}
//~^^^^^^ ERROR seal `MadeBy.pointer` on `Stamped` does not hold
//~^^^^^^ ERROR seal `MadeBy.boxed` on `Stamped` does not hold
//~^^^^^^ ERROR seal `MadeBy.spawned` on `Source` does not hold
//~^^^^^^ ERROR seal `MadeBy.deferred` on `Stamped` does not hold

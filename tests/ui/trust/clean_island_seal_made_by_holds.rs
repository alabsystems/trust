//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_made_by.rs`: a `madeBy` fn that calls the
//! maker in its OWN body HOLDS, whatever it then hands the value to
//! (`Trust.Protocol.Seal`).
//!
//! - `moved`: a token made in `spawn` itself and moved into the closure the
//!   thread runs (a token, with no writer, may cross a thread freely).
//! - `threaded`: the closure a thread runs calls a fn of its own, named in
//!   `madeBy`, which makes the source in its own body (the shape for a
//!   value with a writer: none crosses `thread::spawn`).
//! - `mapped`: stamps made in the fn's body, passed through `map`.
//! - `asyncfn`: a `madeBy` fn that is an `async fn`: its body is its own,
//!   run when the future it hands back is polled (as for a maker).
//! - `named`: the closure calls a fn of its own that the seal names in
//!   `madeBy`, and that fn calls the maker in its own body.

#![allow(unused)]

mod moved {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn spawn() -> std::thread::JoinHandle<u64> {
        let stamp = mint(1);
        std::thread::spawn(move || stamp.generation)
    }
}

mod threaded {
    pub struct Source { next: u64 }
    impl Source {
        pub fn new() -> Self { Source { next: 0 } }
        pub fn stamp(&mut self) -> u64 { self.next += 1; self.next }
    }
    pub fn watch() -> u64 {
        let mut source = Source::new();
        source.stamp()
    }
    pub fn spawn() -> std::thread::JoinHandle<u64> {
        std::thread::spawn(move || watch())
    }
}

mod mapped {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn watcher() -> u64 {
        let stamps = [mint(1), mint(2)].map(|stamp| stamp);
        stamps.iter().map(|stamp| stamp.generation).sum()
    }
}

mod asyncfn {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub async fn watcher() -> u64 {
        mint(1).generation
    }
}

mod named {
    pub struct Stamped { generation: u64 }
    pub fn mint(generation: u64) -> Stamped { Stamped { generation } }
    pub fn one(generation: u64) -> Stamped { mint(generation) }
    pub fn watcher() -> u64 {
        let make = |g| one(g);
        make(3).generation
    }
}

fn main() {
    println!("{}", moved::spawn().join().unwrap());
    println!("{}", threaded::spawn().join().unwrap());
    println!("{}", mapped::watcher());
    let _ = asyncfn::watcher();
    println!("{}", named::watcher());
}

clean {
    import Trust.Binding
    namespace MadeByHolds
    open Trust.Protocol
    def moved : Trust.Protocol.Seal := seals "moved::Stamped" [] ["moved::mint"] ["moved::spawn"] []
    def threaded : Trust.Protocol.Seal := seals "threaded::Source" ["threaded::Source::stamp"] ["threaded::Source::new"] ["threaded::watch"] []
    def mapped : Trust.Protocol.Seal := seals "mapped::Stamped" [] ["mapped::mint"] ["mapped::watcher"] []
    def asyncfn : Trust.Protocol.Seal := seals "asyncfn::Stamped" [] ["asyncfn::mint"] ["asyncfn::watcher"] []
    def named : Trust.Protocol.Seal := seals "named::Stamped" [] ["named::mint"] ["named::one"] []
    end MadeByHolds
}

//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! An inline `const { }` in a STATIC's initializer that runs a maker
//! (`Trust.Protocol.Seal`): each seal must FAIL (an inline `const` that runs
//! a maker is refused wherever it is), and the note says what is so. Review
//! 3 of the review-14 build found the notes written for a fn that runs: "each
//! run of `S` copies the value", "call the maker in the fn's own body",
//! "keep it in a `static`". A static does not run; the inline `const` is
//! evaluated once and its one value becomes the static's; the remedy is to
//! drop the `const { }` (`_static_const_holds.rs`).
//!
//! - `maker`: `static S = const { mint(7) }`, `S` named in `madeBy`.
//! - `via_fn`: `static S = const { watcher() }`, `watcher` named in `madeBy`.
#![allow(unused)]

mod maker {
    pub struct Stamped { generation: u64 }
    impl Stamped { pub const fn get(&self) -> u64 { self.generation } }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub const fn watcher() -> Stamped { mint(1) }
    pub static S: Stamped = const { mint(7) }; //~ NOTE this inline `const` in the static `maker::S` runs
}

mod via_fn {
    pub struct Stamped { generation: u64 }
    impl Stamped { pub const fn get(&self) -> u64 { self.generation } }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub const fn watcher() -> Stamped { mint(1) }
    pub static S: Stamped = const { watcher() }; //~ NOTE this inline `const` in the static `via_fn::S` runs
}

fn main() {
    println!("{} {}", maker::S.get(), via_fn::S.get());
}

clean {
    import Trust.Binding
    namespace StaticConst
    open Trust.Protocol
    def maker : Trust.Protocol.Seal := seals "maker::Stamped" [] ["maker::mint"] ["maker::watcher", "maker::S"] []
    def via_fn : Trust.Protocol.Seal := seals "via_fn::Stamped" [] ["via_fn::mint"] ["via_fn::watcher"] []
    end StaticConst
}
//~^^^^ ERROR seal `StaticConst.maker` on `Stamped` does not hold
//~^^^^ ERROR seal `StaticConst.via_fn` on `Stamped` does not hold

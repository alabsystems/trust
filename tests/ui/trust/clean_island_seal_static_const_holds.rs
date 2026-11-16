//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The twin of `clean_island_seal_static_const.rs` (`Trust.Protocol.Seal`):
//! the same statics with the `const { }` dropped. A static's initializer is
//! evaluated once and its value is the static's own; both seals HOLD.
#![allow(unused)]

mod maker {
    pub struct Stamped { generation: u64 }
    impl Stamped { pub const fn get(&self) -> u64 { self.generation } }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub const fn watcher() -> Stamped { mint(1) }
    pub static S: Stamped = mint(7);
}

mod via_fn {
    pub struct Stamped { generation: u64 }
    impl Stamped { pub const fn get(&self) -> u64 { self.generation } }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub const fn watcher() -> Stamped { mint(1) }
    pub static S: Stamped = watcher();
}

fn main() {
    println!("{} {}", maker::S.get(), via_fn::S.get());
}

clean {
    import Trust.Binding
    namespace StaticConstHolds
    open Trust.Protocol
    def maker : Trust.Protocol.Seal := seals "maker::Stamped" [] ["maker::mint"] ["maker::watcher", "maker::S"] []
    def via_fn : Trust.Protocol.Seal := seals "via_fn::Stamped" [] ["via_fn::mint"] ["via_fn::watcher"] []
    end StaticConstHolds
}

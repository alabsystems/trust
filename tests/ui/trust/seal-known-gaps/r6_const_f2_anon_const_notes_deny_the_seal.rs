//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -A warnings
//@ check-fail
//@ known-bug: unknown
//@ dont-check-compiler-stderr
//@ error-pattern: this builds a `Stamped` in `build_in_maker::mint`, which is not one of its makers
//@ error-pattern: this calls the maker `call_in_made_by::mint` in `call_in_made_by::watcher`, which is not a fn the seal says may
//@ error-pattern: this calls the maker `const_arg_in_made_by::mint` in `const_arg_in_made_by::watcher`, which is not a fn the seal says may
//@ error-pattern: this calls the maker `in_static::mint` in `in_static::S`, which is not a fn the seal says may
//! KNOWN GAP of the sealed-types check (review 6 of the review-14 build,
//! 2026-10-16; R6-CONST-F2, a false note; lens: constants). Recorded, not
//! fixed (docs/DECISION_QUEUE.md, "sealed types land with review 6's findings
//! recorded, not fixed").
//! Each seal below is refused (fail-closed), and each note DENIES what the
//! seal says: it names the maker `mint` "not one of its makers", or the
//! `madeBy` fn `watcher` (the `madeBy` static `S`) "not a fn the seal says
//! may", where the seal names each. What is refused is an ANONYMOUS constant
//! inside the maker or `madeBy` item (an array length, a const generic
//! argument, an array length in a static's initializer), evaluated when the
//! program is compiled; `madeBy` cannot name one, so the note offers no
//! remedy. The same shapes in an inline `const { }` get the accurate note
//! ("in an inline `const` in its maker .., when the program is compiled").
//! The file passes while the false sentences are printed; when a fix changes
//! them, it fails: that is the win. Give the program a must-fail fixture whose
//! notes say what is refused, and delete this file.
//! Root, as its skeptic put it: sealed.rs `read_body` sets `root =
//! typeck_root_def_id(def)`; an AnonConst is its own typeck root (an
//! InlineConst is not), so it reads as `Own::Body`, and `report` compares the
//! anon const's own DefId with the seal's makers and `madeBy` (`is(&seal.makers,
//! root)`), both false. The note's `at` is `item_path(root)`, which skips the
//! unnamed segment and prints the parent's path.

#![allow(unused)]
mod build_in_maker {
    pub struct Stamped { generation: u64 }
    pub const fn mint(g: u64) -> Stamped {
        let a = [0u8; { Stamped { generation: 3 }.generation as usize }];
        Stamped { generation: g + a.len() as u64 }
    }
    pub fn watcher() -> Stamped { mint(1) }
}
mod call_in_made_by {
    pub struct Stamped { generation: u64 }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub fn watcher() -> Stamped { let a = [0u8; { mint(3).generation as usize }]; mint(a.len() as u64) }
}
mod const_arg_in_made_by {
    pub struct Stamped { generation: u64 }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub fn h<const N: u64>() -> u64 { N }
    pub fn watcher() -> Stamped { mint(h::<{ mint(3).generation }>()) }
}
mod in_static {
    pub struct Stamped { generation: u64 }
    pub const fn mint(g: u64) -> Stamped { Stamped { generation: g } }
    pub static S: Stamped = mint([0u8; { mint(1).generation as usize }].len() as u64);
}
fn main() {
    let _ = build_in_maker::watcher();
    let _ = call_in_made_by::watcher();
    let _ = const_arg_in_made_by::watcher();
    let _ = &in_static::S;
}
clean {
    import Trust.Binding
    namespace R6ConstF2
    open Trust.Protocol
    def a : Trust.Protocol.Seal := seals "build_in_maker::Stamped" [] ["build_in_maker::mint"] ["build_in_maker::watcher"] []
    def b : Trust.Protocol.Seal := seals "call_in_made_by::Stamped" [] ["call_in_made_by::mint"] ["call_in_made_by::watcher"] []
    def c : Trust.Protocol.Seal := seals "const_arg_in_made_by::Stamped" [] ["const_arg_in_made_by::mint"] ["const_arg_in_made_by::watcher"] []
    def d : Trust.Protocol.Seal := seals "in_static::Stamped" [] ["in_static::mint"] ["in_static::S"] []
    end R6ConstF2
}

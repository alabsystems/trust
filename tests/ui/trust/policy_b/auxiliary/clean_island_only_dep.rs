//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency holding a `clean { … }` island and no assembly. The island
//! takes `DefKind::GlobalAsm` in this crate's metadata (there is no island def kind)
//! but lowers no machine code, and the encoder marks it in the
//! `trust_clean_island_item` table: it cannot define an allocator symbol.

clean {
    theorem island_only_dependency_holds : 0 = 0 := rfl
}

pub fn half(x: u8) -> u8 {
    x / 2
}

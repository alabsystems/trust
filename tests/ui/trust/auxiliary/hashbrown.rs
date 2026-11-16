//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency that SHARES A SYSROOT CRATE'S NAME. Its file name
//! makes its crate name `hashbrown` — the name of the sysroot-internal crate
//! behind `std::collections::HashMap`, and an ordinary crates.io name. Compiled
//! the way `targo` compiles every dependency unit (`-Ztrust-verify=off`,
//! `-Zalways-encode-mir`). Consumed by
//! `xcrate_drop_glue_sysroot_name_shadowed_not_credited.rs` (the destructor
//! credit) and `vanilla_hashbrown_name_shadowed_stays_closed.rs` (the vanilla
//! callee class); see those files.
//!
//! `raw::RawTable` renders to the SAME path as the sysroot's
//! `hashbrown::raw::RawTable`. Its `drop` PANICS on 7 — that is the assertion.
//! Do not make it total.
pub mod raw {
    pub struct RawTable(pub u32);
    impl Drop for RawTable {
        fn drop(&mut self) {
            if self.0 == 7 {
                panic!("boom");
            }
        }
    }
}

/// W4 HASHMAP (2026-09-25): an item at the SAME path as the sysroot
/// `hashbrown::map::HashMap` the vanilla class now credits (by structural
/// identity — the crate std's `HashMap` field is declared in — never by name).
/// Consumed by `hashbrown_namesake_dep_not_vanilla.rs`. `insert` PANICS on key 7 — that is
/// the assertion. Do not make it total.
pub mod map {
    pub struct HashMap {
        pub k: u64,
        pub v: u64,
    }
    impl HashMap {
        pub fn insert(&mut self, k: u64, v: u64) -> Option<u64> {
            if k == 7 {
                panic!("boom");
            }
            let old = self.v;
            self.k = k;
            self.v = v;
            Some(old)
        }
    }
}

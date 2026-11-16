//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_check_build_holds.rs`: the source of
//! `seal_dep_checked.rs`, built in full, so that its generic fns' MIR is in
//! its metadata. Safe, and sound.

/// Counts what it is handed; writes nothing.
pub fn count_refs<P: std::ops::Deref>(items: &[P]) -> usize {
    items.iter().filter(|item| std::mem::size_of_val(&**item) > 0).count()
}

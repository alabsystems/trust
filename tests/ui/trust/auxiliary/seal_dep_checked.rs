//@ edition: 2021
//@ compile-flags: --crate-type=rlib --emit=metadata -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_check_build.rs`, built as `cargo check`
//! builds one: metadata only, with no MIR for its generic fns. The same
//! source, built in full, is `seal_dep_built.rs`. Safe, and sound.

/// Counts what it is handed; writes nothing.
pub fn count_refs<P: std::ops::Deref>(items: &[P]) -> usize {
    items.iter().filter(|item| std::mem::size_of_val(&**item) > 0).count()
}

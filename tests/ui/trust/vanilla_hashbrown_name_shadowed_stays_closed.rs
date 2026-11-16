//@ needs-trust-verify
// `aux-crate`, not `aux-build`: the aux's crate name is `hashbrown`, so a bare
// `-L` search leaves `extern crate hashbrown` ambiguous against the sysroot's
// own `hashbrown` (E0464 "multiple candidates") before any Trust check runs.
//@ aux-crate: hashbrown=hashbrown.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! The vanilla class admits std's private `hashbrown` only while no crate
//! OUTSIDE the sysroot shares its name (`def_is_in_sysroot_implementation_crate`).
//! The ledger that tolerates an absent callee, and the row it judges, are keyed
//! by the RENDERED callee path, which spells the crate NAME — the same channel
//! through which a dependency named `hashbrown` once inherited the sysroot
//! `RawTable`'s destructor credit
//! (`xcrate_drop_glue_sysroot_name_shadowed_not_credited.rs`).
//!
//! So with the verify-off `hashbrown` dependency in the graph, the SAME `entry`
//! program `policy_b/hashmap_through_hashbrown_is_vanilla.rs` builds is refused:
//! the cost of the namesake, fail-closed. Keep it refused; fix the compiler,
//! never this file.
// Loading the crate is enough: `extern crate` puts it in the crate graph, and
// `f` itself touches nothing of it, so the only thing that can refuse `f` is the
// namesake.
extern crate hashbrown;

pub fn f(m: &mut std::collections::HashMap<u32, u32>, k: u32) { //~ ERROR Trust strict verification failed
    let e = m.entry(k).or_insert(0);
    *e = e.saturating_add(1);
}

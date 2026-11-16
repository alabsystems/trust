//@ needs-trust-verify
//@ revisions: vanilla vanilla_release_std
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[vanilla] check-pass
//@[vanilla] needs-std-debug-assertions (pinned by `vanilla_release_std`)
//@[vanilla_release_std] check-fail
//@[vanilla_release_std] ignore-std-debug-assertions (pinned by `vanilla`)
#![crate_type = "lib"]
//! `std::collections::HashMap` at foundational types stays inside the tolerated
//! vanilla-sysroot class, although every one of its methods forwards into std's
//! PRIVATE implementation crate, `hashbrown`.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29. `HashMap<K, V>` is a one-field wrapper
//! around `hashbrown::HashMap<K, V, RandomState>`. The class admitted only
//! `core`/`alloc`/`std` code, so the `base` field made `HashMap<u32, u32>`
//! non-foundational, and the hashbrown callees a bundled `entry`/`values` reaches
//! (`hashbrown::rustc_entry::..::rustc_entry`, `RawTable::insert_no_grow`,
//! `hashbrown::map::HashMap::iter`) were refused — the first as NOT-IN-LEDGER,
//! because the bundle walk recorded a callee's verdict only after declining its
//! crate. The same programs over a `BTreeMap` (an `alloc` type) built. Five of
//! the 659 ordinary-Rust sweep programs flipped, and none regressed.
//!
//! The admitted crates are std's private implementation crates only: resident in
//! the compiler's own sysroot, reached through no dependency edge this crate
//! names, and with no namesake outside the sysroot
//! (`def_is_in_sysroot_implementation_crate`). A user key, value, hasher or
//! closure still leaves the class (`hashmap_non_foundational_stays_closed.rs`),
//! and so does a dependency named `hashbrown`
//! (`../vanilla_hashbrown_name_shadowed_stays_closed.rs`).
//!
//! This is a POLICY tolerance, not a proof: the rows stay runtime-checked and
//! `-Ztrust-policy=certify` still demands full static discharge.
//!
//! Trust (2026-10-19, std-config pin): measured under BOTH std configurations on the a7c37f9f0ee5
//! pin. The pre-existing pin was measured under a debug-assertions std; under the canonical
//! release std (debug-assertions-std=false) the verdict flips, so each configuration has its
//! own revision (KNOWN_HAZARDS, the debug-assertions std entry).
//! Under a release std, `bump`'s bundled members carry no runtime-checked row,
//! so the zero-obligation gate refuses it (DECISION_QUEUE, "Bundled std-member
//! losses" — recovery work listed there).
use std::collections::{HashMap, HashSet};

pub fn bump(m: &mut HashMap<u32, u32>, k: u32) {
    // CAPABILITY RETURNED on the 1.101 toolchain (2026-10-18, measured: the
    // body builds under the default policy with its absent-callee
    // assumption row carried as vanilla runtime-checked — the pre-loss
    // policy-B behaviour this file measures). Was: CAPABILITY LOSS,
    // re-pinned 2026-10-15 (ZERO-ROW-GATE: the body published no row of its
    // own, and its `HashMap::entry` call into BUNDLED std bodies was
    // discharged by no registry the gate reads). On 1.101 the hashbrown
    // 0.17 entry is charged as an absent sysroot callee instead, so the row
    // is published and the gate does not fire; under `certify` the row
    // still refuses, as the file header requires.
    let e = m.entry(k).or_insert(0);
    *e = e.saturating_add(1);
}

pub fn bump_existing(m: &mut HashMap<u32, u32>, k: u32) {
    if let Some(x) = m.get_mut(&k) {
        *x = x.saturating_add(1);
    }
}

pub fn largest(m: &HashMap<u32, u32>) -> u32 {
    m.values().copied().max().unwrap_or(0)
}

pub fn remember(s: &mut HashSet<String>, k: &str) -> bool {
    s.insert(k.to_string())
}

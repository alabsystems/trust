#![crate_type = "lib"]
// MUTANT twin of proved/btreemap_string_registry.rs — the BUG this pins: a keyed
// `BTreeMap` lookup dispatches the KEY type's `Ord` (user code), and here that
// user `cmp` PANICS on a reachable input (k.0 == 13). `get` must therefore stay
// FAIL-CLOSED (exit 1) under the default strict policy: the bridge's total-summary
// allowlist admits only the zero-comparison `::BTreeMap::iter` CONSTRUCTOR
// (crate-origin anchored, exact suffix), NEVER the keyed `get`/`contains_key`
// family. What flips this gate: wrongly adding `::BTreeMap::get` (or a blanket
// `::get` suffix) to `total_no_panic_call_summary` — the exact false-proof class
// the oracle's `BTreeMap::<UserOrdK>::get` pin guards — would summarize this call
// panic-free and verify a function that panics at runtime.
use std::cmp::Ordering;
use std::collections::BTreeMap;

pub struct PanicKey(pub u32);

impl PartialEq for PanicKey {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for PanicKey {}
impl PartialOrd for PanicKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PanicKey {
    fn cmp(&self, other: &Self) -> Ordering {
        // The user comparator PANICS on a reachable key value.
        if self.0 == 13 {
            panic!("poisoned key");
        }
        self.0.cmp(&other.0)
    }
}

pub fn get_weight(m: &BTreeMap<PanicKey, u32>, k: PanicKey) -> u32 {
    match m.get(&k) {
        Some(w) => *w,
        None => 0,
    }
}

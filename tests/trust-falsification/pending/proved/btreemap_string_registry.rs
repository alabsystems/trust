#![crate_type = "lib"]
// T3+T4 (bridge lowering, aterm-scrollback batch): the aterm-spec XREF shape — a
// `BTreeMap<String, _>` get/iter loop over a static `&[(&str, u32)]` registry.
// MUST PROVE (exit 0) under the default strict policy. One fixture pins BOTH fixes
// in the trust-ir-bridge lane:
//   * `ConstValue::OpaqueConst` operand typing — the static REGISTRY constant is
//     an opaque ref-to-slice; before the fix the operand-type catch-alls
//     ("unknown const"/"unknown operand variant") ABORTED the whole-function
//     native lowering, poisoning every obligation to Unsupported;
//   * the `::BTreeMap::iter` total summary — the in-order iterator CONSTRUCTOR
//     runs ZERO user-`Ord` comparisons and cannot panic; before the fix the call
//     fell to the absent-callee assumption.
// The String-keyed `get` stays OUTSIDE the total envelope (keyed lookups
// dispatch `Ord` on the key) and is discharged by the formula lane; its
// user-`Ord` twin MUST keep failing closed — that soundness edge is pinned by
// mutant/user_ord_btreemap_get.rs (a key type whose `cmp` panics), which flips
// this gate if `::BTreeMap::get` / a blanket `::get` suffix ever creeps into
// `total_no_panic_call_summary`.
use std::collections::BTreeMap;

static REGISTRY: &[(&str, u32)] = &[("cursor", 1), ("scroll", 2), ("wrap", 3)];

/// Map-first lookup with a registry fallback: `get` on the String-keyed map,
/// then the linear scan over the static table (the OpaqueConst constant).
pub fn xref_weight(specs: &BTreeMap<String, u32>, key: &str) -> u32 {
    if let Some(w) = specs.get(key) {
        return w.saturating_add(0);
    }
    let mut total: u32 = 0;
    for (name, w) in REGISTRY {
        if *name == key {
            total = total.saturating_add(*w);
        }
    }
    total
}

/// The in-order iteration (`BTreeMap::iter` — the total zero-comparison
/// constructor) with a saturating fold: statically panic-free.
pub fn ordered_sum(specs: &BTreeMap<String, u32>) -> u64 {
    let mut sum: u64 = 0;
    for (_name, w) in specs.iter() {
        sum = sum.saturating_add(u64::from(*w));
    }
    sum
}

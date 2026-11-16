//! Trust (2026-10-04, wave 13): the `callee_key` a PRE-CARRIER fixture lacks.
//!
//! Several `tests/fixtures/*_mir.json` files are real extracted MIR captured before
//! the extractor minted `Terminator::Call::callee_key`. Since SLICE-INHERENT-1 and
//! NUM-METHOD-ANCHOR-1 (2026-10-04) the `<[T]>` slice-method and std `f64` recognizers
//! decide on that key first, so a keyless call is (correctly) not std's and those
//! fixtures would lose the facts they were captured to pin. This gives every keyless
//! DIRECT call the residency key today's extractor mints (`callee_key_for`:
//! `krate_is_real_sysroot` for a callee defined in `core`/`alloc`/`std`, measured on
//! `scratchpad/stage1-w11fix`), reading the defining crate off the rendering — the
//! root of the path, or of the trait half of `<Self as Trait>::m`, whose `DefId` is the
//! trait method's. That reading is sound only for a dump known to contain no
//! impersonating crate: a stand-in for the extractor in a test, never a decision
//! procedure. A key already present is left alone.

use trust_types::{CalleeKey, Terminator, VerifiableFunction};

pub fn rekey_pre_carrier_dump(mut func: VerifiableFunction) -> VerifiableFunction {
    for block in &mut func.body.blocks {
        let Terminator::Call { func: callee, callee_key, .. } = &mut block.terminator else {
            continue;
        };
        if callee_key.is_some() || callee.as_str() == trust_types::TRUST_INDIRECT_CALLEE_PATH {
            continue;
        }
        let path = match callee.strip_prefix('<') {
            Some(qualified) => qualified.split_once(" as ").map_or(qualified, |(_, t)| t),
            None => callee.as_str(),
        };
        let root = path.split("::").next().unwrap_or("").to_string();
        *callee_key = Some(CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot: matches!(root.as_str(), "core" | "alloc" | "std"),
            krate_name_is_ambiguous: false,
            stable_crate_id: 0x5157_5f52_4f4f_5421,
            krate_name: root,
            foreign_block_leaf: None,
            upstream_foreign_link_symbol: None,
            diverging_entry: None,
        });
    }
    func
}

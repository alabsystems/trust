//! Trust (2026-10-04, wave 13): the `callee_key` a hand-built unit-test `Call`
//! needs once a recognizer decides on the key (ASPTR-KEY-1, SLICE-INHERENT-1,
//! NUM-METHOD-ANCHOR-1).
//!
//! FIXTURE ONLY. It stands in for the extractor's `callee_key_for`, exactly as
//! `sep_engine::tests::fixture_key` does for the unsafe-mint tags; that helper
//! gives a key with `krate_is_real_sysroot: true` only to a spelling in its own
//! map, so a fixture calling `core::slice::<impl [u8]>::windows` or
//! `core::f64::<impl f64>::clamp` through it carries a NON-sysroot key and the
//! keyed recognizers (correctly) refuse it. The key below is what the real
//! extractor mints for a `core`/`std` callee with no modeled tag — measured on
//! `scratchpad/stage1-w11fix` (2026-10-04) for `core::slice::<impl [u8]>::windows`,
//! `core::f64::<impl f64>::clamp`, `std::f64::<impl f64>::sin` and
//! `<usize as core::convert::From<bool>>::from`: `sysroot_item: None`,
//! `krate_is_real_sysroot: true`, `krate_name_is_ambiguous: false`. Only the
//! residency bit is load-bearing for the recognizers that read it.

use trust_types::CalleeKey;

/// The key the extractor mints for a callee DEFINED in the real sysroot crate
/// `krate` (`core`, `alloc`, `std`) that carries no modeled tag.
pub(crate) fn sysroot_key(krate: &str) -> Option<CalleeKey> {
    Some(CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x5157_5f52_4f4f_5421,
        krate_name: krate.to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    })
}

/// The key the extractor mints for a USER crate's callee.
pub(crate) fn user_key(krate: &str) -> Option<CalleeKey> {
    sysroot_key(krate).map(|k| CalleeKey { krate_is_real_sysroot: false, ..k })
}

/// Give every keyless DIRECT call of a PRE-CARRIER dump — real MIR captured before
/// the extractor minted `callee_key` (e.g. `fixtures/a3d-geom-2026-07-18`, whose
/// `PROVENANCE.md` pins the bytes) — the residency key today's extractor mints:
/// `krate_is_real_sysroot` for a callee defined in `core`/`alloc`/`std`, a user key
/// otherwise. The defining crate is read off the rendering (the root of the path,
/// or of the trait half of a `<Self as Trait>::m` spelling, whose `DefId` is the
/// trait method's). That reading is sound only for a dump known to contain no
/// impersonating crate — a stand-in for the extractor in a test, never a decision
/// procedure; a key already present is left alone.
pub(crate) fn rekey_pre_carrier_dump(func: &mut trust_types::VerifiableFunction) {
    for block in &mut func.body.blocks {
        let trust_types::Terminator::Call { func: callee, callee_key, .. } = &mut block.terminator
        else {
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
        *callee_key = if matches!(root.as_str(), "core" | "alloc" | "std") {
            sysroot_key(&root)
        } else {
            user_key(&root)
        };
    }
}

#[test]
fn the_fixture_keys_are_what_the_extractor_mints() {
    // Captured from `-Ztrust-dump=mir` (see the module doc): the slice `windows`
    // call of `win_std` in `tests/fixtures/vcgen_recognizer_anchor/`.
    let func: trust_types::VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/slice_win_std_mir.json"
    ))
    .expect("fixture");
    let real = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            trust_types::Terminator::Call { func: callee, callee_key, .. }
                if callee == "core::slice::<impl [u8]>::windows" =>
            {
                callee_key.clone()
            }
            _ => None,
        })
        .expect("win_std calls core's windows with a key");
    let fixture = sysroot_key("core").expect("some");
    assert_eq!(real.sysroot_item, fixture.sysroot_item);
    assert_eq!(real.krate_is_real_sysroot, fixture.krate_is_real_sysroot);
    assert_eq!(real.krate_name_is_ambiguous, fixture.krate_name_is_ambiguous);
    assert_eq!(real.krate_name, fixture.krate_name);
    assert!(!user_key("mycrate").expect("some").krate_is_real_sysroot);
}

#[test]
fn rekeying_a_pre_carrier_dump_reads_the_defining_crate() {
    let mut func: trust_types::VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/vcgen_recognizer_anchor/slice_win_std_mir.json"
    ))
    .expect("fixture");
    let captured: Vec<Option<CalleeKey>> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            trust_types::Terminator::Call { callee_key, .. } => Some(callee_key.clone()),
            _ => None,
        })
        .collect();
    for block in &mut func.body.blocks {
        if let trust_types::Terminator::Call { callee_key, .. } = &mut block.terminator {
            *callee_key = None;
        }
    }
    rekey_pre_carrier_dump(&mut func);
    let rekeyed: Vec<Option<CalleeKey>> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            trust_types::Terminator::Call { callee_key, .. } => Some(callee_key.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(captured.len(), rekeyed.len());
    for (real, stand_in) in captured.iter().zip(&rekeyed) {
        let (real, stand_in) = (real.as_ref().expect("keyed"), stand_in.as_ref().expect("keyed"));
        assert_eq!(real.krate_is_real_sysroot, stand_in.krate_is_real_sysroot);
        assert_eq!(real.krate_name, stand_in.krate_name);
    }
}

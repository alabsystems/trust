// az_tuple_return_family — the RED pin for the (Dst, bool) TUPLE-RETURN leaf shape
// (Track B of the 2026-07-28 corpus-intake follow-up;
// reports/2026-07-28-corpus-intake-published-ladder.md §4.1 cause (b), re-derived as
// the committed fixture fixtures/az-tuple-return-2026-07-28/ — see its PROVENANCE.md).
//
// WHAT THIS PINS (the honest, measured state at commit time): the real, unmodified
// az 1.3.0 u16→u8 / i32→i16 delegation ladder — two `overflowing_cast` impl LEAVES
// (`_2 = _1 as Dst; _3 = _2 as Src; _4 = Ne(_1, _3); _0 = (_2, _4)`), their two
// monomorphized free-fn forwarders (observational w16-mono harvests, present so the
// diagnosis runs WITH callees), and two `.0`-projecting `wrapping_cast` callers —
// is 6/6 SHAPE_GAP: NO recognizer on EITHER lane accepts a two-element
// (scalar, bool) tuple return. Decline sites (file:line) are tabulated in the
// fixture's PROVENANCE.md.
//
// THIS TEST IS MEANT TO BE FLIPPED. When the trust-ir-side tuple-return lane lands
// (design of record: reports/2026-07-28-az-tuple-return-track-b.md), the LEAF rows
// flip to FULLY_FAITHFUL **via_trustir** and this pin must be rewritten to assert
// the green state — deliberately, in the same commit, with the lane split reported.
// Per the standing ruling, the flip must NOT come from a new MirSem-grounder
// recognizer: a leaf that certifies `mirsem_fallback` here is a wrong-lane landing,
// and the via_trustir assertions below are written to fail loudly on it.
//
// Run with:
//   cd crates && RUSTC_BOOTSTRAP=1 cargo test -p trust-clean \
//       --test az_tuple_return_family -- --test-threads=1 --nocapture

use std::collections::BTreeMap;
use std::path::Path;

use trust_clean::{diagnose_fully_faithful_gate_with_bodies, prove_dump_dir};
use trust_types::VerifiableFunction;

const LEAVES: [&str; 2] = [
    "az::int::<impl az::OverflowingCast<u8> for u16>::overflowing_cast",
    "az::int::<impl az::OverflowingCast<i16> for i32>::overflowing_cast",
];
const FORWARDERS: [&str; 2] =
    ["az::overflowing_cast::<u16, u8>", "az::overflowing_cast::<i32, i16>"];
const PROJECTING_CALLERS: [&str; 2] = [
    "az::int::<impl az::WrappingCast<u8> for u16>::wrapping_cast",
    "az::int::<impl az::WrappingCast<i16> for i32>::wrapping_cast",
];

fn read_family(dir: &Path) -> Vec<VerifiableFunction> {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .expect("fixture dumps dir")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("json"))
        .collect();
    entries.sort();
    entries
        .iter()
        .map(|p| {
            let bytes = std::fs::read(p).expect("read dump");
            trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(
                &bytes,
            )
            .expect("decode dump")
        })
        .collect()
}

#[test]
fn az_tuple_return_family_is_six_shape_gaps_with_callees_present() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/az-tuple-return-2026-07-28");
    let funcs = read_family(&dir.join("dumps"));
    assert_eq!(funcs.len(), 6, "all six family dumps must load");

    // Callees-first order + sibling-bodies map — EXACTLY the ff-gate/production
    // discipline (mirrors bin/ff-gate-diagnose-2026-07-10.rs), so a leaf that
    // certified would be registered before its forwarder/caller is diagnosed.
    let order = trust_vcgen::compute_verification_order(&trust_vcgen::build_call_graph(&funcs));
    let mut by_path: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, f) in funcs.iter().enumerate() {
        by_path.entry(f.def_path.as_str()).or_insert(i);
    }
    let mut seq: Vec<usize> = order.iter().filter_map(|p| by_path.get(p.as_str()).copied()).collect();
    for i in 0..funcs.len() {
        if !seq.contains(&i) {
            seq.push(i);
        }
    }
    let bodies: trust_clean::trustir_fold::DumpBodies = funcs
        .iter()
        .map(|f| (f.def_path.clone(), f.clone()))
        .collect();

    let mut certified: BTreeMap<String, trust_clean::mirsem::CalleeFact> = BTreeMap::new();
    let mut diagnosed: BTreeMap<String, trust_clean::FullyFaithfulDiagnosis> = BTreeMap::new();
    for i in seq {
        let func = &funcs[i];
        let diag = diagnose_fully_faithful_gate_with_bodies(func, &certified, &bodies);
        if diag.fully_faithful {
            certified
                .insert(func.def_path.clone(), trust_clean::mirsem::CalleeFact::of_certified(func));
        }
        diagnosed.insert(func.def_path.clone(), diag);
    }

    for group in [&LEAVES[..], &FORWARDERS[..], &PROJECTING_CALLERS[..]] {
        for def_path in group {
            let diag = diagnosed
                .get(*def_path)
                .unwrap_or_else(|| panic!("family row missing from fixture: {def_path}"));
            println!("{def_path}\n    {diag:?}");
            // THE RED PIN: no recognizer on either lane accepts the shape today.
            // If `via_ir_shape` flips true here, the tuple-return lane has landed —
            // rewrite this test to assert the green via_trustir state instead.
            assert!(
                !diag.fully_faithful && !diag.via_ir_shape && !diag.via_mirsem_shape,
                "{def_path}: expected SHAPE_GAP (the RED pin — see the test header for \
                 the deliberate flip protocol), got {diag:?}"
            );
            assert_eq!(diag.cluster_tag(), "SHAPE_GAP", "{def_path}");
        }
    }

    // WRONG-LANE GUARD (standing ruling): if any row certifies at all, it must be
    // via_trustir, never a new MirSem-grounder landing. Vacuous while RED.
    for (def_path, diag) in &diagnosed {
        assert!(
            !diag.via_mirsem,
            "{def_path}: a (Dst, bool) tuple-return row certified on the MirSem lane — \
             the standing ruling requires this shape to land trust-ir-side"
        );
    }
}

#[test]
fn az_tuple_return_family_production_scorecard_is_fail_closed() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/az-tuple-return-2026-07-28");
    let sc = prove_dump_dir(&dir.join("dumps")).expect("prove family dumps");
    println!(
        "az-tuple-return family: total={} inhabited={} fully_faithful={} (via_trustir={} \
         mirsem_fallback={}) kernel_rejected={}",
        sc.total,
        sc.inhabited,
        sc.fully_faithful,
        sc.fully_faithful_via_trustir,
        sc.fully_faithful_mirsem_fallback,
        sc.kernel_rejected
    );
    assert_eq!(sc.total, 6, "all six family dumps must load through the production gate");
    // Soundness invariant (must hold RED or GREEN): the kernel never rejects.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND: {:?}", sc.rejections);
    // THE RED PIN, production-gate edition. On the deliberate flip, update to the
    // measured green counts WITH the lane split (via_trustir only — see above).
    assert_eq!(
        sc.fully_faithful, 0,
        "the tuple-return lane has landed (or leaked): rewrite this RED pin to the \
         measured green state with its via_trustir lane split"
    );
}

// W-BITINTRIN — fail-closed acceptance evidence for the pure-total bit-intrinsic
// modeling (`intrinsics::{ctpop,cttz,ctlz,bswap,bitreverse}` as an opaque, total
// `call_result`). Mirrors the ascii/num harvest's forgery methodology: the
// genuine `count_ones` body certifies (kernel witness, modulo 3), while every
// adversarial mutation DECLINES — an exact but unmarked source-spellable path,
// a wrong-arity call, a non-total (`cttz_nonzero`) sibling, a foreign ABI, or an
// unmodeled intrinsic.
//
// Uses ONLY the public API (`PureTotalIntrinsic::classify`,
// `function_fully_faithful_witness_with_callees`, `diagnose_fully_faithful_gate`),
// so it exercises the same gate `prove_one_function` evaluates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::mirsem::{
    CalleeFact, PureTotalIntrinsic, function_fully_faithful_witness_with_callees,
};
use trust_types::{TRUST_RUSTC_INTRINSIC_PATH_PREFIX, VerifiableFunction};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/stdlib-leaf-num-2026-07-16")
}

fn load(rel: &str) -> VerifiableFunction {
    let bytes = std::fs::read(corpus_dir().join(rel)).expect("fixture present");
    serde_json::from_slice(&bytes).expect("fixture parses")
}

/// The STRICT classifier accepts EXACTLY the pinned total unary bit-intrinsics
/// at the canonical intrinsic paths, and NOTHING else.
#[test]
fn classify_accepts_only_pinned_total_intrinsics() {
    use PureTotalIntrinsic::*;
    let marked = |path: &str| format!("{TRUST_RUSTC_INTRINSIC_PATH_PREFIX}{path}");
    // Accept: compiler-marked truncated/core/std forms, generics stripped.
    for (path, want) in [
        ("intrinsics::ctpop::<u8>", Ctpop),
        ("intrinsics::cttz::<u8>", Cttz),
        ("core::intrinsics::ctlz::<u32>", Ctlz),
        ("std::intrinsics::bswap::<u16>", Bswap),
        ("intrinsics::bitreverse::<u64>", Bitreverse),
    ] {
        let path = marked(path);
        assert_eq!(PureTotalIntrinsic::classify(&path), Some(want), "must accept {path}");
    }

    // Decline (fail-closed): exact source-spellable intrinsic paths without the
    // compiler marker, forged wrapper crates, and bare names.
    for path in [
        "intrinsics::ctpop::<u8>",       // exact lookalike, but unmarked
        "core::intrinsics::cttz::<u8>",  // canonical text is still not authority
        "std::intrinsics::ctlz::<u32>",  // same for std-prefixed diagnostic text
        "evil::ctpop::<u8>",             // forged crate — no `intrinsics` segment
        "evil::intrinsics::ctpop::<u8>", // forged crate before `intrinsics`
        "a::intrinsics::ctpop::b",       // trailing junk segment (name != ctpop)
        "num::<impl u8>::count_ones",    // the Rust wrapper, not the intrinsic
        "ctpop",                         // bare name, no `intrinsics`
        "",                              // empty
    ] {
        assert_eq!(PureTotalIntrinsic::classify(path), None, "must DECLINE {path:?}");
    }

    // The marker prevents source-spellable DefPath collision under compiler
    // extraction; hand-edited JSON can forge it, so artifact authority remains
    // the authenticated compiler transport/session. Independently, the semantic
    // allowlist remains exact and rejects partial/effectful/malformed callees.
    for path in [
        "evil::intrinsics::ctpop::<u8>",
        "a::intrinsics::ctpop::b",
        "intrinsics::cttz_nonzero::<u8>",
        "intrinsics::ctlz_nonzero::<u8>",
        "intrinsics::unchecked_add::<u8>",
        "intrinsics::transmute::<u8, i8>",
        "intrinsics::write_bytes::<u8>",
    ] {
        let path = marked(path);
        assert_eq!(PureTotalIntrinsic::classify(&path), None, "must DECLINE {path:?}");
    }
}

/// All modeled bit-intrinsics are UNARY.
#[test]
fn classify_pinned_intrinsics_are_unary() {
    for k in [
        PureTotalIntrinsic::Ctpop,
        PureTotalIntrinsic::Cttz,
        PureTotalIntrinsic::Ctlz,
        PureTotalIntrinsic::Bswap,
        PureTotalIntrinsic::Bitreverse,
    ] {
        assert_eq!(k.arity(), 1);
    }
}

/// POSITIVE CONTROL — the genuine `count_ones`/`trailing_zeros` bodies certify a
/// whole-function faithfulness witness that is modulo 3 (the KERNEL accepted the
/// opaque-`call_result` return, not a shape-only promotion).
#[test]
fn genuine_bit_intrinsic_leaves_certify_modulo_3() {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for rel in [
        "dumps/num__<impl u8>__count_ones.json",
        "dumps/num__<impl u8>__trailing_zeros.json",
        "dumps/num__<impl u16>__count_ones.json",
        "dumps/num__<impl u64>__trailing_zeros.json",
    ] {
        let f = load(rel);
        let wit = function_fully_faithful_witness_with_callees(&f, &empty);
        assert!(
            wit.as_ref().is_some_and(|c| c.is_modulo_3()),
            "{rel}: genuine pure-total intrinsic leaf must certify modulo 3 (kernel witness)"
        );
    }
}

/// FAIL-CLOSED FORGERY PANEL — each adversarial mutation of the genuine
/// `count_ones` body MUST decline the fully-faithful witness (never certified),
/// AND the production diagnose gate must NOT call it fully faithful.
#[test]
fn bit_intrinsic_forgeries_all_decline() {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for rel in [
        "forgeries/forgery__B1_fake_ctpop_defpath.json", // exact ctpop text, no marker
        "forgeries/forgery__B2_wrong_arity_ctpop.json",  // ctpop with 2 args
        "forgeries/forgery__B3_nontotal_cttz_nonzero.json", // PARTIAL cttz_nonzero
        "forgeries/forgery__B4_foreign_ctpop.json",      // foreign ABI
        "forgeries/forgery__B5_unmodeled_intrinsic_transmute.json", // transmute
    ] {
        let f = load(rel);
        assert!(
            function_fully_faithful_witness_with_callees(&f, &empty).is_none(),
            "{rel}: forgery must DECLINE the fully-faithful witness (fail-closed)"
        );
        let diag = trust_clean::diagnose_fully_faithful_gate(&f, &empty);
        assert!(!diag.fully_faithful, "{rel}: forgery must not be fully faithful");
    }
}

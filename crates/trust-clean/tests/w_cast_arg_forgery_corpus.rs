// W-CAST-ARG — fail-closed acceptance evidence for the SIGNED bit-method delegate
// modeling: the signed `leading_zeros`/`swap_bytes`/`reverse_bits` leaves delegate
// to their UNSIGNED PRIMARY on the SAME bit pattern —
//   num::<impl i8>::leading_zeros = `_2 := self as u8; _0 := <impl u8>::leading_zeros(_2)`
//   num::<impl i8>::swap_bytes    = `_2 := self as u8; _3 := <impl u8>::swap_bytes(_2); _0 := _3 as i8`
// The cast-INTO-arg (`iN as uN`) is a SAME-WIDTH signedness reinterpret (a pure bit
// reinterpret); the cast-ON-result (`uN as iN`) recovers the signed value. Both are
// modeled by the OPAQUE `idx_elem` cast carrier, so the delegate certifies FULLY
// FAITHFUL modulo 3 WITHOUT a value theory.
//
// THE SHARP SOUNDNESS GATE — SAME WIDTH ONLY. `leading_zeros`/`ctlz` is
// WIDTH-SENSITIVE (`ctlz(x as u64) != ctlz(x as u8)` for the same logical value), so
// the delegation is bit-faithful ONLY when the cast preserves the WIDTH. A
// DIFFERENT-width cast into the argument (even to the matching-width primary) MUST
// DECLINE — the forgery panel below confirms each adversarial mutation declines the
// recognizer (never a false witness; the kernel is never handed a wrong claim).
//
// Uses ONLY the public API (`function_fully_faithful_witness_with_callees`,
// `diagnose_fully_faithful_gate`, `CalleeFact`), so it exercises the same gate
// `prove_one_function` evaluates. Mirrors `bitintrin_forgery_corpus.rs`'s methodology.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::mirsem::{CalleeFact, function_fully_faithful_witness_with_callees};
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/stdlib-leaf-bitmethods-2026-07-16")
}

fn load(rel: &str) -> VerifiableFunction {
    let bytes = std::fs::read(corpus_dir().join(rel)).expect("fixture present");
    serde_json::from_slice(&bytes).expect("fixture parses")
}

fn load_value(rel: &str) -> serde_json::Value {
    let bytes = std::fs::read(corpus_dir().join(rel)).expect("fixture present");
    serde_json::from_slice(&bytes).expect("fixture parses")
}

/// The 12 UNSIGNED-primary certified callees (`{leading_zeros,swap_bytes,
/// reverse_bits}` over `{u8,u16,u32,u64}`), each a W-BITINTRIN leaf certified
/// against the empty registry, folded into a `CalleeFact` registry keyed by
/// def-path — exactly the callees-first registry the production ff-gate builds.
fn unsigned_primary_registry() -> BTreeMap<String, CalleeFact> {
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    let mut reg = BTreeMap::new();
    for width in ["u8", "u16", "u32", "u64"] {
        for method in ["leading_zeros", "swap_bytes", "reverse_bits"] {
            let rel = format!("dumps/num__<impl {width}>__{method}.json");
            let f = load(&rel);
            let wit = function_fully_faithful_witness_with_callees(&f, &empty);
            assert!(
                wit.as_ref().is_some_and(|c| c.is_modulo_3()),
                "{rel}: the unsigned PRIMARY must certify modulo 3 (kernel witness)"
            );
            reg.insert(f.def_path.clone(), CalleeFact::of_certified(&f));
        }
    }
    reg
}

/// POSITIVE CONTROL — every one of the 12 SIGNED delegates (`{leading_zeros,
/// swap_bytes,reverse_bits}` over `{i8,i16,i32,i64}`) certifies a whole-function
/// faithfulness witness that is modulo 3 (the KERNEL accepted the opaque cast-arg /
/// cast-on-result carrier composed with the certified unsigned primary — NOT a
/// shape-only promotion), AND the production diagnose gate calls it fully faithful.
#[test]
fn signed_bit_method_delegates_certify_modulo_3() {
    let reg = unsigned_primary_registry();
    let mut flipped = 0usize;
    for width in ["i8", "i16", "i32", "i64"] {
        for method in ["leading_zeros", "swap_bytes", "reverse_bits"] {
            let rel = format!("dumps/num__<impl {width}>__{method}.json");
            let f = load(&rel);
            let wit = function_fully_faithful_witness_with_callees(&f, &reg);
            assert!(
                wit.as_ref().is_some_and(|c| c.is_modulo_3()),
                "{rel}: the signed delegate must certify modulo 3 (kernel witness)"
            );
            let diag = trust_clean::diagnose_fully_faithful_gate(&f, &reg);
            assert!(diag.fully_faithful, "{rel}: signed delegate must be fully faithful");
            flipped += 1;
        }
    }
    assert_eq!(flipped, 12, "all 12 signed bit-method delegate rows must flip");
}

/// Mutate the block's sole cast assignment so its destination integer becomes
/// `(width, signed)`. Returns the mutated function.
fn mutate_cast_dest_ty(mut v: serde_json::Value, block: usize, width: u64, signed: bool) -> VerifiableFunction {
    let stmts = v["body"]["blocks"][block]["stmts"].as_array_mut().expect("stmts");
    let assign = stmts
        .iter_mut()
        .find_map(|s| s.get_mut("Assign").filter(|a| a["rvalue"].get("Cast").is_some()))
        .expect("a Cast assignment in this block");
    let destination = assign["place"]["local"].as_u64().expect("destination local") as usize;
    let cast = assign["rvalue"]["Cast"].as_array_mut().expect("Cast tuple");
    cast[1] = serde_json::json!({ "Int": { "width": width, "signed": signed } });
    let replacement = serde_json::json!({ "Int": { "width": width, "signed": signed } });
    let local = v["body"]["locals"]
        .as_array_mut()
        .expect("locals")
        .iter_mut()
        .find(|local| local["index"].as_u64() == Some(destination as u64))
        .expect("declared destination local");
    local["ty"] = replacement.clone();
    if destination == 0 {
        v["body"]["return_ty"] = replacement;
    }
    serde_json::from_value(v).expect("mutated fn parses")
}

fn set_callee(mut v: serde_json::Value, block: usize, callee: &str) -> VerifiableFunction {
    v["body"]["blocks"][block]["terminator"]["Call"]["func"] = serde_json::json!(callee);
    serde_json::from_value(v).expect("mutated fn parses")
}

/// FAIL-CLOSED FORGERY PANEL — each adversarial mutation of a GENUINE signed
/// delegate MUST DECLINE the fully-faithful witness (never certified) AND the
/// production diagnose gate must NOT call it fully faithful. Because each declines
/// at the RECOGNIZER, the kernel is never handed a wrong claim (kernel_rejected
/// stays 0 by construction — no false witness is ever minted).
#[test]
fn w_cast_arg_forgeries_all_decline() {
    let reg = unsigned_primary_registry();

    // The genuine controls (must certify) so a decline below is the MUTATION's doing.
    for rel in ["dumps/num__<impl i8>__leading_zeros.json", "dumps/num__<impl i8>__swap_bytes.json"] {
        let f = load(rel);
        assert!(
            function_fully_faithful_witness_with_callees(&f, &reg)
                .is_some_and(|c| c.is_modulo_3()),
            "{rel}: genuine control must certify (else the forgery test is vacuous)"
        );
    }

    let lz = "dumps/num__<impl i8>__leading_zeros.json";
    let sb = "dumps/num__<impl i8>__swap_bytes.json";

    // F1 — DIFFERENT-WIDTH cast into arg (`self as u16` fed to the u8 primary): the
    // width-sensitivity gate declines — the same bit pattern no longer reaches the
    // same-width callee.
    let f1 = mutate_cast_dest_ty(load_value(lz), 0, 16, false);
    // F2 — SELF-RECURSIVE callee (`num::<impl i8>::leading_zeros`): the self-call
    // guard declines (a callee's certificate cannot precede the caller's own).
    let f2 = set_callee(load_value(lz), 0, "num::<impl i8>::leading_zeros");
    // F3 — non-bit-preserving SAME-SIGN WIDENING cast (`self as i16`): opposite-
    // signedness is required AND same width — a widening sign-extend declines.
    let f3 = mutate_cast_dest_ty(load_value(lz), 0, 16, true);
    // F4 — THE SHARP PROBE: a DIFFERENT-width cast (`self as u16`) fed to the
    // MATCHING-width certified primary (`num::<impl u16>::leading_zeros`, which IS
    // in the registry). This is a genuinely WRONG delegation (`ctlz` on 16 bits, not
    // 8) that must STILL decline — the width gate refuses it before the callee
    // resolution ever matters.
    let f4 = {
        let v = load_value(lz);
        let v = set_callee(v, 0, "num::<impl u16>::leading_zeros");
        // set_callee returned a VerifiableFunction; re-serialize to mutate the cast.
        let vv = serde_json::to_value(&v).expect("reserialize");
        mutate_cast_dest_ty(vv, 0, 16, false)
    };
    // F5 — DIFFERENT-WIDTH cast ON RESULT (`_3 as i16` instead of `_3 as i8`): the
    // call-then-cast result-recovery arm's width gate declines.
    let f5 = mutate_cast_dest_ty(load_value(sb), 1, 16, true);

    for (name, f) in [
        ("F1 different-width cast into arg", f1),
        ("F2 self-recursive callee", f2),
        ("F3 same-sign widening cast into arg", f3),
        ("F4 different-width cast into MATCHING-width primary", f4),
        ("F5 different-width cast on result", f5),
    ] {
        assert!(
            function_fully_faithful_witness_with_callees(&f, &reg).is_none(),
            "{name}: forgery must DECLINE the fully-faithful witness (fail-closed)"
        );
        let diag = trust_clean::diagnose_fully_faithful_gate(&f, &reg);
        assert!(!diag.fully_faithful, "{name}: forgery must not be fully faithful");
    }
}

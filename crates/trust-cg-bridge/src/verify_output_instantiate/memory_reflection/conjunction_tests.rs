use super::*;
use crate::verify_output::{ProvenEvidence, try_kernel_recheckable_original_conjunction};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn v(name: &str, width: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(width))
}
fn c(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}
fn mem(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))))
}
fn read(m: Formula, q: Formula) -> Formula {
    Formula::Select(b(m), b(q))
}
fn store(m: Formula, a: Formula, value: Formula) -> Formula {
    Formula::Store(b(m), b(a), b(value))
}
fn low(f: Formula, high: u32) -> Formula {
    Formula::BvExtract { inner: b(f), high, low: 0 }
}
fn zext(f: Formula, extra: u32) -> Formula {
    Formula::BvZeroExt(b(f), extra)
}
fn add0(f: Formula) -> Formula {
    Formula::BvAdd(b(f), b(c(0, 64)), 64)
}
fn items() -> Vec<(Formula, Formula)> {
    let q = v("CER_LEAF_QUERY@object:function", 64);
    let exit = store(mem("M0"), v("X0", 64), low(v("X1", 64), 7));
    vec![
        (v("X19", 64), v("X19", 64)),
        (v("SP", 64), v("SP", 64)),
        (c(0, 64), c(0, 64)),
        (read(exit.clone(), q.clone()), read(exit, q)),
    ]
}
fn proved(items: &[(Formula, Formula)]) -> bool {
    matches!(
        try_kernel_recheckable_original_conjunction(items),
        Some(ProvenEvidence::KernelInstantiated { .. })
    )
}
/// Whether the bit-level reflection builds a proof of `machine = source`, in
/// the conjunction's context. It compares both sides' normalized bits and
/// declines a mismatch, so a false member never reaches the kernel by this
/// route. (`reflect`, the fallback, has no `Ite` arm.)
fn bit_equation(machine: &Formula, source: &Formula) -> bool {
    let mut context =
        Context { exact_byte_arrays: true, compact_original: true, ..Context::default() };
    scalar_bits::equation(machine, source, &mut context).is_some()
}

#[test]
fn original_not_preserves_movn_signed_return_and_memory() {
    for width in [8, 16] {
        // Actual O0 MOVN W0,#6; SXTB/SXTH X1,W0; MOV W0,W1.
        // Every cast remains in the original statement checked by the kernel.
        let movn = zext(Formula::BvNot(b(c(6, 32)), 32), 32);
        let signed = Formula::BvSignExt(b(low(movn, width - 1)), 64 - width);
        let physical = low(zext(low(signed, 31), 32), 31);
        let expected = Formula::BvSignExt(b(c(-7, width)), 32 - width);
        let mut all = items();
        all.push((physical.clone(), expected));
        assert!(proved(&all), "actual signed MOVN width {width}");
        all.last_mut().unwrap().1 = c(249, 32);
        assert!(!proved(&all), "zero padding cannot replace physical sign padding");
        all.last_mut().unwrap().1 = c(-6, 32);
        assert!(!proved(&all), "changed MOVN literal cannot retain a proof");
    }
}

#[test]
fn original_not_checks_width_and_retains_the_operation() {
    let value = v("not_input", 64);
    let not = Formula::BvNot(b(value.clone()), 64);
    let mut all = items();
    all.push((not.clone(), not.clone()));
    assert!(proved(&all));
    all.last_mut().unwrap().1 = value;
    assert!(!proved(&all), "complement is not an identity");
    assert!(proved(&[(Formula::BvNot(b(c(i128::MIN, 128)), 128), c(i128::MAX, 128))]));
    for bad in [
        Formula::BvNot(b(v("bad_not", 8)), 16),
        Formula::BvNot(b(v("empty_not", 0)), 0),
        Formula::BvNot(b(v("wide_not", 129)), 129),
    ] {
        assert!(!proved(&[(bad.clone(), bad)]));
    }
}

#[test]
fn actual_signed_o0_original_equations_fit_existing_packet_and_kernel_bounds() {
    for data in [
        include_bytes!("../../../tests/fixtures/signed_o0_original/original-8.json").as_slice(),
        include_bytes!("../../../tests/fixtures/signed_o0_original/original-16.json").as_slice(),
    ] {
        let original: Vec<(Formula, Formula)> = serde_json::from_slice(data).unwrap();
        assert_eq!(original.len(), 24);
        let prepared = prepare_conjunction(&original).expect("actual original formulas reflect");
        crate::original_conjunction_certificate::check_produced(
            &original,
            &prepared.goal,
            &prepared.proof,
        )
        .expect("actual original conjunction retains and kernel-checks");
    }
}

#[test]
fn actual_signed_o0_capture_closes_two_stores_and_replays_without_producer() {
    use crate::call_event::{replay_original_certificates, verify_compiled_module};
    use crate::compiler_input_capture::CompilerInputCapture;
    use crate::object_replay::artifact_digest;
    let data = include_bytes!("../../../tests/fixtures/signed_o0_original/compiler-input.json");
    let object = include_bytes!("../../../tests/fixtures/signed_o0_original/compiler-output.o");
    assert_eq!(
        artifact_digest(data),
        "8b0fea9f81e69a36adab955bcb2bb3ad158aaaf1ebe63c20439da1944199f104"
    );
    assert_eq!(
        artifact_digest(object),
        "6f730f51bd83601d193a141525e57bc57524eb4ca3f3a8d4e8c5ba543eb44742"
    );
    let decoded = CompilerInputCapture::from_bytes(data).unwrap().decode_inputs().unwrap();
    assert_eq!(decoded.object, object);
    assert_eq!(decoded.m_cg.functions.iter().filter(|f| !f.blocks.is_empty()).count(), 8);
    let report = verify_compiled_module(&decoded.input()).unwrap();
    assert_eq!(report.certificates.len(), 8);
    for name in ["trust_c_i8_store", "trust_c_i16_store"] {
        let row = report.certificate(name).unwrap();
        assert!(
            row.is_kernel_proved() && row.original_proof.is_some(),
            "{name}: {:?}",
            row.leaf_memory
        );
    }
    assert_eq!(report.closure.closed_kernel.len(), 8);
    let sidecar = report.to_json();
    let replay = crate::original_conjunction_certificate::without_production(|| {
        replay_original_certificates(&decoded.input(), sidecar.as_bytes())
    })
    .unwrap();
    assert_eq!(replay.rows.len(), 8, "complete function denominator is retained");
    for name in ["trust_c_i8_store", "trust_c_i16_store"] {
        assert!(replay.rows.iter().find(|r| r.symbol == name).unwrap().replayed);
    }
    // Neither a proof from the other signed function nor an old proof on new
    // object bytes can stand in for this exact function's original theorem.
    let mut substituted: serde_json::Value = serde_json::from_str(&sidecar).unwrap();
    let rows = substituted["certificates"].as_array_mut().unwrap();
    let left = rows.iter().position(|r| r["symbol"] == "trust_c_i8_store").unwrap();
    let right = rows.iter().position(|r| r["symbol"] == "trust_c_i16_store").unwrap();
    let old = rows[left]["original_proof"].clone();
    rows[left]["original_proof"] = rows[right]["original_proof"].clone();
    rows[right]["original_proof"] = old;
    let substituted = serde_json::to_vec(&substituted).unwrap();
    let rejected = crate::original_conjunction_certificate::without_production(|| {
        replay_original_certificates(&decoded.input(), &substituted)
    });
    if let Ok(rejected) = rejected {
        assert_eq!(rejected.rows.len(), 8);
        for name in ["trust_c_i8_store", "trust_c_i16_store"] {
            assert!(!rejected.rows.iter().find(|r| r.symbol == name).unwrap().replayed);
        }
    }
    let object = crate::compiled_object::CompiledObject::parse(&decoded.object).unwrap();
    let text = &object.sections.iter().find(|s| s.name == "__TEXT,__text").unwrap().bytes;
    let text_offset = decoded.object.windows(text.len()).position(|b| b == text).unwrap();
    assert_eq!(decoded.object.windows(text.len()).filter(|b| *b == text.as_slice()).count(), 1);
    let start = report.certificate("trust_c_i8_store").unwrap().extent.0 as usize;
    for (offset, original, replacement) in
        [(start + 4, 0x39000002u32, 0xd503201fu32), (start + 8, 0x128000c0u32, 0x128000e0u32)]
    {
        let mut changed = decoded.object.clone();
        let at = text_offset + offset;
        assert_eq!(u32::from_le_bytes(changed[at..at + 4].try_into().unwrap()), original);
        changed[at..at + 4].copy_from_slice(&replacement.to_le_bytes());
        let input = crate::call_event::CerInput { object: &changed, ..decoded.input() };
        let bad = verify_compiled_module(&input).unwrap();
        assert_eq!(bad.certificates.len(), 8);
        assert!(matches!(
            bad.certificate("trust_c_i8_store").unwrap().verdict,
            crate::verify_output::OutputVerdict::Unknown { .. }
        ));
        assert!(bad.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_err());
        assert!(
            crate::original_conjunction_certificate::without_production(|| {
                replay_original_certificates(&input, sidecar.as_bytes())
            })
            .is_err()
        );
    }
    if let Some(out) = std::env::var_os("TRUST_SIGNED_O0_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("certificates.json"), &sidecar).unwrap();
        std::fs::write(out.join("fresh-replay.json"), serde_json::to_vec_pretty(&replay).unwrap())
            .unwrap();
    }
}

#[test]
fn mixed_scalar_and_original_memory_kernel_conjunction() {
    assert!(proved(&items()));
    let one = items().pop().unwrap();
    assert!(proved(&[one]));
}

#[test]
fn mixed_checked_store_children_and_address_coverage() {
    let p = v("X0", 64);
    let byte = low(v("X1", 64), 7);
    let q = v("CER_LEAF_QUERY@store", 64);
    let machine = store(mem("M0"), add0(p.clone()), low(zext(byte.clone(), 56), 7));
    let source = store(mem("M0"), p.clone(), byte);
    let mut all = items();
    all.pop();
    all.push((add0(p.clone()), p));
    all.push((read(machine, q.clone()), read(source, q)));
    assert!(
        discharge(&all[3].0, &all[3].1).is_none(),
        "new address identity belongs to the joint route"
    );
    assert!(
        discharge(&all[4].0, &all[4].1).is_none(),
        "legacy single route retains original Store children"
    );
    assert!(
        proved(&all),
        "right-zero and Store child transports must be checked in the original joint goal"
    );
}

#[test]
fn mixed_copy_load_readouts_preserve_byte_width() {
    let p = v("X0", 64);
    let q = v("fresh_copy_query", 64);
    let value = read(mem("M0"), v("X1", 64));
    let wrapped = low(zext(value.clone(), 56), 7);
    assert!(
        discharge(&zext(wrapped.clone(), 56), &zext(value.clone(), 56)).is_none(),
        "legacy opaque-list readout cannot borrow the new exact-byte joint context"
    );
    let mut all = items();
    all.pop();
    all.push((zext(wrapped.clone(), 56), zext(value.clone(), 56)));
    all.push((
        read(store(mem("M0"), p.clone(), wrapped), q.clone()),
        read(store(mem("M0"), p, value), q),
    ));
    assert!(proved(&all), "all byte-array outputs retain eight unconstrained bits");
}

#[test]
fn mixed_false_or_unreflectable_member_refuses_whole_goal() {
    assert!(try_kernel_recheckable_original_conjunction(&[]).is_none());
    let original = items();
    for index in 0..original.len() {
        let mut bad = original.clone();
        bad[index] = (c(0, 64), c(1, 64));
        assert!(!proved(&bad));
    }
    // A reflected `Ite` is held to its value. Each condition below picks one
    // symbolic arm: the equation naming that arm proves, and the same `Ite`
    // equated to the other arm is false and refuses the whole goal. The
    // conditions include symbolic `Eq`s, the shape production's `Ite`s carry
    // (the C small-scalar domain laws in abi_extensions). The kernel's goal is
    // rendered by the same bit renderer, so only these cases catch a renderer
    // that misreads an `Eq` condition (measured 2026-11-06 by the hostile
    // review: with `bool_bits` rendering every `Eq` as true, the constant
    // conditions alone, the lib suite and source_c_u8_abi all stayed green).
    // The decided constant pairs differ in bit 0, in bit 3 alone and in bit 7
    // alone, so a renderer that compares only some of an `Eq`'s bits fails too.
    let (x, y) = (v("ix", 64), v("iy", 64));
    let (ea, eb) = (v("ea", 8), v("eb", 8));
    let eq = |l: &Formula, r: &Formula| Formula::Eq(b(l.clone()), b(r.clone()));
    let ite = |condition: &Formula| Formula::Ite(b(condition.clone()), b(x.clone()), b(y.clone()));
    let flag = |condition: &Formula| Formula::Ite(b(condition.clone()), b(c(1, 1)), b(c(0, 1)));
    for (condition, picked, other) in [
        (Formula::Bool(true), &x, &y),
        (Formula::Bool(false), &y, &x),
        (Formula::Not(b(Formula::Bool(false))), &x, &y),
        (eq(&ea, &ea), &x, &y),
        (Formula::Not(b(eq(&ea, &ea))), &y, &x),
        (eq(&c(5, 8), &c(5, 8)), &x, &y),
        (eq(&c(5, 8), &c(6, 8)), &y, &x),
        (eq(&c(0x01, 8), &c(0x09, 8)), &y, &x),
        (eq(&c(0x01, 8), &c(0x81, 8)), &y, &x),
    ] {
        let mut good = original.clone();
        good.push((ite(&condition), picked.clone()));
        assert!(proved(&good), "{condition:?} picks its arm");
        assert!(bit_equation(&ite(&condition), picked), "{condition:?}: the bit route proves it");
        let mut bad = original.clone();
        bad.push((ite(&condition), other.clone()));
        assert!(!proved(&bad), "{condition:?} does not pick the other arm");
        assert!(
            !bit_equation(&ite(&condition), other),
            "{condition:?}: the false member is declined before the kernel"
        );
    }
    // `ea = eb` decides neither arm, so neither equation holds, and its 0/1
    // flag is neither constant. The last two pairs are false domain laws: a
    // true flag equated to the flag of a false `Eq`, which differs in bit 0
    // and in bit 7 alone.
    for false_member in [
        (ite(&eq(&ea, &eb)), x.clone()),
        (ite(&eq(&ea, &eb)), y.clone()),
        (flag(&eq(&ea, &eb)), c(1, 1)),
        (flag(&eq(&ea, &eb)), c(0, 1)),
        (flag(&eq(&ea, &ea)), flag(&eq(&c(0, 8), &c(1, 8)))),
        (flag(&eq(&ea, &ea)), flag(&eq(&c(0x01, 8), &c(0x81, 8)))),
    ] {
        let mut bad = original.clone();
        bad.push(false_member.clone());
        assert!(!proved(&bad), "{false_member:?} is false");
        assert!(
            !bit_equation(&false_member.0, &false_member.1),
            "{false_member:?}: declined before the kernel"
        );
    }
    // A true member whose condition stays symbolic: `Eq` is symmetric bit by
    // bit, and a true domain law.
    for true_member in [
        (ite(&eq(&ea, &eb)), ite(&eq(&eb, &ea))),
        (flag(&eq(&ea, &ea)), flag(&eq(&c(1, 8), &c(1, 8)))),
    ] {
        let mut good = original.clone();
        good.push(true_member.clone());
        assert!(proved(&good), "{true_member:?} holds");
        assert!(
            bit_equation(&true_member.0, &true_member.1),
            "{true_member:?}: the bit route proves it"
        );
    }
    let same = Formula::Ite(b(Formula::Bool(true)), b(v("opaque", 64)), b(v("opaque", 64)));
    let mut same_arms = original.clone();
    same_arms.push((same.clone(), v("opaque", 64)));
    assert!(proved(&same_arms));
    assert!(bit_equation(&same, &v("opaque", 64)), "the bit route proves equal arms");
    let q = v("CER_LEAF_QUERY@object:function", 64);
    for changed in [
        read(mem("M0"), q.clone()),
        read(store(mem("other_M0"), v("X0", 64), low(v("X1", 64), 7)), q.clone()),
        read(store(mem("M0"), v("X0", 64), v("changed_byte", 8)), q.clone()),
        read(store(mem("M0"), v("wrong_address", 64), low(v("X1", 64), 7)), q.clone()),
        read(store(mem("M0"), v("X0", 64), low(v("X1", 64), 7)), v("different_query", 64)),
        read(
            store(mem("M0"), v("X0", 64), low(v("X1", 64), 7)),
            Formula::BvAnd(b(q), b(c(i128::from(u64::MAX >> 1), 64)), 64),
        ),
    ] {
        let mut bad = original.clone();
        bad.last_mut().unwrap().1 = changed;
        assert!(!proved(&bad));
    }
    for bad_pair in [
        (v("badwidth", 8), v("badwidth", 16)),
        (Formula::Var("bool".into(), Sort::Bool), Formula::Var("bool".into(), Sort::Bool)),
        (read(mem("M0"), v("short_query", 63)), c(0, 8)),
        (read(store(mem("M0"), v("X0", 64), v("wide_byte", 16)), v("query", 64)), c(0, 8)),
        (low(v("narrow", 8), 8), c(0, 9)),
        (Formula::BvAdd(b(v("short", 8)), b(c(0, 8)), 64), c(0, 64)),
        // A free Bool condition has no bit reflection, so this true,
        // well-sorted `Ite` is outside the fragment.
        (
            Formula::Ite(
                b(Formula::Var("pick".into(), Sort::Bool)),
                b(v("opaque", 64)),
                b(v("opaque", 64)),
            ),
            v("opaque", 64),
        ),
        // An `Ite` whose arms differ in width is ill-sorted.
        (
            Formula::Ite(b(Formula::Bool(true)), b(v("opaque", 64)), b(v("opaque8", 8))),
            v("opaque", 64),
        ),
        (
            Formula::BvConcat(b(v("hi", 8)), b(v("lo", 8))),
            Formula::BvConcat(b(v("lo", 8)), b(v("hi", 8))),
        ),
    ] {
        let mut bad = original.clone();
        bad.push(bad_pair);
        assert!(!proved(&bad));
    }
    let mut malformed = original.clone();
    malformed
        .extend([(v("same_name", 8), v("same_name", 8)), (v("same_name", 16), v("same_name", 16))]);
    assert!(!proved(&malformed));
    let wrong = Formula::Var(
        "M32".into(),
        Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
    );
    let mut bad = original;
    let read_wrong = read(wrong, v("address", 64));
    bad.push((read_wrong.clone(), read_wrong));
    assert!(!proved(&bad));
}

#[test]
fn mixed_names_full_query_bits_and_hostile_substitution() {
    let mut all = items();
    all.push((v("a.bé", 8), v("a.bé", 8)));
    all.push((v("a..be\u{301}", 8), v("a..be\u{301}", 8)));
    assert!(proved(&all));
    let prepared = prepare_conjunction(&all).unwrap();
    let key = format!("M8_w64_x{}", encoded("CER_LEAF_QUERY@object:function"));
    assert_eq!(prepared.context.bits.iter().filter(|n| n.contains(&key)).count(), 64);
    assert_eq!(prepared.context.memories.len(), 8);
    let mut bad = all;
    bad[1] = (c(0, 64), c(1, 64));
    let changed = prepare_conjunction(&bad).unwrap();
    assert!(
        run_recheck_thread("trust-m8-hostile-joint-goal", move || {
            let env = context_env(&changed.context).unwrap();
            clean_kernel::TypeChecker::with_mode(&env, env.mode())
                .check_type(&prepared.proof, &changed.goal)
                .is_err()
        })
        .unwrap(),
        "a valid joint proof cannot be substituted for a changed original goal"
    );
    let a = read(mem("m.a"), v("p", 64));
    let b = read(mem("m..a"), v("p", 64));
    let mut collision = items();
    collision.push((a, b));
    assert!(!proved(&collision));
}

#[test]
fn mixed_evidence_binds_ordered_inputs_and_joint_goal() {
    let original = items();
    let mut reordered = original.clone();
    reordered.reverse();
    let label = |xs: &[(Formula, Formula)]| match try_kernel_recheckable_original_conjunction(xs)
        .unwrap()
    {
        ProvenEvidence::KernelInstantiated { theorem, .. } => theorem,
        _ => panic!("original conjunction grade"),
    };
    let first = label(&original);
    let second = label(&reordered);
    assert_ne!(first, second);
    assert!(
        first.contains("inputs-sha256=")
            && first.contains("goal-sha256=")
            && first.contains("proof-sha256=")
    );
}

#[test]
fn mixed_actual_leaf_exports_keep_unmodified_original_equations() {
    for input in [
        include_str!("fixtures/leaf_store.json"),
        include_str!("fixtures/leaf_load.json"),
        include_str!("fixtures/leaf_copy.json"),
        include_str!("fixtures/leaf_gep.json"),
    ] {
        let fixture: serde_json::Value = serde_json::from_str(input).unwrap();
        let equations: Vec<(Formula, Formula)> =
            serde_json::from_value(fixture["equations"].clone()).unwrap();
        assert!(
            proved(&equations),
            "actual compiler/executor original equations: {}",
            fixture["binding"]
        );
    }
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/leaf_store_wide.json")).unwrap();
    let equations: Vec<(Formula, Formula)> =
        serde_json::from_value(fixture["equations"].clone()).unwrap();
    assert!(
        !proved(&equations),
        "unsupported high-offset extract must decline the whole actual eight-byte goal"
    );
}

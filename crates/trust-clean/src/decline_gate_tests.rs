//! DECLINE IS NOT DISCHARGE — the regression pins for the two false-proof channels
//! closed by `mirsem::function_has_open_declined_vc`.
//!
//! Every fixture here is a REAL `-Ztrust-dump=mir:` extraction (stage2 `trustc`) whose
//! runtime behaviour was measured by a stock-rustc oracle before any claim was made
//! about it — `fixtures/decline-handling-2026-08-25/{sources,oracle_rows.txt}`. The
//! panicking rows panic; the control rows do not panic within their declared
//! preconditions. That is what entitles this file to call a `Certified` verdict on one
//! of them a FALSE PROOF rather than a precision question.
//!
//! CHANNEL 1 — a `Bool(false)` violation formula "discharges". The slice-range emitter
//! built its declined row with `Formula::Bool(false)`; `whole_program`'s certification
//! loops select by `proof_level() == L0Safety` (which `UnsupportedMir` satisfies) and
//! read `RefutedModulo3` as discharged. `Bool(false)` is UNSAT, so the DECLINED row
//! discharged and `vec_range_index_with_ensures` reached `ProofStatus::Certified` /
//! `is_assumable == true` — assumption authority for every caller.
//!
//! CHANNEL 2 — an EMPTY safety-VC set reads as vacuously discharged. `is_safety_vc_kind`
//! does not name `UnsupportedMir`, so a body whose only obligation is a decline produced
//! an EMPTY filtered set, and `function_safety_vcs_all_discharged` returns `true` on
//! empty. The compensating gate `function_emits_unmodeled_safety_vc` applied the SAME
//! filter first, so it could not catch it. Channel 2 is independent of Channel 1:
//! `p3_map_index`'s declined row already carried the correct `Bool(true)` polarity and
//! the gate passed it anyway.
//!
//! WHAT "OPEN" MEANS — AND WHERE. The FAITHFULNESS gates ask
//! `function_has_open_declined_vc`, not "is there any decline". Exactly one declined kind
//! is a HAND-OFF rather than a coverage gap: `UnsupportedMir { kind: "Rvalue::PtrOffset" }`,
//! whose in-bounds obligation the vcgen emitter explicitly assigns to
//! `prove::function_ptr_offsets_all_discharged` in trust-clean. Refusing a body whose
//! offsets ALL discharge would refuse more than a faithfulness verdict requires — it would
//! break the W2 lane's spelling-independence, where the same offset written `ptr::add`
//! certifies and written `Rvalue::PtrOffset` does not
//! (`mirsem::tests::ptr_offset_binop_count_certifies_identically_to_intrinsic`).
//! `ptr_offset_decline_is_honored_only_when_its_lane_closes` pins that the hand-off is
//! conditional and that it spares NO other kind.
//!
//! THE CERTIFICATION TIER SPARES NOTHING. `whole_program`'s two gates mint a different
//! claim — whole-body panic-freedom plus assumption authority for every caller — and the
//! offset lane does not establish it. On the probes below the decline is the ONLY L0 row,
//! so SKIPPING it empties the surviving L0 set — Channel 2's shape one level down:
//! `probe::count_after_panicking_leaf` panics 24/24 under the runtime oracle
//! (`sources/oracle_d1.rs`) with an offset that discharges perfectly, and reached
//! `cert_proved` / `is_assumable` / `ProofStatus::Certified` while the row was skipped.
//! `ptr_offset_decline_earns_no_certification_tier` pins the refusal AND pins that the
//! two spellings agree at that tier — the `ptr::add` twin is refused too, by a real
//! `Assertion { "[unsafe:sep:offset] …" }` row that does not refute.

#![cfg(test)]

use trust_types::{VcKind, VerifiableFunction};

const FIXTURES: &str = "fixtures/decline-handling-2026-08-25/dumps";

fn load(name: &str) -> Option<VerifiableFunction> {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURES).join(format!("{name}.json"));
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

fn declined_rows(func: &VerifiableFunction) -> Vec<VcKind> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .map(|vc| vc.kind)
        .filter(|k| matches!(k, VcKind::UnsupportedMir { .. }))
        .collect()
}

/// The bodies whose runtime oracle PANICS and whose obligation set reaches a declined
/// row. `oracle_rows.txt` records the measured panic rate and first witness for each.
const PANICKING_WITH_DECLINE: &[&str] = &[
    "vec_range_index_with_ensures", // 63/108, first (len 0, end 1)
    "p1_vec_range_sum",             // 63/108, first (len 0, end 1)
    "p3_map_index",                 // 18/24,  first (nkeys 0, k 0)
    "q3_vec_range2",                // 328/384, first (len 0, a 0, b 1)
    "q5_dyn_range",                 // 27/48,  first (len 0, e 1)
    "q6_vec_range_ensures",         // 27/48,  first (len 0, end 1)
    "q7_boxslice_range",            // 27/48,  first (len 0, end 1)
    "q2_btree_index",               // 18/24,  first (n 0, k 0)
];

/// Every fixture in [`PANICKING_WITH_DECLINE`] must actually reach a declined row —
/// otherwise the tests below would pass for the wrong reason (a fixture that stopped
/// exercising the channel would silently become a no-op).
#[test]
fn panicking_fixtures_all_reach_a_declined_row() {
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else {
            panic!("fixture {name} is missing — the channel would go unmeasured");
        };
        assert!(
            !declined_rows(&func).is_empty(),
            "{name} no longer emits a declined row; this fixture no longer exercises the \
             decline channel and must be replaced, not deleted"
        );
    }
}

/// CHANNEL 2 (and, for the `Bool(false)` rows, Channel 1 as well): the LIVE soundness
/// gate must REFUSE every panicking body that reaches a declined row.
#[test]
fn declined_row_blocks_the_safety_discharge_gate() {
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else { continue };
        assert!(
            !crate::prove::function_safety_vcs_all_discharged(&func),
            "{name} PANICS under the runtime oracle and its obligation set contains a \
             DECLINED row {:?}, yet function_safety_vcs_all_discharged said every safety \
             obligation is discharged — that verdict is threaded into termination and \
             fully-faithful claims",
            declined_rows(&func)
        );
    }
}

/// The COMPENSATING gate must fire on the same rows. Before the decline clause it
/// applied the identical `is_safety_vc_kind` filter, so it was defeated by exactly what
/// defeated the gate above.
#[test]
fn declined_row_trips_the_unmodeled_safety_gate() {
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else { continue };
        assert!(
            crate::mirsem::function_emits_unmodeled_safety_vc_pub(&func),
            "{name} reaches a declined row but the compensating gate reported nothing \
             unmodeled — it is applying the same filter that drops the row"
        );
    }
}

/// CHANNEL 1, end to end on the real gates: a declined row must never reach
/// `ProofStatus::Certified` / `ProofStatusRegistry::is_assumable`. That tier mints
/// ASSUMPTION AUTHORITY, so one laundered function poisons every caller.
#[test]
fn declined_row_never_reaches_assumption_authority() {
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else { continue };
        let mut registry = crate::composition_transfer::ProofStatusRegistry::new();
        let summary =
            crate::whole_program::certify_callee_summary(&func, trust_ir::FuncId::new(0), &mut registry);
        assert!(
            !summary.ir_summary.proved,
            "{name} PANICS under the runtime oracle yet certify_callee_summary reported \
             ir_summary.proved — a declined row was read as a discharge"
        );
        assert!(
            !registry.is_assumable(&func.def_path),
            "{name} PANICS under the runtime oracle yet the registry made it assumable"
        );
        let graph = crate::whole_program::verify_call_graph(std::slice::from_ref(&func));
        for v in &graph.verdicts {
            assert!(
                !matches!(v.status, crate::composition_transfer::ProofStatus::Certified),
                "{name} PANICS under the runtime oracle yet verify_call_graph certified it"
            );
        }
    }
}

/// The trust-ir twin of the safety-faithfulness gate uses `.all()` over the SAME
/// filtered set, which is vacuously `true` on empty. Same fixtures, same refusal.
#[test]
fn declined_row_blocks_the_trustir_safety_faithfulness_gate() {
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else { continue };
        assert!(
            !crate::trustir_safety::function_safety_vcs_faithful_via_trustir(&func),
            "{name} reaches a declined row yet the trust-ir safety-faithfulness gate was \
             vacuously true over an empty filtered set"
        );
    }
}

/// THE NEGATIVE CONTROL — the half that makes the tests above non-trivial. A gate that
/// refuses everything is not a fix. These three fixtures emit NO declined row, never
/// panic within their declared preconditions (`oracle_rows.txt`: `safe_div|requires
/// b!=0` 0/132, `safe_add|requires a<1000,b<1000` 0/1000000, and `opaque_divisor` is
/// `wrapping_sub`, which cannot panic), and must keep passing every gate above.
#[test]
fn decline_free_controls_keep_their_verdicts() {
    for name in ["safe_div", "safe_add", "opaque_divisor"] {
        let Some(func) = load(name) else {
            panic!("control fixture {name} is missing");
        };
        assert!(
            declined_rows(&func).is_empty(),
            "{name} must remain decline-free to serve as a control"
        );
        assert!(
            crate::prove::function_safety_vcs_all_discharged(&func),
            "{name} is panic-free within its preconditions and must still discharge"
        );
        assert!(
            !crate::mirsem::function_emits_unmodeled_safety_vc_pub(&func),
            "{name} must not be reported as emitting an unmodeled safety VC"
        );
        assert!(
            crate::trustir_safety::function_safety_vcs_faithful_via_trustir(&func),
            "{name} must still pass the trust-ir safety-faithfulness gate"
        );
    }
    // The two contract-carrying controls additionally keep their MirSem full-faithfulness
    // certificate — the tier the decline clause must not disturb.
    for name in ["safe_div", "safe_add"] {
        let Some(func) = load(name) else { continue };
        assert!(
            crate::mirsem::function_fully_faithful_witness(&func).is_some(),
            "{name} must keep its fully-faithful certificate"
        );
    }
}

/// THE POLARITY INVARIANT (the Channel-1 root cause, as a standing rule rather than a
/// one-site fix). A VC is a VIOLATION formula, so `Bool(true)` is SAT and can never be
/// reported as a proof while `Bool(false)` is UNSAT and discharges everywhere. A
/// declined row must therefore never carry `Bool(false)` — and, more strongly, must
/// never refute. Checked over every fixture in this directory.
#[test]
fn no_declined_row_carries_a_refutable_placeholder() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURES);
    let mut checked = 0usize;
    for entry in std::fs::read_dir(&dir).expect("fixture dir").flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        for vc in trust_vcgen::generate_vcs(&func) {
            if !matches!(vc.kind, VcKind::UnsupportedMir { .. }) {
                continue;
            }
            checked += 1;
            assert_ne!(
                vc.formula,
                trust_types::Formula::Bool(false),
                "{} emitted a DECLINED row with the UNSAT placeholder Bool(false); every \
                 consumer that tests `does the violation refute` reads that as a proof \
                 (kind={:?})",
                func.def_path,
                vc.kind
            );
            let augmented = crate::prove::augment_with_type_bounds_pub(&vc.formula, &func);
            assert!(
                !matches!(
                    crate::vc_refute::check_refute_vc(&augmented),
                    Some(crate::RefuteOutcome::RefutedModulo3)
                ),
                "{} emitted a DECLINED row whose violation formula REFUTES modulo 3 \
                 (kind={:?}) — a declined obligation must never be discharged by its \
                 placeholder",
                func.def_path,
                vc.kind
            );
        }
    }
    assert!(checked > 0, "no declined row was examined — the invariant went unmeasured");
}

/// THE COMPENSATION, pinned from both sides.
///
/// (a) A `Rvalue::PtrOffset` decline is spared ONLY while
///     `prove::function_ptr_offsets_all_discharged` closes it. The same body with an
///     UNRESOLVED offset base (`ptr_offset_bounds_open == None`) is refused — which is
///     what `prove::tests::intermediate_unmodeled_ptr_offset_fails_closed_via_discharge_gate`
///     measures on a real body.
/// (b) The hand-off is keyed to that ONE kind. Every panicking fixture in this file
///     carries a decline of a DIFFERENT kind and stays refused (the tests above), and the
///     kind-level classifier keeps them apart here.
#[test]
fn ptr_offset_decline_is_honored_only_when_its_lane_closes() {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody,
    };

    // (b) the kind key is exact: no other declined kind is spared. Measured over the
    // panicking fixtures, whose declines are SliceBoundsCheck / map-index-key-presence /
    // Rvalue::Cast — every one of them still reports OPEN.
    for name in PANICKING_WITH_DECLINE {
        let Some(func) = load(name) else { continue };
        assert!(
            crate::mirsem::function_has_open_declined_vc(&func),
            "{name}: only `Rvalue::PtrOffset` may be spared, and only conditionally; its \
             declined rows are {:?}",
            declined_rows(&func)
        );
    }

    // (a) an offset over a BARE PARAMETER pointer does not resolve, so its lane does not
    // close and the row stays OPEN even though it IS the spared kind.
    let raw = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) };
    let unresolved = VerifiableFunction {
        name: "bare_offset".into(),
        def_path: "probe::bare_offset".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: raw.clone(), name: None },
                LocalDecl { index: 1, ty: raw.clone(), name: Some("p".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::PtrOffset {
                        ptr: Operand::Copy(Place::local(1)),
                        count: Operand::Constant(ConstValue::Uint(1, 64)),
                    },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: raw,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(
        declined_rows(&unresolved)
            .iter()
            .any(|k| matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::PtrOffset")),
        "the probe must actually raise the spared kind, or it measures nothing"
    );
    assert!(
        !crate::prove::function_ptr_offsets_all_discharged(&unresolved),
        "the receiving lane must NOT close over a bare-parameter base"
    );
    assert!(
        crate::mirsem::function_has_open_declined_vc(&unresolved),
        "an unresolved offset leaves its declined row OPEN — the hand-off is conditional"
    );
    assert!(
        !crate::prove::function_safety_vcs_all_discharged(&unresolved),
        "and the gate must refuse it"
    );
}

// ===========================================================================
// D1 — THE COMPENSATED ROW EARNS NO CERTIFICATION TIER
// ===========================================================================

/// The `ptr-spine-corpus` `count` fixture (`memchr` `One::count`), the body both
/// spellings below are built from.
fn ptr_spine_count() -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/ptr-spine-corpus/count.json");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

/// `count` re-spelled with `Rvalue::PtrOffset` — the SAME construction as
/// `mirsem::tests::ptr_offset_binop_count_certifies_identically_to_intrinsic`: BB1's
/// `ptr::add(start, len)` Call terminator becomes a `Rvalue::PtrOffset` STATEMENT
/// writing `end` (_4), and BB1 becomes a `Goto`.
fn binop_spelled_count() -> VerifiableFunction {
    use trust_types::{BlockId, Place, Rvalue, Statement, Terminator};
    let mut f = ptr_spine_count();
    let Terminator::Call { args, .. } = &f.body.blocks[1].terminator else {
        panic!("count BB1 must be the ptr::add Call");
    };
    let (ptr, count) = (args[0].clone(), args[1].clone());
    f.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::PtrOffset { ptr, count },
        span: Default::default(),
    });
    f.body.blocks[1].terminator = Terminator::Goto(BlockId(2));
    f
}

/// `fn g(self, h) -> u64 { let r = leaf(h); let start = h.as_ptr();
/// let _end = unsafe { start.add(h.len()) }; r }` — `leaf` PANICS unconditionally.
///
/// Both calls form a PREFIX with empty pre-call statement lists, which is the shape
/// `whole_program::global_callee_hypotheses_have_supported_scope` admits, so this probe
/// reaches `certify_function_in_graph`'s VC loop (the `count` layout does not — its
/// verdict stops at the dominance-scope gate). `spell_binop` picks the offset spelling.
fn panicking_leaf_graph_probe(spell_binop: bool) -> VerifiableFunction {
    use trust_types::{BasicBlock, BlockId, Operand, Place, Rvalue, Statement, Terminator};
    let base = ptr_spine_count();
    let mut f = base.clone();
    f.name = "g".into();
    f.def_path = "probe::count_after_panicking_leaf".into();
    let as_ptr_call = base.body.blocks[0].terminator.clone();
    let meta = base.body.blocks[1].stmts[0].clone();
    let add_call = base.body.blocks[1].terminator.clone();
    let Terminator::Call { args, .. } = &add_call else {
        panic!("count BB1 must be the ptr::add Call");
    };
    let (ptr, count) = (args[0].clone(), args[1].clone());

    // BB0: the panicking leaf, writing the u64 result straight into `_0`.
    let mut leaf = as_ptr_call.clone();
    if let Terminator::Call { func, args, dest, target, .. } = &mut leaf {
        *func = "probe::always_panics".into();
        *args = vec![Operand::Copy(Place::local(2))];
        *dest = Place::local(0);
        *target = Some(BlockId(1));
    }
    f.body.blocks[0].stmts.clear();
    f.body.blocks[0].terminator = leaf;
    // BB1: `as_ptr`.
    let mut ap = as_ptr_call;
    if let Terminator::Call { target, .. } = &mut ap {
        *target = Some(BlockId(2));
    }
    f.body.blocks[1].stmts.clear();
    f.body.blocks[1].terminator = ap;
    // BB2: the slice-metadata read, then the offset in the chosen spelling.
    f.body.blocks[2].stmts = vec![meta];
    if spell_binop {
        f.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::PtrOffset { ptr, count },
            span: Default::default(),
        });
        f.body.blocks[2].terminator = Terminator::Return;
        f.body.blocks.truncate(3);
    } else {
        let mut add = add_call;
        if let Terminator::Call { target, .. } = &mut add {
            *target = Some(BlockId(3));
        }
        f.body.blocks[2].terminator = add;
        f.body.blocks.truncate(3);
        f.body.blocks.push(BasicBlock {
            id: BlockId(3),
            stmts: vec![],
            terminator: Terminator::Return,
        });
    }
    f
}

/// `#[ensures(result >= 0)]` — trivially true of the `u64` return, so the postcondition
/// VC refutes on the type bound alone and can never be the reason a verdict goes either
/// way. What is left deciding each verdict is the L0 row set.
fn with_trivial_ensures(mut f: VerifiableFunction) -> VerifiableFunction {
    use trust_types::{Formula, Sort};
    f.postconditions = vec![Formula::Ge(
        Box::new(Formula::Var("_0".to_string(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )];
    f
}

/// The three certification-tier authority columns for one body.
fn authority(f: &VerifiableFunction) -> (bool, bool, bool) {
    let mut registry = crate::composition_transfer::ProofStatusRegistry::new();
    let summary = crate::whole_program::certify_callee_summary(
        f,
        trust_ir::FuncId::new(0),
        &mut registry,
    );
    let graph = crate::whole_program::verify_call_graph(std::slice::from_ref(f));
    let certified = graph
        .verdicts
        .iter()
        .any(|v| matches!(v.status, crate::composition_transfer::ProofStatus::Certified));
    (summary.ir_summary.proved, registry.is_assumable(&f.def_path), certified)
}

/// D1 — a COMPENSATED declined row must not be SKIPPED by the certification loops.
///
/// `whole_program::{ensures_certified_modulo_3, certify_function_in_graph}` used to
/// `continue` past a `Rvalue::PtrOffset` decline whenever
/// `prove::function_ptr_offsets_all_discharged` held. That lane closes the OFFSET's own
/// in-bounds obligation; it does not establish whole-body panic-freedom, which is what
/// these two gates mint. With the row skipped the surviving row set went EMPTY, so the
/// loop was vacuous — Channel 2's shape one level down.
///
/// MEASURED, runtime oracle (`fixtures/decline-handling-2026-08-25/sources/oracle_d1.rs`,
/// stock rustc `-O -C debug-assertions=on`, `#[inline(never)]`, `black_box`,
/// `catch_unwind`, lengths 0..24): `count_panicking_leaf` 24/24 panicked,
/// `count_after_panicking_leaf` 24/24 panicked, `count_ok` 0/24. While the row was
/// skipped both panicking bodies reported `cert_proved` and `is_assumable`, and
/// `count_after_panicking_leaf` additionally reported `ProofStatus::Certified`.
///
/// The test also pins SPELLING AGREEMENT at this tier in the direction that matters:
/// the `ptr::add` twin of each probe is refused too (its offset raises a real
/// `Assertion { "[unsafe:sep:offset] …" }` row that does not refute), so refusing the
/// `Rvalue::PtrOffset` spelling is what makes the two agree — crediting it made the
/// BinOp spelling STRICTLY MORE authoritative than the intrinsic.
#[test]
fn ptr_offset_decline_earns_no_certification_tier() {
    let probes: [(&str, VerifiableFunction); 3] = [
        ("binop count", with_trivial_ensures(binop_spelled_count())),
        (
            "binop count, panicking leaf",
            with_trivial_ensures({
                let mut f = binop_spelled_count();
                for b in &mut f.body.blocks {
                    if let trust_types::Terminator::Call { func, .. } = &mut b.terminator {
                        if func == "arch::all::memchr::One::count_raw" {
                            *func = "probe::always_panics".to_string();
                        }
                    }
                }
                f.def_path = "probe::count_via_panicking_leaf".into();
                f
            }),
        ),
        (
            "panicking-leaf graph probe",
            with_trivial_ensures(panicking_leaf_graph_probe(true)),
        ),
    ];

    for (name, f) in &probes {
        // The probe must actually exercise the COMPENSATED path: one offset decline,
        // and a receiving lane that closes. Otherwise the refusal below proves nothing.
        assert!(
            declined_rows(f)
                .iter()
                .any(|k| matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::PtrOffset")),
            "{name}: the probe must raise the compensated kind, or it measures nothing"
        );
        assert!(
            crate::prove::function_ptr_offsets_all_discharged(f),
            "{name}: the compensating lane must CLOSE, or this is the unresolved case \
             `ptr_offset_decline_is_honored_only_when_its_lane_closes` already covers"
        );
        assert!(
            !crate::mirsem::function_has_open_declined_vc(f),
            "{name}: the FAITHFULNESS predicate still spares the closed hand-off — this \
             test is about the certification tier, which must refuse it anyway"
        );

        let (proved, assumable, certified) = authority(f);
        assert!(
            !proved,
            "{name}: certify_callee_summary reported `proved` for a body whose only L0 \
             obligation is a DECLINED row — the row was skipped, not discharged"
        );
        assert!(!assumable, "{name}: the registry made a declined-row body assumable");
        assert!(
            !certified,
            "{name}: verify_call_graph reached ProofStatus::Certified with the whole L0 \
             row set skipped"
        );
    }

    // The graph probe must really reach the VC loop, not stop at the dominance-scope
    // gate — otherwise its `Certified == false` would hold for an unrelated reason.
    let graph_probe = with_trivial_ensures(panicking_leaf_graph_probe(true));
    let verdicts = crate::whole_program::verify_call_graph(std::slice::from_ref(&graph_probe));
    assert!(
        verdicts.verdicts.iter().any(|v| v
            .open_reason
            .as_deref()
            .is_some_and(|r| r.contains("DECLINED row"))),
        "the graph probe must be refused BY THE DECLINE CLAUSE, got {:?}",
        verdicts.verdicts.iter().map(|v| v.open_reason.clone()).collect::<Vec<_>>()
    );

    // SPELLING AGREEMENT at this tier: the `ptr::add` twins are refused too.
    for (name, f) in [
        ("intrinsic count", with_trivial_ensures(ptr_spine_count())),
        ("intrinsic graph probe", with_trivial_ensures(panicking_leaf_graph_probe(false))),
    ] {
        assert!(
            declined_rows(&f).is_empty(),
            "{name}: the intrinsic spelling raises no decline — it is refused by a REAL \
             obligation, which is the asymmetry this test is about"
        );
        assert_eq!(
            authority(&f),
            (false, false, false),
            "{name}: the intrinsic spelling must stay refused at the certification tier"
        );
    }

    // THE POSITIVE CONTROL — without it every assertion above would also hold of a gate
    // that refuses everything, and of one that refuses exactly the decline-FREE bodies.
    // These three committed dumps carry no declined row and reach all three authority
    // columns; they are the only such bodies in the fixture corpus (measured over its
    // 2334 parsing dumps), so this is the whole positive side of the ledger.
    for name in ["real-spec-corpus/inc_gt", "safe-corpus/clamp_hi", "safe-corpus/pos"] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join(format!("{name}.json"));
        let func: VerifiableFunction =
            serde_json::from_slice(&std::fs::read(&path).unwrap_or_else(|e| {
                panic!("read {}: {e}", path.display())
            }))
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        assert!(
            declined_rows(&func).is_empty(),
            "{name} must stay decline-free to serve as the positive control"
        );
        assert_eq!(
            authority(&func),
            (true, true, true),
            "{name} carries no declined row and must keep cert_proved / is_assumable / \
             ProofStatus::Certified — the decline clause must not be a refuse-all"
        );
    }

    // AND the FAITHFULNESS tier is untouched: both spellings still certify fully
    // faithful, which is what `ptr_offset_binop_count_certifies_identically_to_intrinsic`
    // pins. Refusing declines at the certification tier must not reach into it.
    let empty_bodies = crate::trustir_fold::DumpBodies::new();
    let registry = {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures/ptr-spine-corpus/count_raw.json");
        let raw: VerifiableFunction =
            serde_json::from_slice(&std::fs::read(&path).expect("count_raw")).expect("parse");
        let mut r = std::collections::BTreeMap::new();
        r.insert(
            "arch::all::memchr::One::count_raw".to_string(),
            crate::mirsem::CalleeFact::of_certified(&raw),
        );
        r
    };
    for (name, f) in [("intrinsic", ptr_spine_count()), ("binop", binop_spelled_count())] {
        assert!(
            crate::prove::diagnose_fully_faithful_gate_with_bodies(&f, &registry, &empty_bodies)
                .fully_faithful,
            "{name}: the fully-faithful verdict must be unchanged by the certification-tier \
             decline clause"
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust (triage ticket 216): real-MIR evidence that a flat-lowered enum's `__tag`
//! slot holds the DECODED declared discriminant (`VariantDef::discriminant`), not
//! the variant index.
//!
//! THE DEFECT. The flat lane wrote the variant INDEX into `__tag`, while every
//! reader of the slot compares it against the declared discriminant: the
//! exact-extract `Discriminant` read hands `__tag` to a `SwitchInt` whose labels
//! are sign-extended at the `__tag` width, and the exhaustive-match `Assume`
//! requires the tag to be one of those labels. For `enum E { A = 5, B = 9 }` the
//! lowered IR wrote `1` for `E::B` and then assumed `tag == 5 || tag == 9` — an
//! `Assume(false)` on every path through the constructed value.
//!
//! THE FIXTURES ARE COMPILER DUMPS, NOT HAND-BUILT `Ty`s. Every `data/t216_*.json`
//! was produced by
//!
//! ```text
//! trustc --edition 2021 --crate-type=lib \
//!        -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> fixture.rs
//! ```
//!
//! from these enums (`mk_*` builds one per `pick`, `roundtrip_*` builds one and
//! matches on it — 100 for the first variant, 200 for the second — and
//! `vacuity_canary_*` divides by zero under the first variant's arm):
//!
//! ```text
//! pub enum E { A = 5, B = 9 }                           // SUBJECT, fieldless
//! #[repr(i8)] pub enum F { X = -3, Y = 7 }              // SUBJECT, negative
//! pub enum G { A = -3, B = 7 }                          // SUBJECT, negative, default repr
//! #[repr(u8)] pub enum P { A(u32) = 5, B(u32) = 9 }     // SUBJECT, payload
//! #[repr(i8)] pub enum N { X(u32) = -3, Y(u32) = 7 }    // SUBJECT, payload, negative
//! pub enum C { P = 0, Q = 1 }                           // CONTROL
//! pub enum GC { P = 0, Q = 1 }                          // CONTROL (G's module)
//! #[repr(u8)] pub enum PC { R(u32) = 0, S(u32) = 1 }    // CONTROL
//! ```
//!
//! WHICH FIXTURES CAN TELL THE OLD WRITE FROM THE NEW ONE. Every flat enum's
//! `__tag` is `i64`, but the bridge's `Discriminant` read only extracts `__tag`
//! when the read's destination type IS that type — default repr (`E`, `G`, `C`,
//! `GC`). `repr(u8)` (`P`, `PC`) reads a fresh value bounded to `[min, max]` and
//! `repr(i8)` (`F`, `N`) a bare fresh value; neither looks at `__tag`. So only
//! `E` and `G` can show the defect as behaviour, and the interpreter tests below
//! run exactly those, with `C`/`GC` as the controls.
//! `read_models_are_pinned_per_repr` pins that split, so a change in the read
//! lowering that would make this file measure a different lane goes red here.
//!
//! No probed shape produces a `SetDiscriminant`; that write site is covered by
//! the hand-built tests in `src/tests.rs`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as TrustIrTy;
use trust_ir::value::ValueId;
use trust_ir::{Constant as TrustIrConstant, Module};
use trust_types::{AggregateKind, Rvalue, Statement, Ty, VerifiableFunction};

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn lower(name: &str, json: &str) -> Module {
    let func = load(json);
    let module = trust_ir_bridge::lower_to_trust_ir(&func)
        .unwrap_or_else(|error| panic!("{name}: fixture must lower, got {error:?}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{name}: lowered to an invalid module: {errors:?}\n{module}");
    module
}

/// The `Ty::Adt` of the local the fixture's enum lives in.
fn enum_local_ty(func: &VerifiableFunction) -> Ty {
    func.body
        .locals
        .iter()
        .find_map(|l| match &l.ty {
            ty @ Ty::Adt { fields, .. } if fields.iter().any(|(n, _)| n == "__tag") => {
                Some(ty.clone())
            }
            _ => None,
        })
        .expect("fixture has a flat-lowered enum local with a `__tag` field")
}

/// The variant index every enum `Aggregate` write in the body names, in order.
fn aggregate_variants(func: &VerifiableFunction) -> Vec<usize> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Aggregate(kind, _), .. } = stmt
                && let AggregateKind::Adt { variant, .. } = kind
            {
                out.push(*variant);
            }
        }
    }
    out
}

/// The case labels of every `SwitchInt` whose block reads a `Discriminant`.
fn switch_case_labels(func: &VerifiableFunction) -> Vec<Vec<u128>> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        if let trust_types::Terminator::SwitchInt { targets, .. } = &block.terminator {
            let reads_discr = block
                .stmts
                .iter()
                .any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::Discriminant(_), .. }));
            if reads_discr {
                out.push(targets.iter().map(|(v, _)| *v).collect());
            }
        }
    }
    out
}

/// What the lowered module stores into a flat enum's `__tag` lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TagWrite {
    Const(i128),
    Havoc,
    Other,
}

/// The instruction that defines `value`, and whether it carries the
/// `FreshSymbolicHavoc` stamp.
fn producer_of(module: &Module, value: ValueId) -> Option<(&Inst, bool)> {
    module
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
        .find(|node| node.results.contains(&value))
        .map(|node| (&node.inst, node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)))
}

/// The field index of `__tag` in the module's struct `id`, if it has one.
fn tag_field_index(module: &Module, id: trust_ir::value::StructId) -> Option<u32> {
    let def = module.structs.get(id.index() as usize)?;
    def.fields.iter().position(|f| f.name == "__tag").and_then(|i| u32::try_from(i).ok())
}

/// Every value stored into a `__tag` lane, in program order: the `__tag` lane of
/// each complete `MakeAggregate` of a struct (the bridge's spelling of a complete
/// construction since BMC-LANE-1), or each `InsertField` into a struct's `__tag`
/// index (a seeded partial construction), followed back to the instruction that
/// produced the stored value. Tied to the slot, not to "the module contains this
/// constant" — an unrelated `const i64 0` elsewhere cannot satisfy it.
fn tag_writes(module: &Module) -> Vec<TagWrite> {
    let mut out = Vec::new();
    for func in &module.functions {
        for block in &func.blocks {
            for node in &block.body {
                let value = match &node.inst {
                    Inst::InsertField { ty: TrustIrTy::Struct(id), field, value, .. }
                        if tag_field_index(module, *id) == Some(*field) =>
                    {
                        *value
                    }
                    Inst::MakeAggregate { ty: TrustIrTy::Struct(id), variant: None, fields } => {
                        let Some(field) = tag_field_index(module, *id) else { continue };
                        let Some(value) = fields.get(field as usize) else { continue };
                        *value
                    }
                    _ => continue,
                };
                out.push(match producer_of(module, value) {
                    Some((Inst::Const { value: TrustIrConstant::Int(n), .. }, _)) => {
                        TagWrite::Const(*n)
                    }
                    Some((Inst::Undef { .. }, true)) => TagWrite::Havoc,
                    _ => TagWrite::Other,
                });
            }
        }
    }
    out
}

/// How the lowered module models the `Discriminant` read that feeds the enum's
/// `switch`.
#[derive(Debug, PartialEq, Eq)]
enum ReadModel {
    /// `extractfield` of the `__tag` lane — the only model that sees the write.
    ExtractTag,
    /// A `FreshSymbolicHavoc` value with this many `ule` bound comparisons on it.
    Range { bounds: usize },
    /// An unstamped fresh value with no bound.
    BareHavoc,
}

fn discriminant_read_model(name: &str, module: &Module) -> ReadModel {
    let insts = || module.functions.iter().flat_map(|f| &f.blocks).flat_map(|b| &b.body);
    let switches: Vec<ValueId> = insts()
        .filter_map(|n| match &n.inst {
            Inst::Switch { value, .. } => Some(*value),
            _ => None,
        })
        .collect();
    assert_eq!(switches.len(), 1, "{name}: exactly one enum switch\n{module}");
    let scrutinee = switches[0];
    match producer_of(module, scrutinee) {
        Some((Inst::ExtractField { aggregate, field, .. }, _)) => {
            let Some((Inst::Load { ty: TrustIrTy::Struct(id), .. }, _)) =
                producer_of(module, *aggregate)
            else {
                panic!("{name}: the extract reads a loaded enum struct\n{module}");
            };
            assert_eq!(tag_field_index(module, *id), Some(*field), "{name}: extracts `__tag`");
            ReadModel::ExtractTag
        }
        Some((Inst::Undef { .. }, true)) => {
            let bounds = insts()
                .filter(|n| {
                    matches!(&n.inst, Inst::ICmp { op: ICmpOp::Ule, lhs, rhs, .. }
                        if *lhs == scrutinee || *rhs == scrutinee)
                })
                .count();
            ReadModel::Range { bounds }
        }
        Some((Inst::Undef { .. }, false)) => ReadModel::BareHavoc,
        other => panic!("{name}: unexpected switch scrutinee producer {other:?}\n{module}"),
    }
}

/// The enum constructions of the module, made executable: a complete
/// `MakeAggregate` of a struct with a `__tag` lane (the bridge's spelling since
/// BMC-LANE-1) already executes and is counted as it is; each remaining
/// aggregate-seed `undef` of a struct is replaced by [`seed_struct_aggregates`].
fn struct_constructions(name: &str, module: &mut Module) -> usize {
    let complete = module
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
        .filter(|node| {
            matches!(&node.inst, Inst::MakeAggregate { ty: TrustIrTy::Struct(id), variant: None, .. }
                if tag_field_index(module, *id).is_some())
        })
        .count();
    complete + seed_struct_aggregates(name, module)
}

/// Replace each aggregate-seed `undef` of a struct with a zero `Const`, so the
/// reference interpreter (which refuses aggregate poison) can run the body.
///
/// Sound for these fixtures ONLY because the `InsertField` chain that follows
/// each seed overwrites EVERY field of the struct, so the seed's value never
/// shows through; that is asserted per seed, and a seed with any lane left
/// unwritten, or a non-integer lane, is refused rather than zeroed.
fn seed_struct_aggregates(name: &str, module: &mut Module) -> usize {
    let lane_tys: Vec<Vec<TrustIrTy>> =
        module.structs.iter().map(|s| s.fields.iter().map(|f| f.ty.clone()).collect()).collect();
    let mut seeded = 0;
    for func in &mut module.functions {
        for block in &mut func.blocks {
            for i in 0..block.body.len() {
                let Inst::Undef { ty: TrustIrTy::Struct(id) } = &block.body[i].inst else {
                    continue;
                };
                let id = *id;
                let lanes = &lane_tys[id.index() as usize];
                let mut current = block.body[i].results[0];
                let mut written = BTreeSet::new();
                for node in &block.body[i + 1..] {
                    if let Inst::InsertField { aggregate, field, .. } = &node.inst
                        && *aggregate == current
                    {
                        written.insert(*field);
                        current = node.results[0];
                    }
                }
                assert_eq!(
                    written.len(),
                    lanes.len(),
                    "{name}: the InsertField chain must overwrite every lane of the seeded \
                     struct, else a zero seed would show through: wrote {written:?} of {lanes:?}"
                );
                let zero = lanes
                    .iter()
                    .map(|ty| {
                        assert!(
                            matches!(
                                ty,
                                TrustIrTy::I8
                                    | TrustIrTy::I16
                                    | TrustIrTy::I32
                                    | TrustIrTy::I64
                                    | TrustIrTy::U8
                                    | TrustIrTy::U16
                                    | TrustIrTy::U32
                                    | TrustIrTy::U64
                            ),
                            "{name}: refusing to zero-seed a non-integer lane {ty}"
                        );
                        TrustIrConstant::Int(0)
                    })
                    .collect();
                block.body[i].inst = Inst::Const {
                    ty: TrustIrTy::Struct(id),
                    value: TrustIrConstant::Aggregate(zero),
                };
                block.body[i].proofs.clear();
                seeded += 1;
            }
        }
    }
    seeded
}

fn run(module: &Module, args: Vec<InterpretValue>) -> Result<i128, InterpretErrorCode> {
    match Interpreter::with_module(module).execute_func(module.functions[0].id, args) {
        Ok(outcome) => {
            let value = &outcome.returns[0];
            let bits = value.as_int().unwrap_or_else(|| panic!("an integer result, got {value:?}"));
            Ok(i128::try_from(bits.as_unsigned()).expect("u32 results fit i128"))
        }
        Err(error) => Err(error.code),
    }
}

fn u32_arg(value: i128) -> InterpretValue {
    InterpretValue::int(TrustIrTy::U32, value).expect("in-range u32")
}

// ---------------------------------------------------------------------------
// The artifacts: what the compiler hands the bridge.
// ---------------------------------------------------------------------------

/// The subjects reach the enum-aggregate `__tag` write with a NON-EMPTY variant
/// descriptor whose discriminants are not the variant indices. If a descriptor
/// ever comes back empty, the declared-value branch is unreachable again and
/// every other test in this file measures the index fallback instead.
#[test]
fn subject_fixtures_reach_the_aggregate_tag_write_with_a_non_index_descriptor() {
    for (name, json, expected) in [
        ("mk_e", include_str!("data/t216_mk_e_mir.json"), [("A", 5i128), ("B", 9)]),
        ("mk_f", include_str!("data/t216_mk_f_mir.json"), [("X", -3), ("Y", 7)]),
        ("mk_g", include_str!("data/t216_mk_g_mir.json"), [("A", -3), ("B", 7)]),
        ("mk_p", include_str!("data/t216_mk_p_mir.json"), [("A", 5), ("B", 9)]),
        ("mk_n", include_str!("data/t216_mk_n_mir.json"), [("X", -3), ("Y", 7)]),
    ] {
        let func = load(json);
        let ty = enum_local_ty(&func);
        let Ty::Adt { variants, .. } = &ty else { unreachable!() };
        let got: Vec<(String, i128)> =
            variants.iter().map(|v| (v.name.clone(), v.discriminant)).collect();
        let want: Vec<(String, i128)> =
            expected.iter().map(|(n, d)| ((*n).to_string(), *d)).collect();
        assert_eq!(got, want, "{name}: declared discriminants come from the compiler");
        for (idx, (_, disc)) in got.iter().enumerate() {
            assert_ne!(
                i128::try_from(idx).unwrap(),
                *disc,
                "{name}: a subject whose index == discriminant cannot show the defect"
            );
        }
        assert_eq!(aggregate_variants(&func), vec![0, 1], "{name}: one write per variant");
    }
}

/// The controls reach the same site in the same state, with index ==
/// discriminant at every variant, so the old and new writes coincide there.
#[test]
fn control_fixtures_reach_the_same_site_with_index_equal_discriminant() {
    for (name, json) in [
        ("mk_c", include_str!("data/t216_mk_c_mir.json")),
        ("mk_pc", include_str!("data/t216_mk_pc_mir.json")),
        ("roundtrip_gc", include_str!("data/t216_roundtrip_gc_mir.json")),
    ] {
        let func = load(json);
        let ty = enum_local_ty(&func);
        let Ty::Adt { variants, .. } = &ty else { unreachable!() };
        assert!(!variants.is_empty(), "{name}: same descriptor-present state as the subjects");
        for (idx, v) in variants.iter().enumerate() {
            assert_eq!(v.discriminant, i128::try_from(idx).unwrap(), "{name}: a control");
        }
        assert_eq!(aggregate_variants(&func), vec![0, 1], "{name}: same two writes");
    }
}

/// The read side of the artifacts: the enum's `SwitchInt` labels are the
/// declared discriminants (raw, as MIR spells them), not the indices.
#[test]
fn the_read_switches_on_declared_discriminants_not_indices() {
    for (name, json, want) in [
        ("roundtrip_e", include_str!("data/t216_roundtrip_e_mir.json"), vec![5u128, 9]),
        // `#[repr(i8)] F::X = -3`: the MIR label is the RAW pattern 253.
        ("roundtrip_f", include_str!("data/t216_roundtrip_f_mir.json"), vec![7, 253]),
        // Default-repr `G::A = -3`: the raw pattern at the isize width.
        (
            "roundtrip_g",
            include_str!("data/t216_roundtrip_g_mir.json"),
            vec![7, u128::from(u64::MAX) - 2],
        ),
        ("roundtrip_p", include_str!("data/t216_roundtrip_p_mir.json"), vec![5, 9]),
        ("roundtrip_c", include_str!("data/t216_roundtrip_c_mir.json"), vec![0, 1]),
        ("roundtrip_gc", include_str!("data/t216_roundtrip_gc_mir.json"), vec![0, 1]),
        ("roundtrip_pc", include_str!("data/t216_roundtrip_pc_mir.json"), vec![0, 1]),
    ] {
        let func = load(json);
        let labels = switch_case_labels(&func);
        assert_eq!(labels.len(), 1, "{name}: exactly one discriminant switch: {labels:?}");
        let mut got = labels[0].clone();
        got.sort_unstable();
        assert_eq!(got, want, "{name}: switch labels are the compiler's, not this test's");
    }
}

/// `VariantDef::discriminant` is DECODED while the `SwitchInt` label for the same
/// variant is RAW: `F::X` is `-3` in the descriptor and `253` on the switch. The
/// bridge decodes the label at the switch's width before comparing, so the value
/// `__tag` must hold is the decoded one — the raw pattern would be as wrong as
/// the index.
#[test]
fn descriptor_is_decoded_while_the_switch_label_is_raw() {
    let func = load(include_str!("data/t216_roundtrip_f_mir.json"));
    let ty = enum_local_ty(&func);
    let Ty::Adt { variants, .. } = &ty else { unreachable!() };
    assert_eq!(variants[0].name, "X");
    assert_eq!(variants[0].discriminant, -3, "the extractor decodes `X = -3` to -3, not 253");
    let labels = switch_case_labels(&func);
    assert!(labels[0].contains(&253), "the MIR label is the raw pattern 253: {labels:?}");
}

/// A negative result, recorded so the next reader does not repeat the search: no
/// probed shape produces a `SetDiscriminant`. Every construction arrives as
/// `Rvalue::Aggregate`, so the `lower_set_discriminant` half of the fix has no
/// source-level fixture here.
#[test]
fn no_probed_shape_emits_set_discriminant() {
    for json in [
        include_str!("data/t216_mk_c_mir.json"),
        include_str!("data/t216_mk_e_mir.json"),
        include_str!("data/t216_mk_f_mir.json"),
        include_str!("data/t216_mk_g_mir.json"),
        include_str!("data/t216_mk_n_mir.json"),
        include_str!("data/t216_mk_p_mir.json"),
        include_str!("data/t216_mk_pc_mir.json"),
        include_str!("data/t216_roundtrip_c_mir.json"),
        include_str!("data/t216_roundtrip_e_mir.json"),
        include_str!("data/t216_roundtrip_f_mir.json"),
        include_str!("data/t216_roundtrip_g_mir.json"),
        include_str!("data/t216_roundtrip_gc_mir.json"),
        include_str!("data/t216_roundtrip_p_mir.json"),
        include_str!("data/t216_roundtrip_pc_mir.json"),
        include_str!("data/t216_vacuity_canary_c_mir.json"),
        include_str!("data/t216_vacuity_canary_e_mir.json"),
        include_str!("data/t216_vacuity_canary_g_mir.json"),
        include_str!("data/t216_vacuity_canary_gc_mir.json"),
    ] {
        let func = load(json);
        let n = func
            .body
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .filter(|s| matches!(s, Statement::SetDiscriminant { .. }))
            .count();
        assert_eq!(n, 0, "{}: a shape now reaches `lower_set_discriminant`", func.name);
    }
}

// ---------------------------------------------------------------------------
// The lowering: what the bridge writes, and how it reads it back.
// ---------------------------------------------------------------------------

/// THE WRITE. The value stored into the `__tag` lane for each variant, followed
/// from the constructor's `__tag` lane back to its `Const`: the declared discriminant, decoded
/// (`-3`, not `253` and not `2^64 - 3`), for every subject; and for every control
/// the same value as before the fix, since there index == discriminant.
#[test]
fn tag_writes_are_the_declared_discriminants() {
    let mut wrong = Vec::new();
    for (name, json, want) in [
        ("mk_e", include_str!("data/t216_mk_e_mir.json"), [5, 9]),
        ("mk_f", include_str!("data/t216_mk_f_mir.json"), [-3, 7]),
        ("mk_g", include_str!("data/t216_mk_g_mir.json"), [-3, 7]),
        ("mk_n", include_str!("data/t216_mk_n_mir.json"), [-3, 7]),
        ("mk_p", include_str!("data/t216_mk_p_mir.json"), [5, 9]),
        ("mk_c", include_str!("data/t216_mk_c_mir.json"), [0, 1]),
        ("roundtrip_gc", include_str!("data/t216_roundtrip_gc_mir.json"), [0, 1]),
        ("mk_pc", include_str!("data/t216_mk_pc_mir.json"), [0, 1]),
    ] {
        let got = tag_writes(&lower(name, json));
        if got != want.map(TagWrite::Const) {
            wrong.push(format!("{name}: {got:?}, declared {want:?}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "`__tag` writes that are not the declared discriminants:\n{}",
        wrong.join("\n")
    );
}

/// THE READ, per repr — which of the bridge's three `Discriminant` read models
/// each fixture takes. Only the exact-extract model reads `__tag`, so only `E`,
/// `G` and their controls can show the write as behaviour; `P`/`PC` (a
/// `[min, max]`-bounded fresh value) and `F` (a bare fresh value) cannot, and a
/// before/after over them would be vacuous. Pinned so this file cannot quietly
/// start measuring a different lane.
#[test]
fn read_models_are_pinned_per_repr() {
    for (name, json, want) in [
        ("roundtrip_e", include_str!("data/t216_roundtrip_e_mir.json"), ReadModel::ExtractTag),
        ("roundtrip_g", include_str!("data/t216_roundtrip_g_mir.json"), ReadModel::ExtractTag),
        ("roundtrip_c", include_str!("data/t216_roundtrip_c_mir.json"), ReadModel::ExtractTag),
        ("roundtrip_gc", include_str!("data/t216_roundtrip_gc_mir.json"), ReadModel::ExtractTag),
        (
            "roundtrip_p",
            include_str!("data/t216_roundtrip_p_mir.json"),
            ReadModel::Range { bounds: 2 },
        ),
        (
            "roundtrip_pc",
            include_str!("data/t216_roundtrip_pc_mir.json"),
            ReadModel::Range { bounds: 2 },
        ),
        ("roundtrip_f", include_str!("data/t216_roundtrip_f_mir.json"), ReadModel::BareHavoc),
    ] {
        let module = lower(name, json);
        assert_eq!(discriminant_read_model(name, &module), want, "{name}\n{module}");
    }
}

/// THE BEHAVIOUR. Each round trip builds one variant and matches on it; Rust
/// returns 100 for the first variant and 200 for the second. The lowered IR,
/// executed on the reference interpreter, must agree. With the index in `__tag`,
/// `E` and `G` stop at the exhaustive-match `Assume(tag ∈ {labels})`
/// (`AssumeViolated`) on both inputs; the controls return the same values either
/// way.
#[test]
fn round_trips_execute_to_the_rust_result() {
    let mut wrong = Vec::new();
    for (name, json) in [
        ("roundtrip_e", include_str!("data/t216_roundtrip_e_mir.json")),
        ("roundtrip_g", include_str!("data/t216_roundtrip_g_mir.json")),
        ("roundtrip_c", include_str!("data/t216_roundtrip_c_mir.json")),
        ("roundtrip_gc", include_str!("data/t216_roundtrip_gc_mir.json")),
    ] {
        let mut module = lower(name, json);
        assert_eq!(struct_constructions(name, &mut module), 2, "{name}: two enum constructions");
        let got = (
            run(&module, vec![InterpretValue::bool(true)]),
            run(&module, vec![InterpretValue::bool(false)]),
        );
        if got != (Ok(100), Ok(200)) {
            wrong.push(format!("{name}(true, false) = {got:?}, Rust gives (100, 200)"));
        }
    }
    assert!(wrong.is_empty(), "round trips that disagree with Rust:\n{}", wrong.join("\n"));
}

/// THE CANARY. `vacuity_canary_*(true, n)` builds the first variant, whose arm
/// divides `n` by zero: the lowered IR must reach that division's `assert` and
/// fail it (`Panic`), not stop earlier on a false `Assume`, which would make the
/// arm — and the division-by-zero obligation in it — unreachable. The other arm
/// returns `n`.
#[test]
fn vacuity_canaries_reach_the_division_by_zero() {
    let mut wrong = Vec::new();
    for (name, json) in [
        ("vacuity_canary_e", include_str!("data/t216_vacuity_canary_e_mir.json")),
        ("vacuity_canary_g", include_str!("data/t216_vacuity_canary_g_mir.json")),
        ("vacuity_canary_c", include_str!("data/t216_vacuity_canary_c_mir.json")),
        ("vacuity_canary_gc", include_str!("data/t216_vacuity_canary_gc_mir.json")),
    ] {
        let mut module = lower(name, json);
        assert_eq!(struct_constructions(name, &mut module), 2, "{name}: two enum constructions");
        let got = (
            run(&module, vec![InterpretValue::bool(true), u32_arg(5)]),
            run(&module, vec![InterpretValue::bool(false), u32_arg(5)]),
        );
        if got != (Err(InterpretErrorCode::Panic), Ok(5)) {
            wrong
                .push(format!("{name}((true, 5), (false, 5)) = {got:?}, want (Err(Panic), Ok(5))"));
        }
    }
    assert!(wrong.is_empty(), "canaries that do not reach their division:\n{}", wrong.join("\n"));
}

// ---------------------------------------------------------------------------
// The IR conservation dump (run by hand; see the ticket-216 commit).
// ---------------------------------------------------------------------------

fn json_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "json") {
            out.push(path);
        }
    }
}

/// The number of enum constructions / `SetDiscriminant`s in `func` whose flat
/// `__tag` write differs between the index and the declared discriminant — the
/// writes this ticket changes.
fn non_dense_flat_tag_writes(func: &VerifiableFunction) -> usize {
    let local_ty = |local: usize| func.body.locals.iter().find(|l| l.index == local).map(|l| &l.ty);
    let is_flat_tagged =
        |ty: &Ty| matches!(ty, Ty::Adt { fields, .. } if fields.iter().any(|(n, _)| n == "__tag"));
    let mut count = 0;
    for stmt in func.body.blocks.iter().flat_map(|b| &b.stmts) {
        let (ty, variant) = match stmt {
            Statement::Assign {
                place,
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _),
                ..
            } if place.projections.is_empty() => (local_ty(place.local), *variant),
            Statement::SetDiscriminant { place, variant_index } if place.projections.is_empty() => {
                (local_ty(place.local), *variant_index)
            }
            _ => continue,
        };
        if let Some(ty) = ty
            && is_flat_tagged(ty)
            && ty.variant_tag(variant).is_some_and(|tag| i128::try_from(variant) != Ok(tag))
        {
            count += 1;
        }
    }
    count
}

/// Writes the lowered trust-ir text of every `VerifiableFunction` JSON under
/// `fixtures/` and `tests/data/` to `$T216_IR_OUT/<relative path>.ir` (a refused
/// lowering writes its error), and prints how many of the changed writes the
/// corpus reaches. Run once on the fixed tree and once with the `lower.rs` half
/// reverted, then `diff -r` the two directories: every file outside the t216
/// subjects must be byte-identical, and inside them only the `__tag` constants
/// may move.
#[test]
#[ignore = "diagnostic dump; needs T216_IR_OUT"]
fn t216_ir_conservation_dump() {
    let out = PathBuf::from(std::env::var("T216_IR_OUT").expect("set T216_IR_OUT"));
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    json_files(&root.join("fixtures"), &mut files);
    json_files(&root.join("tests/data"), &mut files);
    let (mut lowered, mut refused, mut skipped, mut reached) = (0, 0, 0, 0);
    for path in &files {
        let text = std::fs::read_to_string(path).expect("read fixture");
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else {
            skipped += 1;
            continue;
        };
        reached += non_dense_flat_tag_writes(&func);
        let rendered = match trust_ir_bridge::lower_to_trust_ir(&func) {
            Ok(module) => {
                lowered += 1;
                module.to_string()
            }
            Err(error) => {
                refused += 1;
                format!("REFUSED: {error:?}\n")
            }
        };
        let rel = path.strip_prefix(root).expect("under the crate root");
        let dest = out.join(rel).with_extension("ir");
        std::fs::create_dir_all(dest.parent().expect("has a parent")).expect("mkdir");
        std::fs::write(&dest, rendered).expect("write dump");
    }
    println!(
        "t216_ir_conservation_dump: files={} lowered={lowered} refused={refused} \
         skipped_not_a_function={skipped} reached_non_dense_flat_tag_writes={reached}",
        files.len()
    );
    assert!(reached > 0, "the corpus must reach the changed writes, else the diff is vacuous");
}

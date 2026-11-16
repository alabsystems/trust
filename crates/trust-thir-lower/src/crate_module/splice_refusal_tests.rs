//! Trust (2026-09-27): the splice refusals are TYPED. Ratification review 2026-09-28: R2 refuses a
//! signature over a WITHHELD layout as it refuses an identity spelling — the 2026-09-27 ledger
//! exemption admitted bodies the frozen pin refused and is withdrawn.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! Assembly tests over authored records in the shape the producer emits, not claims of executing
//! source Rust. The records transcribe the producer's measured output for
//! `thread_local! { static PAIR: RefCell<Option<(u64, u64)>> = RefCell::new(None) }`; the pin
//! over the real producer is `tests/run-make/trust-ir-withheld-layout-splice`.

use std::collections::BTreeSet;

use rustc_span::def_id::{DefIndex, LOCAL_CRATE};
use trust_ir::{
    Block, BlockId, Constant, FieldDef, FuncId, FuncTy, Inst, InstrNode, StructDef, StructId,
    StructRepr, Ty, ValueId,
};

use super::authority_tests::lineage_body_record;
use super::*;

const INIT_PATH: &str = "PAIR::__rust_std_internal_init_fn";
const REF_CELL: &str = "std::cell::RefCell<std::option::Option<(u64, u64)>>";
const REF_CELL_NEW: &str = "std::cell::RefCell::<T>::new";
const UNSAFE_CELL_OPTION: &str = "std::cell::UnsafeCell<std::option::Option<(u64, u64)>>";

fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef { name: name.to_string(), ty, offset }
}

fn row(
    id: u32,
    name: &str,
    fields: Vec<FieldDef>,
    layout: Option<(u64, u64)>,
    repr: StructRepr,
) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size: layout.map(|(size, _)| size),
        align: layout.map(|(_, align)| align),
        repr,
        origin: None,
    }
}

fn sid(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// `PAIR::__rust_std_internal_init_fn` — the body `thread_local!` generates for
/// `static PAIR: RefCell<Option<(u64, u64)>> = RefCell::new(None)` — as the producer lowers it on
/// a tree that carries `a032dc214b` + `0372fdcaeb`, transcribed from the measured dump:
///
/// ```text
/// struct @"std::cell::UnsafeCell<isize>" { value: isize @0 } size=8 align=8 repr=transparent
/// struct @"std::cell::Cell<isize>" { value: struct.0 @0 } size=8 align=8 repr=transparent
/// struct @"std::cell::UnsafeCell<std::option::Option<(u64, u64)>>" { value: bool } repr=transparent
/// struct @"std::cell::RefCell<std::option::Option<(u64, u64)>>" { borrow: struct.1, value: struct.2 }
/// fn @"PAIR::__rust_std_internal_init_fn"(() -> (struct.3)) {
/// bb0:
///     %0 = const bool false
///     %1 = call @"std::cell::RefCell::<T>::new"(%0)
///     ret %1
/// }
/// ```
///
/// `Option<(u64, u64)>` is declined by `enum_variant_field_admissible` (a tuple payload) and rides
/// the `Ty::Bool` flag lane (`None` is `false`), so the transparent `UnsafeCell<Option<..>>`
/// models 1 byte under rustc's 24 and WITHHOLDS its layout, and `RefCell` over it — a row naming
/// an unsized row — withholds too. The signature returns that `RefCell`.
///
/// `witnessed` is whether the producer's withheld-layout ledger names rows 2 and 3, which
/// `register_struct` now records (rustc computed both layouts; the producer withheld the claim).
fn tls_init_body(witnessed: bool) -> BodyRecord {
    let mut record = lineage_body_record(40, INIT_PATH);
    record.structs = vec![
        row(
            0,
            "std::cell::UnsafeCell<isize>",
            vec![field("value", Ty::Isize, Some(0))],
            Some((8, 8)),
            StructRepr::Transparent,
        ),
        row(
            1,
            "std::cell::Cell<isize>",
            vec![field("value", sid(0), Some(0))],
            Some((8, 8)),
            StructRepr::Transparent,
        ),
        row(
            2,
            UNSAFE_CELL_OPTION,
            vec![field("value", Ty::Bool, None)],
            None,
            StructRepr::Transparent,
        ),
        row(
            3,
            REF_CELL,
            vec![field("borrow", sid(1), None), field("value", sid(2), None)],
            None,
            StructRepr::Rust,
        ),
    ];
    if witnessed {
        record.layout_withheld_structs = vec![StructId::new(2), StructId::new(3)];
    }
    let signature =
        FuncTy { params: Vec::new(), returns: vec![sid(3)], is_vararg: false, abi: None };
    let mut function = record.function.take().expect("the probe record carries a function");
    function.ty = trust_ir::FuncTyId::new(0);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    function.blocks.push(block);
    record.function = Some(function);
    record.func_ty = Some(signature.clone());
    record.func_types = vec![signature];
    record.callees = vec![ref_cell_new()];
    record.contains_call = true;
    record.instr_count = 3;
    record
}

/// The callee ledger entry the producer mints for `RefCell::<T>::new` at this site: a foreign
/// Rust-ABI function taking the `Option` flag and returning the (withheld-layout) `RefCell` row.
fn ref_cell_new() -> CalleeRef {
    let definition = crate::lineage::DefinitionIdentity::test_only(0x7715, 1);
    CalleeRef {
        func_id: FuncId::new(1),
        is_local: false,
        def_index: 7715,
        def_id: DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(7715) },
        definition,
        concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        )),
        def_path: REF_CELL_NEW.to_string(),
        force_havoc: false,
        site_def_id: DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(7715) },
        site_args: None,
        // WS5.2: `Some` exactly when `concrete_key` is (the key's own empty args).
        instance_args: Some(Vec::new()),
        ret_ty: Some(sid(3)),
        ret_ty_conflict: false,
        abi: crate::calling_convention::FunctionAbi::RUST,
        params: crate::ParamSignature::Signed(vec![Ty::Bool]),
    }
}

fn only_row(assembled: &Assembled, def_index: u32) -> &CoverageRow {
    let rows: Vec<&CoverageRow> =
        assembled.coverage_rows.iter().filter(|row| row.def_index == def_index).collect();
    assert_eq!(rows.len(), 1, "exactly one coverage row per body");
    rows[0]
}

/// THE RESTORED REFUSAL (ratification review 2026-09-28). The thread-local init body returns a
/// `RefCell` row whose layout the producer WITHHELD (a 1-byte model of rustc's 24 bytes) and calls
/// the foreign `RefCell::new` with the `bool` flag where rustc passes the `Option`. The frozen pin
/// refused it (R2: its signature reaches a layout-less row); `881a7e964a` spliced it on the
/// producer's ledger witness, decided outside the oracle. It is refused again, BY NAME, WITH the
/// witness present — the ledger admits nothing. RED at `2b05b645a1` ("must not splice").
#[test]
fn a_thread_local_init_body_over_a_withheld_layout_is_refused_by_r2_even_when_witnessed() {
    let records = vec![tls_init_body(true)];
    assert!(signature_reaches_unlaid_struct(&records[0]));
    let assembled = assemble("withheld_layout_tls", &records, &BTreeSet::new());
    let row = only_row(&assembled, 40);
    assert!(row.lowered, "the init body lowered");
    assert!(!row.spliced, "a withheld-layout signature must not splice: {:?}", row.func_id);
    assert_eq!(row.splice_refusal, Some(SpliceRefusal::UnlaidSignatureStruct));
    assert_eq!(assembled.spliced, 0);
    assert!(
        assembled.module.functions.iter().all(|f| f.name != INIT_PATH || f.blocks.is_empty()),
        "no DEFINITION of the refused body may reach the assembled module"
    );
}

/// THE CONTROL: the same body WITHOUT the producer's ledger is refused the same way — the pin's
/// R2, now by name.
#[test]
fn an_unwitnessed_layoutless_signature_is_still_refused_by_r2_and_says_so() {
    let record = tls_init_body(false);
    assert_eq!(splice_refusal(&record, std::slice::from_ref(&record)), None);
    assert!(signature_reaches_unlaid_struct(&record));
    let records = vec![record];
    let assembled = assemble("unwitnessed_layoutless", &records, &BTreeSet::new());
    let row = only_row(&assembled, 40);
    assert!(row.lowered && !row.spliced);
    assert_eq!(row.splice_refusal, Some(SpliceRefusal::UnlaidSignatureStruct));
    assert_eq!(assembled.spliced, 0);
}

/// The ledger launders nothing, on any path R2 walks: by value, through a pointer, a witnessed
/// outer row over a witnessed inner row, and a witnessed row over an unwitnessed one. (RED at
/// `2b05b645a1`: the fully witnessed cases were admitted.)
#[test]
fn the_withheld_layout_ledger_admits_nothing_to_r2() {
    let full = tls_init_body(true);
    assert!(signature_reaches_unlaid_struct(&full), "witnessed outer + inner rows");

    let mut partial = tls_init_body(true);
    partial.layout_withheld_structs.retain(|id| *id != StructId::new(2));
    assert!(signature_reaches_unlaid_struct(&partial), "witnessed outer, unwitnessed inner");

    let mut by_ref = tls_init_body(false);
    by_ref.func_ty = Some(FuncTy {
        params: vec![Ty::Ref(Box::new(sid(2)))],
        returns: Vec::new(),
        is_vararg: false,
        abi: None,
    });
    assert!(signature_reaches_unlaid_struct(&by_ref), "unwitnessed, through a pointer");
    by_ref.layout_withheld_structs = vec![StructId::new(2)];
    assert!(signature_reaches_unlaid_struct(&by_ref), "witnessed, through a pointer");
}

/// Every lowered body the module leaves out names why, and the rest name nothing: one record per
/// refusal class a fixture reaches cheaply, a spliced control and an unlowered control; and the
/// rendered artifact carries the markers.
#[test]
fn every_lowered_but_unspliced_body_names_its_refusal_and_the_rest_name_none() {
    let spliced = lineage_body_record(1, "probe::spliced");
    let mut symbolic = lineage_body_record(2, "probe::symbolic");
    symbolic.symbolic = true;
    let mut union = lineage_body_record(3, "probe::union");
    union.union_lane = true;
    let renumbered = |mut record: BodyRecord, def_index: u32, path: &str| {
        record.def_index = def_index;
        record.def_path = path.to_string();
        record.definition =
            crate::lineage::DefinitionIdentity::test_only(0xC0DE, u64::from(def_index));
        record
    };
    // The call binds a result that its callee's declaration cannot carry (#197's arity rule).
    let mut arity = renumbered(tls_init_body(true), 4, "probe::arity");
    arity.callees[0].ret_ty = None;
    let unwitnessed = renumbered(tls_init_body(false), 5, "probe::unwitnessed");
    let mut unlowered = lineage_body_record(6, "probe::unlowered");
    unlowered.unsupported = vec![("Expr(unsupported)".to_string(), 1)];
    let records = vec![spliced, symbolic, union, arity, unwitnessed, unlowered];
    let assembled = assemble("typed_refusals", &records, &BTreeSet::new());

    let refusal = |def_index| only_row(&assembled, def_index).splice_refusal;
    assert_eq!(refusal(1), None, "a spliced row names no refusal");
    assert!(only_row(&assembled, 1).spliced);
    assert_eq!(refusal(2), Some(SpliceRefusal::Symbolic));
    assert_eq!(refusal(3), Some(SpliceRefusal::UnionLane));
    assert_eq!(refusal(4), Some(SpliceRefusal::CallResultArity));
    assert_eq!(refusal(5), Some(SpliceRefusal::UnlaidSignatureStruct));
    assert_eq!(refusal(6), None, "an unlowered row's reason is its `unsupported` tag");
    assert!(!only_row(&assembled, 6).lowered);
    for row in &assembled.coverage_rows {
        assert_eq!(
            row.lowered && !row.spliced,
            row.splice_refusal.is_some(),
            "the published invariant, row {}",
            row.def_index
        );
    }

    let coverage = coverage_json(
        "typed_refusals",
        &assembled.coverage_rows,
        assembled.spliced,
        assembled.declarations,
        &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded(),
    )
    .expect("every refusal is named, so the artifact renders");
    for marker in [
        "\"splice_refusal\": \"Splice(symbolic body)\"",
        "\"splice_refusal\": \"Splice(union placeholder lane)\"",
        "\"splice_refusal\": \"Splice(call result arity)\"",
        "\"splice_refusal\": \"Splice(signature reaches a layout-less struct)\"",
        "\"splice_refusal\": null",
    ] {
        assert!(coverage.contains(marker), "missing {marker} in {coverage}");
    }
}

/// The artifact boundary enforces the invariant: a lowered row dropped without a named refusal
/// — the silent loss this change exists to end — fails the render, and so does a refusal on a
/// row that was spliced or never lowered.
#[test]
fn the_coverage_render_refuses_a_silent_drop_and_a_misplaced_refusal() {
    let render = |row: CoverageRow| {
        coverage_json(
            "invariant",
            &[row],
            0,
            0,
            &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded(),
        )
    };
    let records = vec![lineage_body_record(9, "probe::row")];
    let assembled = assemble("invariant_rows", &records, &BTreeSet::new());
    let template = || {
        let source = &assembled.coverage_rows[0];
        CoverageRow {
            def_path: source.def_path.clone(),
            def_index: source.def_index,
            kind: source.kind,
            lowered: source.lowered,
            symbolic: source.symbolic,
            spliced: source.spliced,
            splice_refusal: source.splice_refusal,
            instr_count: source.instr_count,
            unsupported: source.unsupported.clone(),
            unsupported_details: source.unsupported_details.clone(),
            enum_declines: source.enum_declines.clone(),
            collect_primary: source.collect_primary.clone(),
            collect_cascade: source.collect_cascade.clone(),
            calls_resolved: source.calls_resolved,
            calls_extern: source.calls_extern,
            calls_unresolved: source.calls_unresolved,
            interpreter: source.interpreter.clone(),
            derived_mir: source.derived_mir.clone(),
            deferred_to_seam: source.deferred_to_seam,
            seam: source.seam.clone(),
            lineage: source.lineage,
            func_id: source.func_id,
        }
    };
    assert!(render(template()).is_ok(), "the assembled row renders as it is");

    let mut silent = template();
    silent.spliced = false;
    silent.func_id = None;
    silent.splice_refusal = None;
    let error = render(silent).expect_err("a silent drop must not publish");
    assert!(error.contains("names no splice refusal"), "{error}");

    let mut spliced_with_reason = template();
    spliced_with_reason.splice_refusal = Some(SpliceRefusal::RemapCertificate);
    assert!(render(spliced_with_reason).expect_err("misplaced").contains("but is spliced"));

    let mut unlowered_with_reason = template();
    unlowered_with_reason.lowered = false;
    unlowered_with_reason.spliced = false;
    unlowered_with_reason.func_id = None;
    unlowered_with_reason.splice_refusal = Some(SpliceRefusal::Symbolic);
    assert!(render(unlowered_with_reason).expect_err("misplaced").contains("but is not lowered"));
}

/// A later assembly round holds an earlier round's refusal out as `Vetoed`; the published row
/// names the refusal that first kept the body out, and keeps `Vetoed` only when no typed refusal
/// was ever recorded for it.
#[test]
fn a_vetoed_row_publishes_the_refusal_that_first_kept_it_out() {
    let unwitnessed = tls_init_body(false);
    let spliced = lineage_body_record(41, "probe::spliced");
    let records = vec![unwitnessed, spliced];
    let first = assemble("veto_round_1", &records, &BTreeSet::new());
    let mut first_refusals = BTreeMap::new();
    record_first_refusals(&first.coverage_rows, &mut first_refusals);
    assert_eq!(first_refusals.get(&40), Some(&SpliceRefusal::UnlaidSignatureStruct));

    let veto: BTreeSet<u32> = [40, 41].into_iter().collect();
    let mut second = assemble("veto_round_2", &records, &veto);
    assert_eq!(only_row(&second, 40).splice_refusal, Some(SpliceRefusal::Vetoed));
    assert_eq!(only_row(&second, 41).splice_refusal, Some(SpliceRefusal::Vetoed));
    record_first_refusals(&second.coverage_rows, &mut first_refusals);
    restore_vetoed_refusals(&mut second.coverage_rows, &first_refusals);
    assert_eq!(
        only_row(&second, 40).splice_refusal,
        Some(SpliceRefusal::UnlaidSignatureStruct),
        "the first round's typed refusal is what the row publishes"
    );
    assert_eq!(
        only_row(&second, 41).splice_refusal,
        Some(SpliceRefusal::Vetoed),
        "a body no round refused by type keeps the veto's own name"
    );
}

/// Every refusal class has its own stable marker: two classes never publish one spelling.
#[test]
fn splice_refusal_markers_are_distinct() {
    use SpliceRefusal::*;
    let all = [
        NotLowered,
        GeneratedUngated,
        Symbolic,
        UnionLane,
        StorageValueTraffic,
        EnumParamLane,
        ZstClosureArg,
        CoroutineFramePtr,
        FnptrAdapter,
        NoFunctionBody,
        EnumTable,
        StructTable,
        TypesTable,
        ClosureTable,
        GlobalShape,
        SignatureType,
        BlockParamType,
        InstructionType,
        UnmodeledInstruction,
        Invoke,
        IndirectCallSignature,
        FnPtrConstant,
        ConstantFuncId,
        SwitchFuncId,
        StaticGlobalOrigin,
        DefTableGraph,
        DefTableRemap,
        TypeTableRemap,
        ClosureTableRemap,
        TupleLayout,
        GlobalRemap,
        FunctionRemap,
        RemapCertificate,
        CallResultArity,
        PlaceCarrier,
        UnlaidSignatureStruct,
        PreparedBodyMissing,
        Vetoed,
    ];
    let markers: BTreeSet<&str> = all.iter().map(|refusal| refusal.marker()).collect();
    assert_eq!(markers.len(), all.len(), "a marker names exactly one class");
    assert!(markers.iter().all(|marker| marker.starts_with("Splice(") && marker.ends_with(')')));
}

/// Trust (trust-ir v52/v54): the splice's embedded-type walk models a SITELESS assert whatever its
/// kind (a kind's operands are registers), and never a SITED one: its panic entry (`FuncId`) and
/// location (`GlobalId`) are module ids no splice pass remaps, so the walk answers `None` and the
/// body is refused `Splice(unmodeled instruction)`. The two walkers stay in lockstep.
#[test]
fn a_sited_assert_is_unmodeled_by_the_splice() {
    let kinded = Inst::Assert {
        cond: ValueId::new(1),
        kind: trust_ir::AssertKind::BoundsCheck { index: ValueId::new(2), len: ValueId::new(3) },
        site: None,
    };
    assert_eq!(inst_embedded_tys(&kinded), Some(Vec::new()));
    assert_eq!(inst_embedded_tys_mut(&mut kinded.clone()).map(|tys| tys.len()), Some(0));
    for location in [
        trust_ir::PanicLocation::Value(ValueId::new(4)),
        trust_ir::PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
    ] {
        let mut sited = Inst::Assert {
            cond: ValueId::new(1),
            kind: trust_ir::AssertKind::Unspecified,
            site: Some(trust_ir::PanicSite { entry: FuncId::new(0), location }),
        };
        assert!(inst_embedded_tys(&sited).is_none(), "{sited:?}");
        assert!(inst_embedded_tys_mut(&mut sited).is_none(), "{sited:?}");
    }
}

fn zero_array_struct_record() -> BodyRecord {
    let mut record = lineage_body_record(740, "zero_array_struct_record");
    record.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    record.structs = vec![
        row(
            0,
            "ZeroElement",
            vec![field("word", Ty::U64, Some(0))],
            Some((8, 8)),
            StructRepr::Rust,
        ),
        row(
            1,
            "ZeroHolder",
            vec![field("n", Ty::U32, Some(0)), field("z", Ty::Array(TyId::new(0), 0), Some(8))],
            Some((8, 8)),
            StructRepr::Rust,
        ),
    ];
    record.types = vec![sid(0)];
    let array = Ty::Array(TyId::new(0), 0);
    let signature =
        FuncTy { params: vec![], returns: vec![array.clone()], is_vararg: false, abi: None };
    record.func_ty = Some(signature.clone());
    record.func_types = vec![signature];
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: array, value: Constant::Array(vec![]) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    record.function.as_mut().unwrap().blocks = vec![block];
    record.instr_count = 2;
    record
}

#[test]
fn zero_array_struct_dependency_dag_remaps_changed_ids_and_preserves_layout() {
    let record = zero_array_struct_record();
    assert_eq!(splice_refusal(&record, std::slice::from_ref(&record)), None);
    let mut destination = Module::new("zero_array_struct_destination");
    destination.target_info = record.target_info.clone();
    destination.add_type(Ty::Bool).unwrap();
    destination
        .add_struct_def(row(
            0,
            "Existing",
            vec![field("flag", Ty::Bool, Some(0))],
            Some((1, 1)),
            StructRepr::Rust,
        ))
        .unwrap();
    let mut globals = static_globals::StaticGlobals::default();
    let (mut function, signature, maps) =
        prepare_body_tables(&record, &mut destination, &mut globals)
            .expect("the existing DAG must relocate the admitted dependency");
    assert_eq!(maps.struct_map, vec![Some(StructId::new(1)), Some(StructId::new(2))]);
    assert_eq!(maps.ty_map, vec![Some(TyId::new(1))]);
    let array = Ty::Array(TyId::new(1), 0);
    assert_eq!(destination.types[1], sid(1));
    assert_eq!(destination.structs[2].fields[1].ty, array);
    assert_eq!(destination.structs[2].fields[1].offset, Some(8));
    assert_eq!(destination.structs[2].size, Some(8));
    assert_eq!(destination.structs[2].align, Some(8));
    assert_eq!(signature.returns, vec![array.clone()]);
    assert!(matches!(&function.blocks[0].body[0].inst,
        Inst::Const { ty, value: Constant::Array(elements) } if *ty == array && elements.is_empty()));
    let layout = destination.ty_layout_shape(&array).unwrap();
    assert_eq!(layout.size_bytes(), Some(0));
    assert_eq!(layout.align_bits, Some(64));
    function.ty = destination.add_func_type(signature).unwrap();
    destination.try_add_function(function).unwrap();
    assert!(trust_ir_build::validate_module(&destination).is_empty());
}

#[test]
fn zero_array_struct_still_requires_full_definition_admission_and_exact_order() {
    let original = zero_array_struct_record();
    assert_eq!(splice_refusal(&original, std::slice::from_ref(&original)), None);
    for case in 0..6 {
        let mut record = zero_array_struct_record();
        match case {
            0 => record.structs[0].fields[0].ty = Ty::Func(FuncTyId::new(0)),
            1 => record.structs[0].id = StructId::new(9),
            2 => record.types[0] = sid(9),
            3 => record.types[0] = sid(1), // self
            4 => {
                record.structs.push(row(2, "Later", vec![], Some((0, 1)), StructRepr::Rust));
                record.types[0] = sid(2); // forward
            }
            5 => record.types.clear(),
            _ => unreachable!(),
        }
        assert_eq!(
            splice_refusal(&record, std::slice::from_ref(&record)),
            Some(SpliceRefusal::StructTable),
            "hostile zero-array struct case {case}"
        );
    }
    // `[ZeroElement; 1]` leaves the zero-array lane. Since 689f5c0c81 the nonempty lane admits an
    // exact earlier registered struct element at the splice precheck (the inline twin in
    // `crate_module.rs`: "[S; 1]: exact earlier registered struct in the nonempty lane"), and
    // geometry is the final validator's: the holder still declares 8 bytes, so its now 8-byte `z`
    // at offset 8 lies outside it and the assembled module must not validate.
    let mut widened = zero_array_struct_record();
    widened.structs[1].fields[1].ty = Ty::Array(TyId::new(0), 1);
    assert_eq!(splice_refusal(&widened, std::slice::from_ref(&widened)), None);
    let mut destination = Module::new("zero_array_struct_widened_destination");
    destination.target_info = widened.target_info.clone();
    let mut globals = static_globals::StaticGlobals::default();
    let (mut function, signature, _) =
        prepare_body_tables(&widened, &mut destination, &mut globals)
            .expect("the precheck-admitted record relocates through the existing DAG");
    function.ty = destination.add_func_type(signature).unwrap();
    destination.try_add_function(function).unwrap();
    let errors = trust_ir_build::validate_module(&destination);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::ValidationError::StructLayoutInconsistent { .. }
        )),
        "a widened field past the declared holder size must not validate: {errors:?}"
    );
    let mut union = original;
    union.union_lane = true;
    assert_eq!(
        splice_refusal(&union, std::slice::from_ref(&union)),
        Some(SpliceRefusal::UnionLane)
    );
}

#[test]
fn zero_array_struct_cycles_and_dangling_dag_edges_still_refuse() {
    for case in 0..3 {
        let mut record = zero_array_struct_record();
        match case {
            0 => record.structs[0].fields[0].ty = sid(1), // struct cycle
            1 => record.structs[0].fields[0].ty = Ty::Array(TyId::new(0), 0), // type/struct cycle
            2 => record.types.clear(),                    // dangling type edge
            _ => unreachable!(),
        }
        assert_eq!(
            splice_refusal(&record, std::slice::from_ref(&record)),
            Some(SpliceRefusal::StructTable)
        );
        let mut destination = Module::new("refused_zero_array_struct");
        let mut globals = static_globals::StaticGlobals::default();
        assert!(
            matches!(
                prepare_body_tables(&record, &mut destination, &mut globals),
                Err(SpliceRefusal::DefTableGraph)
            ),
            "hostile dependency graph case {case}"
        );
    }
}

// ---- Trust (2026-11-12, PKG-C2): the per-body storage-value-traffic refusal over whole
// `assemble`. STORAGE-VALUE-TRAFFIC-1 landed the flag and its predicate; these pin what assembly
// does with it: the module validates, no storage-signed declaration is minted, which earlier
// refusals the flag pre-empts, and the crate validator stays the backstop. ----

/// The per-body module a record was cut from, rebuilt from the record's own tables, so a test
/// asks [`module_carries_storage_value_traffic`] what `build_body_record` asks of the intact
/// module.
fn per_body_module(record: &BodyRecord) -> Module {
    let mut module = Module::new("storage_value_traffic_probe");
    module.target_info = record.target_info.clone();
    module.structs = record.structs.clone();
    module.enums = record.enums.clone();
    module.types = record.types.clone();
    module.func_types = record.func_types.clone();
    module.globals = record.globals.clone();
    module.closure_types = record.closure_types.clone();
    module.functions =
        record.function.iter().cloned().chain(record.adapters.iter().cloned()).collect();
    module
}

/// The record as `build_body_record` would have recorded it: its flag computed by the
/// production predicate over its own module and callee ledger.
fn flagged(mut record: BodyRecord) -> BodyRecord {
    record.storage_value_traffic =
        module_carries_storage_value_traffic(&per_body_module(&record), &record.callees);
    record
}

fn storage_8_8() -> Ty {
    Ty::Storage(trust_ir::StorageLayout::new(8, 8))
}

/// `struct W { a: u32, m: MaybeUninit<u64> }` as the producer spells it since `060a4cd7ff`: the
/// `MaybeUninit` field is addressable storage geometry, and `W` keeps its full layout.
fn w_row() -> StructDef {
    row(
        0,
        "W",
        vec![field("a", Ty::U32, Some(0)), field("m", storage_8_8(), Some(8))],
        Some((16, 8)),
        StructRepr::Rust,
    )
}

/// `fn name(w: <param>) -> u32 { 0 }` over the `W` row: the signature and the entry block
/// parameter both carry `param`.
fn w_body(def_index: u32, name: &str, param: Ty) -> BodyRecord {
    let mut record = lineage_body_record(def_index, name);
    record.structs = vec![w_row()];
    let signature =
        FuncTy { params: vec![param.clone()], returns: vec![Ty::U32], is_vararg: false, abi: None };
    let mut function = record.function.take().expect("the probe record carries a function");
    function.ty = trust_ir::FuncTyId::new(0);
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), param));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(0) })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    function.blocks.push(block);
    record.function = Some(function);
    record.func_ty = Some(signature.clone());
    record.func_types = vec![signature];
    record.instr_count = 2;
    record
}

/// `struct Z { c: RefCell<Option<(u64, u64)>>, m: MaybeUninit<u64> }` reduced to what decides it:
/// a storage field in a row whose layout the producer withheld, taken by value by
/// `fn mk(z: Z) -> u32`. Without the flag R2 refuses it (`UnlaidSignatureStruct`, the measured
/// `r2.rs` shape); its own module also carries storage by value.
fn preempted_body(def_index: u32) -> BodyRecord {
    let mut record = w_body(def_index, "probe::mk", sid(0));
    record.structs = vec![row(
        0,
        "Z",
        vec![field("c", Ty::Bool, None), field("m", storage_8_8(), None)],
        None,
        StructRepr::Rust,
    )];
    record
}

fn storage_errors(module: &Module) -> usize {
    trust_ir_build::validate_module(module)
        .iter()
        .filter(|error| matches!(error, trust_ir_build::ValidationError::InvalidStorageUse { .. }))
        .count()
}

/// A body whose signature and entry block parameter carry `W` by value is refused BY NAME, the
/// by-reference control over the same row splices with the row's storage field and full layout
/// intact, and the assembled module passes the unchanged trust-ir storage rule. RED before
/// STORAGE-VALUE-TRAFFIC-1: the by-value body spliced and the module carried `InvalidStorageUse`.
///
/// The mutation half forces the flag off and requires the unchanged validator to refuse the
/// module: the crate-level backstop is intact, so a site the per-body refusal misses fails the
/// crate exactly as it did before.
#[test]
fn a_body_carrying_storage_by_value_is_refused_by_name_and_the_module_validates() {
    let by_value = flagged(w_body(50, "probe::get", sid(0)));
    let by_ref = flagged(w_body(51, "probe::ctl", Ty::Ref(Box::new(sid(0)))));
    assert!(by_value.storage_value_traffic, "W by value is storage value traffic");
    assert!(!by_ref.storage_value_traffic, "a pointer to storage carries no storage by value");
    let records = vec![by_value, by_ref];
    let assembled = assemble("storage_value_traffic", &records, &BTreeSet::new());

    let get = only_row(&assembled, 50);
    assert!(get.lowered && !get.spliced, "the by-value body must not splice");
    assert_eq!(get.splice_refusal, Some(SpliceRefusal::StorageValueTraffic));
    let ctl = only_row(&assembled, 51);
    assert!(ctl.spliced, "the by-reference control splices: {:?}", ctl.splice_refusal);
    assert_eq!(ctl.splice_refusal, None);
    assert_eq!(assembled.spliced, 1);
    let w = assembled.module.structs.iter().find(|row| row.name == "W").expect("W is laid out");
    assert_eq!(w.fields[1].ty, storage_8_8(), "the storage field is kept as geometry");
    assert_eq!((w.size, w.align), (Some(16), Some(8)));
    assert!(
        assembled.module.functions.iter().all(|f| f.name != "probe::get"),
        "no definition of the refused body reaches the module"
    );
    assert_eq!(storage_errors(&assembled.module), 0, "the assembled module obeys the storage rule");

    let coverage = coverage_json(
        "storage_value_traffic",
        &assembled.coverage_rows,
        assembled.spliced,
        assembled.declarations,
        &crate::clean_origin_join::CleanOriginJoinSummary::not_recorded(),
    )
    .expect("every refusal is named, so the artifact renders");
    assert!(coverage.contains("\"splice_refusal\": \"Splice(storage value traffic)\""));

    // Mutation half: without the witness the body splices and the validator still refuses.
    let unflagged: Vec<BodyRecord> = records
        .into_iter()
        .map(|mut record| {
            record.storage_value_traffic = false;
            record
        })
        .collect();
    let backstop = assemble("storage_value_backstop", &unflagged, &BTreeSet::new());
    assert!(only_row(&backstop, 50).spliced, "unflagged, the by-value body splices");
    assert!(
        storage_errors(&backstop.module) > 0,
        "the unchanged crate validator must still refuse storage carried by value"
    );
}

/// A foreign callee row: `ret_ty` and `params` as the producer's ledger records them.
fn foreign_callee(def_index: u32, path: &str, ret_ty: Option<Ty>, params: Vec<Ty>) -> CalleeRef {
    let definition = crate::lineage::DefinitionIdentity::test_only(0x5707, u64::from(def_index));
    let def_id = DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(def_index) };
    CalleeRef {
        func_id: FuncId::new(1),
        def_index,
        def_id,
        definition,
        concrete_key: Some(crate::lineage::ConcreteCalleeKey::test_only(
            definition,
            crate::lineage::ConcreteInstanceKind::Item,
            Vec::new(),
        )),
        def_path: path.to_string(),
        site_def_id: def_id,
        instance_args: Some(Vec::new()),
        ret_ty,
        params: crate::ParamSignature::Signed(params),
        ..ref_cell_new()
    }
}

/// `fn name() { let _ = callee(); }`: one call whose result is bound and never spelled — the
/// body's own module holds no storage, only the declaration it would mint does.
fn caller_body(def_index: u32, name: &str, callee: CalleeRef) -> BodyRecord {
    let mut record = lineage_body_record(def_index, name);
    record.structs = vec![w_row()];
    let mut function = record.function.take().expect("the probe record carries a function");
    let signature = FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None };
    function.ty = trust_ir::FuncTyId::new(0);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![] })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    record.function = Some(function);
    record.func_ty = Some(signature.clone());
    record.func_types = vec![signature];
    record.callees = vec![callee];
    record.contains_call = true;
    record.instr_count = 2;
    record
}

/// `Inst::Call` spells no type, so a caller that only binds a storage-typed result has no storage
/// site in its own module: the declaration it would mint does. The ledger half of the predicate
/// refuses both callers by name, and no storage-signed declaration is minted. The control's
/// storage-free callee is declared. RED with the module half alone: both callers spliced and the
/// minted declarations' signatures were rejected.
#[test]
fn a_caller_whose_callee_row_carries_storage_by_value_is_refused_and_no_declaration_is_minted() {
    let returns = foreign_callee(7801, "probe::new_uninit", Some(storage_8_8()), vec![]);
    let takes = foreign_callee(7802, "probe::consume_w", Some(Ty::Unit), vec![sid(0)]);
    let plain = foreign_callee(7803, "probe::plain", Some(Ty::U64), vec![Ty::Ref(Box::new(sid(0)))]);
    let records = vec![
        flagged(caller_body(60, "probe::binds_storage", returns.clone())),
        flagged(caller_body(61, "probe::passes_w", takes.clone())),
        flagged(caller_body(62, "probe::plain_caller", plain.clone())),
    ];
    // Neither caller's own module holds storage: only the ledger rows do.
    for record in &records {
        assert!(!module_carries_storage_value_traffic(&per_body_module(record), &[]));
    }
    assert!(records[0].storage_value_traffic, "a ledger row returning storage");
    assert!(records[1].storage_value_traffic, "a ledger row taking W by value");
    assert!(!records[2].storage_value_traffic);
    let assembled = assemble("storage_value_callers", &records, &BTreeSet::new());
    for def_index in [60, 61] {
        let row = only_row(&assembled, def_index);
        assert!(row.lowered && !row.spliced, "caller {def_index} must not splice");
        assert_eq!(row.splice_refusal, Some(SpliceRefusal::StorageValueTraffic));
    }
    assert!(only_row(&assembled, 62).spliced, "{:?}", only_row(&assembled, 62).splice_refusal);
    let declared = |callee: &CalleeRef| {
        assembled.codegen_declarations.iter().any(|d| d.definition() == Some(callee.definition))
            || assembled
                .module
                .functions
                .iter()
                .any(|f| f.blocks.is_empty() && f.display_path.as_deref() == Some(&callee.def_path))
    };
    assert!(declared(&plain), "the control's callee is declared");
    assert!(!declared(&returns), "no declaration returning storage is minted");
    assert!(!declared(&takes), "no declaration taking storage by value is minted");
    assert_eq!(storage_errors(&assembled.module), 0);

}

/// ONLY EVER REFUSES, over whole-`assemble` coverage rows (pass 1 AND the fixpoint), not
/// `splice_refusal` alone: every unflagged body publishes exactly the row it published without
/// the flag; a flagged body either keeps its earlier refusal or is refused `StorageValueTraffic`,
/// and is never spliced. The pinned cases:
///   * a refusal checked BEFORE the flag in `splice_refusal` (here `UnionLane`) keeps its marker
///     even when the body carries storage by value;
///   * PRE-EMPTION: a body the fixpoint's R2 refuses (`UnlaidSignatureStruct`) whose own module
///     carries storage by value is named `StorageValueTraffic`. The flag is checked inside
///     `splice_refusal`, before `prepare_body_tables` interns any of the body's tables, so every
///     later refusal (the rest of `splice_refusal`, `prepare_body_tables`' `Err` classes,
///     `RemapCertificate`, `CallResultArity`, `PlaceCarrier`, `UnlaidSignatureStruct`) is
///     pre-empted for such a body; it stays unspliced either way.
#[test]
fn storage_value_traffic_only_ever_refuses_over_whole_assembly() {
    let renumbered = |mut record: BodyRecord, def_index: u32, path: &str| {
        record.def_index = def_index;
        record.def_path = path.to_string();
        record.definition =
            crate::lineage::DefinitionIdentity::test_only(0xFE7C, u64::from(def_index));
        record
    };
    // Built twice from the same constructors: `BodyRecord` is not `Clone`, and the unflagged copy
    // is exactly what assembly sees without the flag (`storage_value_traffic: false`).
    let build = || -> Vec<BodyRecord> {
        let mut symbolic = lineage_body_record(2, "probe::symbolic");
        symbolic.symbolic = true;
        let mut union = lineage_body_record(3, "probe::union");
        union.union_lane = true;
        let mut arity = renumbered(tls_init_body(true), 4, "probe::arity");
        arity.callees[0].ret_ty = None;
        let mut unlowered = lineage_body_record(6, "probe::unlowered");
        unlowered.unsupported = vec![("Expr(unsupported)".to_string(), 1)];
        let mut union_by_value = w_body(9, "probe::union_by_value", sid(0));
        union_by_value.union_lane = true;
        vec![
            lineage_body_record(1, "probe::spliced"),
            symbolic,
            union,
            arity,
            renumbered(tls_init_body(false), 5, "probe::unwitnessed"),
            unlowered,
            w_body(7, "probe::by_value", sid(0)),
            w_body(8, "probe::by_ref", Ty::Ref(Box::new(sid(0)))),
            union_by_value,
            preempted_body(10),
        ]
    };
    let records: Vec<BodyRecord> = build().into_iter().map(flagged).collect();
    let unflagged = build();
    assert!(unflagged.iter().all(|record| !record.storage_value_traffic));
    for (def_index, witnessed) in [(1, false), (7, true), (8, false), (9, true), (10, true)] {
        let record = records.iter().find(|r| r.def_index == def_index).unwrap();
        assert_eq!(record.storage_value_traffic, witnessed, "{}", record.def_path);
    }
    let before = assemble("without_flag", &unflagged, &BTreeSet::new());
    let after = assemble("with_flag", &records, &BTreeSet::new());
    for record in &records {
        let was = only_row(&before, record.def_index);
        let now = only_row(&after, record.def_index);
        assert_eq!(was.lowered, now.lowered);
        if !record.storage_value_traffic {
            assert_eq!(
                (was.spliced, was.splice_refusal),
                (now.spliced, now.splice_refusal),
                "an unflagged body publishes the same row: {}",
                record.def_path
            );
        } else {
            assert!(!now.spliced, "a flagged body never splices: {}", record.def_path);
            assert!(
                now.splice_refusal == was.splice_refusal
                    || now.splice_refusal == Some(SpliceRefusal::StorageValueTraffic),
                "{}: {:?} -> {:?}",
                record.def_path,
                was.splice_refusal,
                now.splice_refusal
            );
        }
    }
    let pin = |def_index| {
        (only_row(&before, def_index).splice_refusal, only_row(&after, def_index).splice_refusal)
    };
    assert_eq!(pin(7), (None, Some(SpliceRefusal::StorageValueTraffic)), "spliced without the flag, refused with it");
    assert!(only_row(&before, 7).spliced);
    assert_eq!(pin(8), (None, None), "the by-reference control splices both times");
    assert_eq!(
        pin(9),
        (Some(SpliceRefusal::UnionLane), Some(SpliceRefusal::UnionLane)),
        "a refusal checked before the flag keeps its marker"
    );
    assert_eq!(
        pin(10),
        (Some(SpliceRefusal::UnlaidSignatureStruct), Some(SpliceRefusal::StorageValueTraffic)),
        "pre-emption: the fixpoint's R2 refusal is named by the flag"
    );
}

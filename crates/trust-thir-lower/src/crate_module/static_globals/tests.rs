//! Assembly tests over authored records, not claims of executing source Rust.

use std::collections::BTreeSet;

use rustc_span::def_id::{CrateNum, DefIndex, LOCAL_CRATE};
use trust_ir::{
    Block, BlockId, Constant, FieldDef, FuncId, Inst, InstrNode, Linkage, StructDef, StructId,
    StructRepr, Ty, ValueId, Visibility,
};

use super::super::authority_tests::lineage_body_record;
use super::super::{assemble, prepare_body_tables};
use super::*;

fn definition(index: u32) -> DefId {
    DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(index) }
}

fn scalar() -> Global {
    Global {
        name: "same_display_name".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(17)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn record(index: u32, globals: Vec<Global>, origins: Vec<GlobalOrigin>) -> BodyRecord {
    let mut record = lineage_body_record(index, &format!("body_{index}"));
    let mut block = Block::new(BlockId::new(0));
    for i in 0..globals.len() {
        block.body.push(
            InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(i as u32) })
                .with_result(ValueId::new(i as u32)),
        );
    }
    block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
    record.function.as_mut().expect("fixture function").blocks = vec![block];
    record.globals = globals;
    record.global_origins = origins;
    record
}

fn single(index: u32, identity: u32, global: Global) -> BodyRecord {
    record(index, vec![global], vec![GlobalOrigin::Static(definition(identity))])
}

fn addresses(function: &trust_ir::Function) -> Vec<GlobalId> {
    function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter_map(
            |node| {
                if let Inst::GlobalAddr { global } = &node.inst { Some(*global) } else { None }
            },
        )
        .collect()
}

#[test]
fn shared_static_remaps_every_body_address_without_merging_promotions() {
    let mut promotion = scalar();
    promotion.mutable = false;
    let first = record(
        0,
        vec![promotion, scalar()],
        vec![GlobalOrigin::BodyLocal, GlobalOrigin::Static(definition(40))],
    );
    let mut other_label = scalar();
    other_label.name = "a_different_body_local_label".into();
    let second = single(1, 40, other_label);
    let assembled = assemble("shared_static", &[first, second], &BTreeSet::new());
    assert_eq!(assembled.spliced, 2);
    assert_eq!(assembled.module.globals.len(), 2);
    assert_eq!(addresses(&assembled.module.functions[0]), [GlobalId::new(0), GlobalId::new(1)]);
    assert_eq!(addresses(&assembled.module.functions[1]), [GlobalId::new(1)]);
    assert!(!assembled.module.globals[0].mutable);
    assert!(assembled.module.globals[1].mutable);
    assert_eq!(assembled.module.globals[1].initializer, Some(Constant::Int(17)));
    assert!(super::super::final_module_validation_errors(&assembled.module).is_empty());
}

#[test]
fn equal_names_and_values_do_not_merge_distinct_definitions_or_promotions() {
    let mut immutable = scalar();
    immutable.mutable = false;
    let foreign =
        GlobalOrigin::Static(DefId { krate: CrateNum::from_u32(1), index: DefIndex::from_u32(40) });
    let records = vec![
        single(0, 40, immutable.clone()),
        single(1, 41, immutable.clone()),
        record(2, vec![immutable.clone()], vec![foreign]),
        record(3, vec![immutable.clone()], vec![GlobalOrigin::BodyLocal]),
        record(4, vec![immutable], vec![GlobalOrigin::BodyLocal]),
    ];
    let assembled = assemble("distinct_allocations", &records, &BTreeSet::new());
    assert_eq!(assembled.spliced, 5);
    assert_eq!(assembled.module.globals.len(), 5);
    for (index, function) in assembled.module.functions.iter().enumerate() {
        assert_eq!(addresses(function), [GlobalId::new(index as u32)]);
    }
}

#[test]
fn conflicting_static_claims_withhold_first_and_later_owners() {
    let mut mutations = Vec::new();
    let mut changed = scalar();
    changed.initializer = Some(Constant::Int(18));
    mutations.push(changed);
    let mut changed = scalar();
    changed.ty = Ty::U32;
    mutations.push(changed);
    let mut changed = scalar();
    changed.mutable = false;
    mutations.push(changed);
    let mut changed = scalar();
    changed.align = Some(16);
    mutations.push(changed);
    let mut changed = scalar();
    changed.linkage = Linkage::External;
    mutations.push(changed);
    let mut changed = scalar();
    changed.section = Some("another_section".into());
    mutations.push(changed);
    let mut changed = scalar();
    changed.visibility = Visibility::Hidden;
    mutations.push(changed);
    let mut changed = scalar();
    changed.retained = true;
    mutations.push(changed);
    let mut changed = scalar();
    changed.tls = Some(trust_ir::TlsModel::LocalExec);
    mutations.push(changed);
    for changed in mutations {
        for (first, second) in [(scalar(), changed.clone()), (changed.clone(), scalar())] {
            let records =
                vec![single(0, 40, first), single(1, 40, second), single(2, 40, scalar())];
            let assembled = assemble("conflicting_static", &records, &BTreeSet::new());
            assert_eq!(assembled.spliced, 0, "{changed:?}");
            assert!(assembled.assigned.is_empty());
            for row in assembled.coverage_rows {
                assert!(!row.lowered && !row.spliced);
                assert!(
                    row.unsupported
                        .iter()
                        .any(|(reason, _)| reason == "StaticGlobal(identity conflict)")
                );
            }
        }
    }
}

fn pending_static(identity: u32, global: u32) -> crate::PendingConst {
    crate::PendingConst {
        value: ValueId::new(0),
        def_id: definition(identity),
        span: rustc_span::DUMMY_SP,
        is_bool: false,
        is_float: false,
        signed: false,
        bits: 64,
        pointer_width: false,
        site_args: None,
        composite: false,
        str_global: None,
        static_global: Some(GlobalId::new(global)),
        promoted_global: None,
    }
}

#[test]
fn missing_duplicate_and_disagreeing_origin_ledgers_fail_closed() {
    let mut cases = Vec::new();
    let mut missing = single(1, 40, scalar());
    missing.global_origins.clear();
    // Independent deferred identity prevents a missing origin from hiding a conflict.
    missing.pending_consts.push(pending_static(40, 0));
    cases.push((missing, "GlobalOrigin(incomplete ledger)"));
    let mut extra = single(1, 40, scalar());
    extra.global_origins.push(GlobalOrigin::BodyLocal);
    cases.push((extra, "GlobalOrigin(incomplete ledger)"));
    cases.push((
        record(
            1,
            vec![scalar(), scalar()],
            vec![GlobalOrigin::Static(definition(40)), GlobalOrigin::Static(definition(40))],
        ),
        "GlobalOrigin(duplicate static identity)",
    ));
    cases.push((
        record(1, vec![scalar()], vec![GlobalOrigin::BodyLocal]),
        "GlobalOrigin(mutable global without static identity)",
    ));
    let mut disagreement = single(1, 41, scalar());
    disagreement.pending_consts.push(pending_static(40, 0));
    cases.push((disagreement, "GlobalOrigin(deferred static identity disagreement)"));
    for (invalid, expected) in cases {
        assert_eq!(validate_origins(&invalid), Err(expected));
        let assembled =
            assemble("invalid_origin", &[single(0, 40, scalar()), invalid], &BTreeSet::new());
        let invalid_row =
            assembled.coverage_rows.iter().find(|row| row.def_index == 1).expect("row");
        assert!(!invalid_row.lowered && !invalid_row.spliced);
        assert!(invalid_row.unsupported.iter().any(|(reason, _)| reason == expected));
        if expected != "GlobalOrigin(mutable global without static identity)" {
            assert_eq!(assembled.spliced, 0, "independent identity must taint the first owner");
        }
    }
}

fn structure(id: u32, name: &str, field: Ty) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![FieldDef { name: "field".into(), ty: field, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }
}

#[test]
fn nested_scalar_static_types_are_compared_after_struct_relocation() {
    let mut nested = scalar();
    nested.ty = Ty::Struct(StructId::new(1));
    nested.initializer =
        Some(Constant::Aggregate(vec![Constant::Aggregate(vec![Constant::Int(17)])]));
    let mut first = single(0, 40, nested.clone());
    first.structs =
        vec![structure(0, "Inner", Ty::U64), structure(1, "Outer", Ty::Struct(StructId::new(0)))];
    nested.ty = Ty::Struct(StructId::new(2));
    let mut second = single(1, 40, nested);
    second.structs = vec![
        structure(0, "Unrelated", Ty::U64),
        structure(1, "Inner", Ty::U64),
        structure(2, "Outer", Ty::Struct(StructId::new(1))),
    ];
    let assembled = assemble("nested_scalar_static", &[first, second], &BTreeSet::new());
    assert_eq!(assembled.spliced, 2);
    assert_eq!(assembled.module.globals.len(), 1);
    assert_eq!(assembled.module.globals[0].ty, Ty::Struct(StructId::new(1)));
    assert_eq!(addresses(&assembled.module.functions[0]), [GlobalId::new(0)]);
    assert_eq!(addresses(&assembled.module.functions[1]), [GlobalId::new(0)]);
}

#[test]
fn late_remap_failure_cannot_dangle_registry_and_new_assembly_is_fresh() {
    let mut broken = single(0, 40, scalar());
    broken.function.as_mut().expect("function").blocks[0].body[0].inst =
        Inst::GlobalAddr { global: GlobalId::new(9) };
    let good = single(1, 40, scalar());
    let mut module = Module::new("append_only");
    let mut registry = StaticGlobals::default();
    assert_eq!(
        prepare_body_tables(&broken, &mut module, &mut registry).err(),
        Some(super::super::SpliceRefusal::FunctionRemap),
        "a dangling promoted-global id refuses the splice by name"
    );
    assert_eq!(module.globals.len(), 1, "validated storage survives unrelated body refusal");
    let (function, _, _) =
        prepare_body_tables(&good, &mut module, &mut registry).expect("later valid owner");
    assert_eq!(module.globals.len(), 1);
    assert_eq!(addresses(&function), [GlobalId::new(0)]);
    let assembled = assemble("fresh", &[broken, good], &BTreeSet::new());
    assert_eq!(assembled.spliced, 1);
    assert_eq!(assembled.module.globals.len(), 1);
    assert_eq!(assembled.module.functions[0].id, FuncId::new(0));
    assert_eq!(addresses(&assembled.module.functions[0]), [GlobalId::new(0)]);
    let retry = assemble("fresh_again", &[single(1, 40, scalar())], &BTreeSet::new());
    assert_eq!(retry.spliced, 1);
    assert_eq!(addresses(&retry.module.functions[0]), [GlobalId::new(0)]);
}

#[test]
fn constant_identity_is_bit_exact_and_symbol_relocations_stay_refused() {
    for (left, right, equal) in [
        (0x7ff8_0000_0000_0001, 0x7ff8_0000_0000_0001, true),
        (0x7ff8_0000_0000_0001, 0x7ff8_0000_0000_0002, false),
        (0, 0x8000_0000_0000_0000, false),
    ] {
        let float = |bits| {
            let mut global = scalar();
            global.ty = Ty::Tuple(vec![Ty::F64]);
            global.initializer =
                Some(Constant::Aggregate(vec![Constant::Float(f64::from_bits(bits))]));
            global
        };
        let assembled = assemble(
            "float_bits",
            &[single(0, 40, float(left)), single(1, 40, float(right))],
            &BTreeSet::new(),
        );
        assert_eq!(assembled.spliced, if equal { 2 } else { 0 });
    }
    for unsupported in [
        Constant::SymbolAddr { symbol: "same_display_name".into(), addend: 0 },
        Constant::FnDef(FuncId::new(0)),
    ] {
        let mut global = scalar();
        global.initializer = Some(unsupported);
        let assembled =
            assemble("unsupported_relocation", &[single(0, 40, global)], &BTreeSet::new());
        assert_eq!(assembled.spliced, 0);
        assert!(assembled.module.globals.is_empty());
    }
}

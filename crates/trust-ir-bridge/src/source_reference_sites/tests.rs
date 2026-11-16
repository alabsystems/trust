//! Trust (C1, 2026-11-06): the source reference side table records exactly the
//! claims its doc allows, and `reconcile` withdraws every claim the final module
//! no longer matches.

use trust_ir::inst::Inst;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as TrustIrTy;
use trust_types::fx::FxHashSet;
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::*;
use crate::lower::lower_to_trust_ir_functions_with_test_source_reference_sites;

const DEF_PATH: &str = "test::load_through";

/// `fn load_through(<params>) -> ret { _0 = copy (*_<deref_local>) }`.
fn load_function(params: Vec<Ty>, deref_local: usize, ret: Ty) -> VerifiableFunction {
    let arg_count = params.len();
    let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
    locals.extend(params.into_iter().enumerate().map(|(i, ty)| LocalDecl {
        index: i + 1,
        ty,
        name: Some(format!("p{i}")),
    }));
    VerifiableFunction {
        name: "load_through".to_string(),
        def_path: DEF_PATH.to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: deref_local,
                        projections: vec![Projection::Deref],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty: ret,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn shared(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

fn clean() -> FxHashSet<String> {
    FxHashSet::from_iter([DEF_PATH.to_string()])
}

fn lower(
    func: &VerifiableFunction,
    clean_set: Option<&FxHashSet<String>>,
) -> (trust_ir::Module, LoweredSourceReferenceSites) {
    lower_to_trust_ir_functions_with_test_source_reference_sites(
        "source_reference_sites",
        std::slice::from_ref(func),
        clean_set,
    )
    .expect("the fixture must lower")
}

fn load_node(module: &trust_ir::Module) -> (usize, usize) {
    for (b, block) in module.functions[0].blocks.iter().enumerate() {
        for (i, node) in block.body.iter().enumerate() {
            if matches!(node.inst, Inst::Load { .. }) {
                return (b, i);
            }
        }
    }
    panic!("the fixture must contain a load");
}

#[test]
fn clean_scalar_reference_records_parameter_and_load() {
    for (pointee, mutable, mapped) in [
        (Ty::u32(), false, TrustIrTy::U32),
        (Ty::Bool, false, TrustIrTy::Bool),
        (Ty::u32(), true, TrustIrTy::U32),
        (Ty::i32(), false, TrustIrTy::I32),
    ] {
        let reference = Ty::Ref { mutable, inner: Box::new(pointee.clone()) };
        let func = load_function(vec![reference], 1, pointee);
        let (module, sites) = lower(&func, Some(&clean()));
        let reconciled = sites.reconcile(&module);
        assert_eq!(reconciled.withdrawn, 0, "{mapped:?}: nothing may be withdrawn");
        assert_eq!(reconciled.parameters.len(), 1, "{mapped:?}: one parameter claim");
        assert_eq!(reconciled.loads.len(), 1, "{mapped:?}: one load claim");
        let parameter = &reconciled.parameters[0];
        let load = &reconciled.loads[0];
        assert_eq!(parameter.pointee, mapped);
        assert_eq!(parameter.parameter_index, 0);
        assert_eq!(load.pointer, parameter.value, "the load reads through the parameter");
        assert_eq!(load.pointee, mapped);
        let entry = &module.functions[0].blocks[0];
        assert_eq!(entry.params[0], (parameter.value, TrustIrTy::Ptr));
        let node = &module.functions[0].blocks[load.block.index() as usize].body
            [load.instruction_index as usize];
        assert!(node.proofs.contains(&ProofAnnotation::ValidBorrow));
    }
}

#[test]
fn parameter_index_is_the_final_entry_position_not_the_local_number() {
    let func = load_function(vec![Ty::u32(), shared(Ty::u32())], 2, Ty::u32());
    let (module, sites) = lower(&func, Some(&clean()));
    let reconciled = sites.reconcile(&module);
    assert_eq!(reconciled.parameters.len(), 1, "only the reference parameter is claimed");
    let parameter = &reconciled.parameters[0];
    let entry = &module.functions[0].blocks[0];
    assert_eq!(entry.params[parameter.parameter_index as usize], (parameter.value, TrustIrTy::Ptr));
    assert_eq!(parameter.parameter_index, 1);
}

#[test]
fn unclean_function_records_nothing() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let other = FxHashSet::from_iter(["test::someone_else".to_string()]);
    let (_, sites) = lower(&func, Some(&other));
    assert_eq!(sites.claim_count(), 0, "an unclean (unlisted) function claims nothing");
    let (_, sites) = lower(&func, Some(&FxHashSet::default()));
    assert_eq!(sites.claim_count(), 0);
}

#[test]
fn plain_path_records_nothing_although_it_stamps_valid_borrow() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (module, sites) = lower(&func, None);
    let (b, i) = load_node(&module);
    assert!(
        module.functions[0].blocks[b].body[i].proofs.contains(&ProofAnnotation::ValidBorrow),
        "the plain path keeps its default stamp; that is exactly why it may claim nothing"
    );
    assert_eq!(sites.claim_count(), 0);
}

#[test]
fn raw_pointer_deref_records_nothing() {
    let raw = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) };
    let func = load_function(vec![raw], 1, Ty::u32());
    let (_, sites) = lower(&func, Some(&clean()));
    assert_eq!(sites.claim_count(), 0, "a raw pointer is no source reference");
}

fn stamped_struct(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    ty
}

fn stamped(ty: Ty, kind: trust_types::AdtKind) -> Ty {
    let mut ty = ty;
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(kind);
    }
    ty
}

#[test]
fn erased_wrapper_and_unstamped_pointees_are_never_claimed() {
    use trust_types::AdtKind;
    let maybe_uninit = stamped(
        Ty::adt("core::mem::MaybeUninit", vec![("value".into(), Ty::u32())]),
        AdtKind::Union,
    );
    let cell = stamped_struct(
        "core::cell::Cell",
        vec![(
            "value".into(),
            stamped_struct("core::cell::UnsafeCell", vec![("value".into(), Ty::u32())]),
        )],
    );
    let manually_drop =
        stamped_struct("core::mem::ManuallyDrop<u32>", vec![("value".into(), Ty::u32())]);
    // A local struct that reaches `UnsafeCell` through a field.
    let holds_cell = stamped_struct("test::HoldsCell", vec![("c".into(), cell.clone())]);
    let local_union = stamped(Ty::adt("test::U", vec![("a".into(), Ty::u32())]), AdtKind::Union);
    let local_enum_kind = stamped(Ty::adt("test::E", vec![("a".into(), Ty::u32())]), AdtKind::Enum);
    // The extractor never stamped it: a synthetic ADT proves nothing.
    let unstamped = Ty::adt("test::Wrapper", vec![("0".into(), Ty::u32())]);
    let float_field = stamped_struct("test::F", vec![("x".into(), Ty::Float { width: 64 })]);
    let reference_field = stamped_struct("test::R", vec![("r".into(), shared(Ty::u32()))]);
    let unit_struct = stamped_struct("test::Good", vec![]);
    let mut lowered = 0;
    for pointee in [
        maybe_uninit,
        cell,
        manually_drop,
        holds_cell,
        local_union,
        local_enum_kind,
        unstamped,
        float_field,
        reference_field,
        unit_struct,
        Ty::Tuple(vec![]),
        Ty::Char,
        Ty::PtrSizedInt { signed: false },
    ] {
        assert!(
            !source_reference_to_claimable_pointee(&shared(pointee.clone())),
            "{pointee:?} must not be claimable from its source type"
        );
        let func = load_function(vec![shared(pointee.clone())], 1, pointee.clone());
        // A fixture the bridge refuses to lower records nothing either; count the
        // ones that did lower so the lowering half cannot pass vacuously.
        if let Ok((_, sites)) = lower_to_trust_ir_functions_with_test_source_reference_sites(
            "source_reference_sites",
            std::slice::from_ref(&func),
            Some(&clean()),
        ) {
            lowered += 1;
            assert_eq!(sites.claim_count(), 0, "{pointee:?}: no claim may be recorded");
        }
    }
    assert!(lowered >= 3, "the lowering half must reach the recorder ({lowered} lowered)");
    assert!(source_reference_to_claimable_pointee(&shared(Ty::u32())));
    assert!(!source_reference_to_claimable_pointee(&Ty::u32()));
    let module = trust_ir::Module::new("claimable");
    for mapped in
        [TrustIrTy::Char, TrustIrTy::Usize, TrustIrTy::Isize, TrustIrTy::Ptr, TrustIrTy::Unit]
    {
        assert!(!claimable_pointee(&module, &mapped), "{mapped:?} must not be claimable");
    }
}

/// Trust (2026-11-07): a tuple or an extractor-stamped local struct whose whole
/// field tree is `bool`/integers is claimed (parameter and load), with the
/// mapped product as the pointee.
#[test]
fn finite_scalar_products_are_claimed() {
    let pair = Ty::Tuple(vec![Ty::u32(), Ty::Bool]);
    let newtype =
        stamped_struct("test::A", vec![("0".into(), Ty::Int { width: 8, signed: false })]);
    let nested = stamped_struct(
        "test::Outer",
        vec![
            ("a".into(), newtype.clone()),
            ("t".into(), pair.clone()),
            ("z".into(), Ty::Tuple(vec![])),
        ],
    );
    for pointee in [pair, newtype, nested] {
        assert!(source_reference_to_claimable_pointee(&shared(pointee.clone())), "{pointee:?}");
        let func = load_function(vec![shared(pointee.clone())], 1, pointee.clone());
        let (module, sites) = lower(&func, Some(&clean()));
        let reconciled = sites.reconcile(&module);
        assert_eq!(reconciled.withdrawn, 0, "{pointee:?}");
        assert_eq!(reconciled.parameters.len(), 1, "{pointee:?}: one parameter claim");
        assert_eq!(reconciled.loads.len(), 1, "{pointee:?}: one load claim");
        let parameter = &reconciled.parameters[0];
        assert!(claimable_pointee(&module, &parameter.pointee), "{pointee:?}");
        assert!(
            matches!(parameter.pointee, TrustIrTy::Tuple(_) | TrustIrTy::Struct(_) | TrustIrTy::U8),
            "{pointee:?} mapped to {:?}",
            parameter.pointee
        );
        assert_eq!(reconciled.loads[0].pointee, parameter.pointee);
    }
}

#[test]
fn a_stripped_valid_borrow_withdraws_the_load() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (mut module, sites) = lower(&func, Some(&clean()));
    let (b, i) = load_node(&module);
    module.functions[0].blocks[b].body[i]
        .proofs
        .retain(|proof| !matches!(proof, ProofAnnotation::ValidBorrow));
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.loads.is_empty());
    assert_eq!(reconciled.withdrawn, 1);
    assert_eq!(reconciled.parameters.len(), 1, "the parameter claim is independent");
}

#[test]
fn a_rewritten_or_removed_load_withdraws_its_claim() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    // Retyped.
    let (mut module, sites) = lower(&func, Some(&clean()));
    let (b, i) = load_node(&module);
    if let Inst::Load { ty, .. } = &mut module.functions[0].blocks[b].body[i].inst {
        *ty = TrustIrTy::U64;
    }
    assert!(sites.reconcile(&module).loads.is_empty(), "a retyped load is not the claimed site");
    // Made volatile.
    let (mut module, sites) = lower(&func, Some(&clean()));
    if let Inst::Load { volatile, .. } = &mut module.functions[0].blocks[b].body[i].inst {
        *volatile = true;
    }
    assert!(sites.reconcile(&module).loads.is_empty());
    // Removed.
    let (mut module, sites) = lower(&func, Some(&clean()));
    module.functions[0].blocks[b].body.remove(i);
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.loads.is_empty(), "a removed load withdraws");
    // Duplicated (SSA identity no longer unique).
    let (mut module, sites) = lower(&func, Some(&clean()));
    let node = module.functions[0].blocks[b].body[i].clone();
    module.functions[0].blocks[b].body.insert(i, node);
    assert!(sites.reconcile(&module).loads.is_empty(), "an ambiguous definition withdraws");
}

#[test]
fn another_function_at_the_id_withdraws_every_claim() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (mut module, sites) = lower(&func, Some(&clean()));
    module.functions[0].name = "renamed".to_string();
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.is_empty());
    assert_eq!(reconciled.withdrawn, 2);
}

#[test]
fn a_parameter_no_longer_an_entry_pointer_withdraws() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (mut module, sites) = lower(&func, Some(&clean()));
    module.functions[0].blocks[0].params[0].1 = TrustIrTy::U64;
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.parameters.is_empty());
    assert!(reconciled.loads.is_empty(), "a load is claimed only through a parameter claim");
    assert_eq!(reconciled.withdrawn, 2);
}

#[test]
fn a_load_through_a_pointer_that_is_not_a_claimed_parameter_withdraws() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (module, mut sites) = lower(&func, Some(&clean()));
    // Keep the load claim, drop the parameter claim (as if the reference had
    // come from a call result inside the body).
    sites.functions[0].parameters.clear();
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.is_empty(), "{reconciled:?}");
    assert_eq!(reconciled.withdrawn, 1);
}

#[test]
fn withdraw_function_removes_every_claim_of_that_member() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (module, mut sites) = lower(&func, Some(&clean()));
    assert_eq!(sites.claim_count(), 2);
    sites.withdraw_function(0);
    assert_eq!(sites.claim_count(), 0);
    assert!(sites.reconcile(&module).is_empty());
}

#[test]
fn a_table_from_another_lowering_does_not_match_a_different_module() {
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (_, sites) = lower(&func, Some(&clean()));
    // A module of the same function lowered with an extra leading parameter: the
    // recorded values no longer name its loads or params.
    let other = load_function(vec![Ty::u32(), Ty::u32(), shared(Ty::u32())], 3, Ty::u32());
    let (other_module, _) = lower(&other, Some(&clean()));
    let reconciled = sites.reconcile(&other_module);
    assert!(reconciled.is_empty(), "a stale table must not bind to another module: {reconciled:?}");
}

/// The default extraction lane (`FAITHFUL_SCALARS` off) hands the bridge `char`
/// as `Ty::Int { 32, unsigned }` and `usize`/`isize` as `Ty::Int` at the target
/// width, so the source filter cannot tell them from `u32`/`u64` and they ARE
/// claimed: as an initialized integer of that width, which every valid `char`
/// or `usize` is. Only the faithful lane's `Ty::Char`/`Ty::PtrSizedInt` are
/// refused. The claim carries no range: its pointee is the plain integer type.
#[test]
fn default_lane_char_and_usize_are_claimed_only_as_initialized_integers() {
    for (lowered_as, mapped) in [
        (Ty::Int { width: 32, signed: false }, TrustIrTy::U32),
        (Ty::Int { width: 64, signed: false }, TrustIrTy::U64),
        (Ty::Int { width: 64, signed: true }, TrustIrTy::I64),
    ] {
        let func = load_function(vec![shared(lowered_as.clone())], 1, lowered_as);
        let (module, sites) = lower(&func, Some(&clean()));
        let reconciled = sites.reconcile(&module);
        assert_eq!(reconciled.parameters.len(), 1, "{mapped:?}");
        assert_eq!(reconciled.parameters[0].pointee, mapped, "only the plain integer type");
        assert_eq!(reconciled.loads.len(), 1, "{mapped:?}");
        assert_eq!(reconciled.loads[0].pointee, mapped);
    }
    for faithful in [Ty::Char, Ty::PtrSizedInt { signed: false }, Ty::PtrSizedInt { signed: true }]
    {
        assert!(!source_reference_to_claimable_pointee(&shared(faithful.clone())), "{faithful:?}");
    }
}

/// `fn f(pp: &&u32) -> u32 { **pp }`: the inner `&u32` is LOADED from memory,
/// not an entry parameter. The outer parameter is not claimable (its pointee is
/// a reference), and the load through the inner reference is recorded at the
/// stamp but withdrawn at reconciliation, because its pointer is no parameter
/// claim.
#[test]
fn a_load_through_a_loaded_reference_is_withdrawn() {
    let mut func = load_function(vec![shared(shared(Ty::u32()))], 1, Ty::u32());
    let Statement::Assign { rvalue: Rvalue::Use(Operand::Copy(place)), .. } =
        &mut func.body.blocks[0].stmts[0]
    else {
        unreachable!("the fixture's single statement")
    };
    place.projections = vec![Projection::Deref, Projection::Deref];
    let (module, sites) = lower(&func, Some(&clean()));
    assert!(sites.claim_count() >= 1, "the inner load is recorded at the ValidBorrow stamp");
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.is_empty(), "{reconciled:?}");
    assert!(reconciled.withdrawn >= 1);
}

/// `fn f(p: &u32) -> u32 { let r: &u32 = make(); *r }`: a reference the body got
/// from a call (as `MaybeUninit::assume_init_ref` returns one) is not the
/// parameter. The parameter is still claimed; the load through the call result is
/// withdrawn.
#[test]
fn a_load_through_a_call_result_reference_is_withdrawn() {
    let mut func = load_function(vec![shared(Ty::u32())], 2, Ty::u32());
    func.body.locals.push(LocalDecl { index: 2, ty: shared(Ty::u32()), name: Some("r".into()) });
    let load = func.body.blocks[0].stmts.remove(0);
    func.body.blocks[0].terminator = Terminator::Call {
        func: "test::make".to_string(),
        args: vec![],
        dest: Place::local(2),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        unwind: trust_types::UnwindEdge::Unreachable,
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![load],
        terminator: Terminator::Return,
    });
    let (module, sites) = lower(&func, Some(&clean()));
    let reconciled = sites.reconcile(&module);
    assert_eq!(reconciled.parameters.len(), 1, "the entry parameter is still claimed");
    assert!(
        reconciled.loads.is_empty(),
        "the call-result load must not be claimed: {reconciled:?}"
    );
    assert_eq!(sites.claim_count(), 2, "the load was recorded at the stamp and then withdrawn");
    assert_eq!(reconciled.withdrawn, 1);
}

/// `fn f(p: &u32, q: &u32) -> u32 { p = q; *p }`: an argument local reassigned
/// before the deref no longer holds `p`'s entry value. The bridge gives the copy
/// a fresh value, so the load's pointer is neither parameter claim and the load
/// is withdrawn (lossy, never a claim through `p`'s entry value). Both entry
/// parameters stay claimed.
#[test]
fn a_reassigned_argument_local_is_never_claimed_through_its_entry_value() {
    let mut func = load_function(vec![shared(Ty::u32()), shared(Ty::u32())], 1, Ty::u32());
    func.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        },
    );
    let (module, sites) = lower(&func, Some(&clean()));
    let reconciled = sites.reconcile(&module);
    assert_eq!(reconciled.parameters.len(), 2, "{reconciled:?}");
    let p_entry = reconciled
        .parameters
        .iter()
        .find(|parameter| parameter.parameter_index == 0)
        .expect("`p` is claimed at entry")
        .value;
    assert!(
        reconciled.loads.iter().all(|load| load.pointer != p_entry),
        "no load may be claimed through `p`'s entry value after `p = q`: {reconciled:?}"
    );
    assert!(reconciled.loads.is_empty(), "{reconciled:?}");
    assert_eq!(reconciled.withdrawn, 1);
}

/// `fn constant_reference() -> ret { _0 = const <constant> }`.
fn constant_function(ret: Ty, constant: ConstValue) -> VerifiableFunction {
    let mut func = load_function(vec![], 0, ret);
    func.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Constant(constant)),
        span: SourceSpan::default(),
    }];
    func
}

fn undef_node(module: &trust_ir::Module) -> (usize, usize) {
    for (b, block) in module.functions[0].blocks.iter().enumerate() {
        for (i, node) in block.body.iter().enumerate() {
            if matches!(node.inst, Inst::Undef { ty: TrustIrTy::Ptr }) {
                return (b, i);
            }
        }
    }
    panic!("the fixture must contain an Undef(Ptr)");
}

fn unit_struct() -> Ty {
    stamped_struct("test::Good", vec![])
}

fn newtype() -> Ty {
    stamped_struct("test::Newtype", vec![("0".into(), Ty::u32())])
}

/// Trust (2026-11-07): the valtree-recovered promoted shared borrow of a
/// fieldless struct (`&UnitStruct`) records one VALUE claim for its stamped
/// `Undef(Ptr)`, and nothing about its pointee.
#[test]
fn valtree_reference_constant_records_a_value_claim() {
    for (pointee, constant) in
        [(unit_struct(), ConstValue::struct_scalar_fields_ref("test::Good", vec![]))]
    {
        let func = constant_function(shared(pointee.clone()), constant);
        let (module, sites) = lower(&func, Some(&clean()));
        let reconciled = sites.reconcile(&module);
        assert_eq!(reconciled.withdrawn, 0, "{pointee:?}");
        assert!(reconciled.parameters.is_empty() && reconciled.loads.is_empty(), "{pointee:?}");
        assert_eq!(reconciled.values.len(), 1, "{pointee:?}: one value claim");
        let value = &reconciled.values[0];
        let node = &module.functions[0].blocks[value.block.index() as usize].body
            [value.instruction_index as usize];
        assert_eq!(node.results.as_slice(), [value.result]);
        assert!(matches!(node.inst, Inst::Undef { ty: TrustIrTy::Ptr }));
        assert!(node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc));
    }
}

/// `OpaqueConst` also carries unmodeled RUNTIME pointer values, a mutable
/// reference is no promoted shared constant, and an unclean or plain-path
/// function claims nothing at all.
#[test]
fn opaque_mutable_unclean_and_plain_reference_constants_claim_no_value() {
    let shared_unit = shared(unit_struct());
    let opaque = constant_function(shared_unit.clone(), ConstValue::opaque_const());
    let (module, sites) = lower(&opaque, Some(&clean()));
    let _ = undef_node(&module);
    assert_eq!(sites.claim_count(), 0, "OpaqueConst is never claimed");
    let mutable = constant_function(
        Ty::Ref { mutable: true, inner: Box::new(unit_struct()) },
        ConstValue::struct_scalar_fields_ref("test::Good", vec![]),
    );
    if let Ok((_, sites)) = lower_to_trust_ir_functions_with_test_source_reference_sites(
        "source_reference_sites",
        std::slice::from_ref(&mutable),
        Some(&clean()),
    ) {
        assert_eq!(sites.claim_count(), 0, "a mutable reference constant is never claimed");
    }
    let valtree =
        constant_function(shared_unit, ConstValue::struct_scalar_fields_ref("test::Good", vec![]));
    let other = FxHashSet::from_iter(["test::someone_else".to_string()]);
    let (_, sites) = lower(&valtree, Some(&other));
    assert_eq!(sites.claim_count(), 0, "an unclean function claims nothing");
    let (module, sites) = lower(&valtree, None);
    let _ = undef_node(&module);
    assert_eq!(sites.claim_count(), 0, "the plain path claims nothing");
}

/// Trust (2026-11-07): the value carrier is held to trust-mc's contract shape, a
/// promoted borrow of a stateless ZST. A non-ZST pointee (`&Newtype(N)`), a unit
/// variant of an enum, an unstamped ADT and a name disagreement claim nothing.
#[test]
fn non_zst_unit_variant_unstamped_and_mismatched_constants_claim_no_value() {
    for (label, pointee, constant) in [
        (
            "non-ZST newtype",
            newtype(),
            ConstValue::struct_scalar_fields_ref("test::Newtype", vec![ConstValue::Uint(5, 32)]),
        ),
        (
            "unit variant",
            stamped(Ty::adt("test::E", vec![]), trust_types::AdtKind::Enum),
            ConstValue::unit_variant_ref("test::E", 1),
        ),
        (
            "unstamped ADT",
            Ty::adt("test::Good", vec![]),
            ConstValue::struct_scalar_fields_ref("test::Good", vec![]),
        ),
        (
            "name mismatch",
            unit_struct(),
            ConstValue::struct_scalar_fields_ref("test::Other", vec![]),
        ),
    ] {
        let func = constant_function(shared(pointee), constant);
        let (module, sites) = lower(&func, Some(&clean()));
        let _ = undef_node(&module);
        assert_eq!(sites.claim_count(), 0, "{label}: no value claim");
    }
}

#[test]
fn a_rewritten_value_site_withdraws_its_claim() {
    let func = constant_function(
        shared(unit_struct()),
        ConstValue::struct_scalar_fields_ref("test::Good", vec![]),
    );
    // Marker stripped.
    let (mut module, sites) = lower(&func, Some(&clean()));
    let (b, i) = undef_node(&module);
    module.functions[0].blocks[b].body[i]
        .proofs
        .retain(|proof| !matches!(proof, ProofAnnotation::FreshSymbolicHavoc));
    let reconciled = sites.reconcile(&module);
    assert!(reconciled.values.is_empty(), "an unmarked Undef is not the claimed site");
    assert_eq!(reconciled.withdrawn, 1);
    // Retyped.
    let (mut module, sites) = lower(&func, Some(&clean()));
    if let Inst::Undef { ty } = &mut module.functions[0].blocks[b].body[i].inst {
        *ty = TrustIrTy::U64;
    }
    assert!(sites.reconcile(&module).values.is_empty(), "a retyped site withdraws");
    // Duplicated.
    let (mut module, sites) = lower(&func, Some(&clean()));
    let node = module.functions[0].blocks[b].body[i].clone();
    module.functions[0].blocks[b].body.insert(i, node);
    assert!(sites.reconcile(&module).values.is_empty(), "an ambiguous definition withdraws");
    // Removed.
    let (mut module, sites) = lower(&func, Some(&clean()));
    module.functions[0].blocks[b].body.remove(i);
    assert!(sites.reconcile(&module).values.is_empty(), "a removed site withdraws");
}

#[test]
fn wave490_reconcile_empty_and_parameter_only_and_duplicate_defs_match_oracle() {
    // 1. Parameter-only claim (loads and values empty) skips block body scan while keeping param.
    let func = load_function(vec![shared(Ty::u32())], 1, Ty::u32());
    let (module, mut sites) = lower(&func, Some(&clean()));
    sites.functions[0].loads.clear();
    let param_only = sites.reconcile(&module);
    assert_eq!(param_only.parameters.len(), 1);
    assert!(param_only.loads.is_empty() && param_only.values.is_empty());
    assert_eq!(param_only.withdrawn, 0);

    // 2. Empty record followed by duplicate function record must still withdraw the duplicate's claims!
    let (module, mut dup_sites) = lower(&func, Some(&clean()));
    let second = LoweredFunctionSourceReferences {
        function: dup_sites.functions[0].function,
        def_path: dup_sites.functions[0].def_path.clone(),
        link_name: dup_sites.functions[0].link_name.clone(),
        parameters: std::mem::take(&mut dup_sites.functions[0].parameters),
        loads: std::mem::take(&mut dup_sites.functions[0].loads),
        values: std::mem::take(&mut dup_sites.functions[0].values),
    };
    dup_sites.functions.push(second);
    let reconciled_dup = dup_sites.reconcile(&module);
    assert!(reconciled_dup.is_empty());
    assert_eq!(reconciled_dup.withdrawn, 2);
}

fn empty_closure(name: &str) -> Ty {
    Ty::Closure { name: name.to_string(), upvars: vec![], call: None }
}

/// Trust (2026-11-10, EMPTY-CLOSURE-REF-VALUE-1): the extractor's promoted
/// `&{closure}` of an upvar-free closure (`apply(&|x| x / 2, 7)`) records one
/// VALUE claim for its stamped `Undef(Ptr)`: the carrier trust-mc's value-fact
/// contract names. Nothing about its pointee is recorded.
#[test]
fn promoted_empty_closure_reference_records_a_value_claim() {
    let closure = "test::use_apply::{closure#0}";
    let func =
        constant_function(shared(empty_closure(closure)), ConstValue::empty_closure_ref(closure));
    let (module, sites) = lower(&func, Some(&clean()));
    let reconciled = sites.reconcile(&module);
    assert_eq!(reconciled.withdrawn, 0);
    assert!(reconciled.parameters.is_empty() && reconciled.loads.is_empty(), "{reconciled:?}");
    assert_eq!(reconciled.values.len(), 1, "one value claim");
    let value = &reconciled.values[0];
    let node = &module.functions[0].blocks[value.block.index() as usize].body
        [value.instruction_index as usize];
    assert_eq!(node.results.as_slice(), [value.result]);
    assert!(matches!(node.inst, Inst::Undef { ty: TrustIrTy::Ptr }));
    assert!(node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc));
}

/// Trust (2026-11-10, EMPTY-CLOSURE-REF-VALUE-1): the closure carrier is held to
/// its own shape. An `OpaqueConst` at a closure reference type (the extractor
/// also spells unmodeled RUNTIME pointers that way), a closure WITH upvars, a
/// name disagreement, a closure carrier at a struct type, a `&mut`, and an
/// unclean or plain-path function claim nothing.
#[test]
fn opaque_capturing_mismatched_and_unclean_closure_references_claim_no_value() {
    let closure = "test::use_apply::{closure#0}";
    let capturing = Ty::Closure { name: closure.to_string(), upvars: vec![Ty::u32()], call: None };
    for (label, declared, constant) in [
        (
            "OpaqueConst at a closure type",
            shared(empty_closure(closure)),
            ConstValue::opaque_const(),
        ),
        ("capturing closure", shared(capturing), ConstValue::empty_closure_ref(closure)),
        (
            "name mismatch",
            shared(empty_closure("test::other::{closure#0}")),
            ConstValue::empty_closure_ref(closure),
        ),
        (
            "closure carrier at a struct type",
            shared(unit_struct()),
            ConstValue::empty_closure_ref(closure),
        ),
        (
            "struct carrier at a closure type",
            shared(empty_closure("test::Good")),
            ConstValue::struct_scalar_fields_ref("test::Good", vec![]),
        ),
    ] {
        let func = constant_function(declared, constant);
        let (module, sites) = lower(&func, Some(&clean()));
        let _ = undef_node(&module);
        assert_eq!(sites.claim_count(), 0, "{label}: no value claim");
    }
    let mutable = constant_function(
        Ty::Ref { mutable: true, inner: Box::new(empty_closure(closure)) },
        ConstValue::empty_closure_ref(closure),
    );
    if let Ok((_, sites)) = lower_to_trust_ir_functions_with_test_source_reference_sites(
        "source_reference_sites",
        std::slice::from_ref(&mutable),
        Some(&clean()),
    ) {
        assert_eq!(sites.claim_count(), 0, "a mutable reference constant is never claimed");
    }
    let valtree =
        constant_function(shared(empty_closure(closure)), ConstValue::empty_closure_ref(closure));
    let other = FxHashSet::from_iter(["test::someone_else".to_string()]);
    let (_, sites) = lower(&valtree, Some(&other));
    assert_eq!(sites.claim_count(), 0, "an unclean function claims nothing");
    let (module, sites) = lower(&valtree, None);
    let _ = undef_node(&module);
    assert_eq!(sites.claim_count(), 0, "the plain path claims nothing");
}

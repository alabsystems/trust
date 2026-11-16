//! Unit tests for the D5-C borrow-provenance ledger: the AND-composition per key,
//! and conjunct (3), asked on the lowered module (`ReachScope`).

use super::BorrowProvenanceLedger;

// Sorted right after, so the set's iteration order cannot reach an assertion.
#[allow(rustc::potential_query_instability)]
fn set_of(ledger: BorrowProvenanceLedger) -> Vec<String> {
    let mut paths: Vec<String> = ledger.into_clean_set_and_reach_scope().0.into_iter().collect();
    paths.sort();
    paths
}

#[test]
fn clean_root_and_clean_mono_member_are_both_stamped() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::rem_ref", "root", true);
    ledger.record_mono_member("<&u32 as core::ops::arith::Rem<u32>>::rem", true);
    assert_eq!(
        set_of(ledger),
        vec!["<&u32 as core::ops::arith::Rem<u32>>::rem".to_string(), "c::rem_ref".to_string()]
    );
}

/// The clean set carries (1) and (2) only: an unclean B-lane member no longer
/// removes a clean one at the LEDGER. Conjunct (3) is the module-level pass, and
/// `scoped_conjunct3_withholds_a_member_an_unclean_body_calls` pins the `xchain`
/// shape there.
#[test]
fn an_unclean_mono_member_does_not_touch_the_clean_set() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.record_mono_member("bpdep::pass_transmuted", false);
    ledger.record_mono_member("bpdep::load_ref", true);
    assert_eq!(set_of(ledger), vec!["bpdep::load_ref".to_string(), "c::f".to_string()]);
}

/// A foreign `DefId`-lane body that fails the member rule is NOT attested as a
/// caller, although its own (1)-clean stamp is unchanged.
#[test]
fn an_unscreened_foreign_body_seeds_the_reach_pass() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record("dep::derived", "defid-member", true);
    ledger.note_foreign_body("dep::derived", false);
    ledger.record_mono_member("bpdep::load_ref", true);
    let (clean, scope) = ledger.into_clean_set_and_reach_scope();
    assert!(clean.contains("dep::derived") && clean.contains("bpdep::load_ref"));
    let mut module =
        module_of(vec![func(0, vec![]), func(1, vec![call(2)]), func(2, vec![stamped_load()])]);
    assert_eq!(
        scope.strip_unattested_reach(
            &mut module,
            &["c::f", "dep::derived", "bpdep::load_ref"],
            &mut no_sites()
        ),
        1
    );
}

/// A key recorded twice is clean only if every body under it is clean, in
/// either order.
#[test]
fn a_key_recorded_unclean_anywhere_is_absent() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("k", "defid-member", true);
    ledger.record("k", "cmp-sublane", false);
    ledger.record("j", "cmp-sublane", false);
    ledger.record("j", "defid-member", true);
    assert!(set_of(ledger).is_empty());
}

#[test]
fn a_clean_foreign_body_withholds_nothing() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.note_foreign_body("dep::derived", true);
    ledger.record_mono_member("bpdep::pass_through", true);
    ledger.record_mono_member("bpdep::load_ref", true);
    assert_eq!(
        set_of(ledger),
        vec!["bpdep::load_ref".to_string(), "bpdep::pass_through".to_string()]
    );
}

// ---- conjunct (3) on the lowered module (2026-09-27) ----

use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTyId, Function, Inst, InstrNode, Module,
    ProofAnnotation, Ty, ValueId,
};

use super::ReachScope;

fn func(index: u32, body: Vec<InstrNode>) -> Function {
    let mut function =
        Function::new(FuncId::new(index), format!("f{index}"), FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body = body;
    function.blocks.push(block);
    function
}

fn call(callee: u32) -> InstrNode {
    InstrNode::new(Inst::Call { callee: FuncId::new(callee), args: vec![] })
}

/// The `Load` the bridge stamps in a clean body: the thing the pass must keep or strip.
fn stamped_load() -> InstrNode {
    InstrNode::new(Inst::Load { ty: Ty::U32, ptr: ValueId::new(0), volatile: false, align: None })
        .with_proof(ProofAnnotation::ValidBorrow)
}

fn module_of(functions: Vec<Function>) -> Module {
    let mut module = Module::new("m");
    for function in functions {
        module.try_add_function(function).expect("distinct test function names");
    }
    module
}

fn stamped(module: &Module, index: usize) -> bool {
    module.functions[index]
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| node.proofs.contains(&ProofAnnotation::ValidBorrow))
}

fn scope_of(ledger: BorrowProvenanceLedger) -> ReachScope {
    ledger.into_clean_set_and_reach_scope().1
}

/// The side table of a hand-built module: no lowering recorded a claim in it.
fn no_sites() -> trust_ir_bridge::LoweredSourceReferenceSites {
    trust_ir_bridge::LoweredSourceReferenceSites::default()
}

/// `fn <name>(p: &u32) -> u32 { *p }` under `def_path`.
fn load_ref_function(name: &str, def_path: &str) -> trust_types::VerifiableFunction {
    let reference =
        trust_types::Ty::Ref { mutable: false, inner: Box::new(trust_types::Ty::u32()) };
    trust_types::VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
        span: trust_types::SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::u32(), name: None },
                trust_types::LocalDecl { index: 1, ty: reference, name: Some("p".into()) },
            ],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![trust_types::Statement::Assign {
                    place: trust_types::Place::local(0),
                    rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(
                        trust_types::Place {
                            local: 1,
                            projections: vec![trust_types::Projection::Deref],
                        },
                    )),
                    span: trust_types::SourceSpan::default(),
                }],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 1,
            return_ty: trust_types::Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Trust (C1, 2026-11-06): conjunct (3) withdraws EVERY source reference claim
/// (the parameter claim too, which no `ValidBorrow` stamp carries) of each member
/// it withholds, and only theirs. The table is a real one, recorded by the
/// compiler-context lowering of the same module.
#[test]
fn scoped_conjunct3_withdraws_the_source_reference_claims_of_a_withheld_member() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    // Clean under (1) and (2), so the bridge stamps and records it; but its foreign
    // body fails the member rule, so it is no attested caller and seeds the taint.
    ledger.record_mono_member("dep::withheld", true);
    ledger.note_foreign_body("dep::withheld", false);
    ledger.record_mono_member("dep::kept", true);
    let (clean, scope) = ledger.into_clean_set_and_reach_scope();
    let functions = vec![
        load_ref_function("f", "c::f"),
        load_ref_function("withheld", "dep::withheld"),
        load_ref_function("kept", "dep::kept"),
    ];
    let empty = rustc_data_structures::fx::FxHashSet::<String>::default();
    let (mut module, mut sites) =
        trust_ir_bridge::lower_to_trust_ir_functions_with_instance_hypothesis_context(
            "c::f",
            &functions,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &empty,
            &trust_ir_bridge::CallReachWithdrawals::default(),
            Some(&clean),
            &trust_ir_bridge::InstanceHypothesisSites::default(),
            &trust_ir_bridge::CompilerAllocGrowPins::default(),
            &empty,
        )
        .expect("the fixture lowers");
    assert_eq!(sites.claim_count(), 6, "each clean function claims its parameter and its load");
    let paths = ["c::f", "dep::withheld", "dep::kept"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut sites), 1);
    assert!(!stamped(&module, 1), "the withheld member loses its stamp");
    assert!(stamped(&module, 0) && stamped(&module, 2));
    let mut claimed: Vec<&str> = sites.claimed_def_paths().collect();
    claimed.sort_unstable();
    assert_eq!(claimed, vec!["c::f", "dep::kept"], "only the withheld member's claims go");
    let reconciled = sites.reconcile(&module);
    assert_eq!(reconciled.parameters.len(), 2);
    assert_eq!(reconciled.loads.len(), 2);
    assert!(
        reconciled.parameters.iter().all(|parameter| parameter.function.index() != 1),
        "{reconciled:?}"
    );
    assert!(reconciled.loads.iter().all(|load| load.function.index() != 1), "{reconciled:?}");
}

/// `i04`: the unclean allocation bodies `collect` pulls in reach nothing, so the
/// operator member reached only through the local closure KEEPS its stamp. The
/// bundle-wide rule withholds it (`an_unclean_mono_member_withholds_every_mono_stamp`).
#[test]
fn scoped_conjunct3_keeps_a_member_no_unclean_body_reaches() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::evens", "root", true);
    ledger.note_local_body("c::evens");
    ledger.record("c::evens::{closure#0}", "defid-member", true);
    ledger.note_local_body("c::evens::{closure#0}");
    ledger.record_mono_member("rem", true);
    ledger.record_mono_member("RawVecInner::current_memory", false);
    let scope = scope_of(ledger);
    let mut module = module_of(vec![
        func(0, vec![call(1)]),
        func(1, vec![call(2)]),
        func(2, vec![stamped_load()]),
        func(3, vec![]),
    ]);
    let paths = ["c::evens", "c::evens::{closure#0}", "rem", "RawVecInner::current_memory"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 0);
    assert!(stamped(&module, 2));
}

/// `xchain`, the shape conjunct 3 exists for: the unclean body CALLS the member.
#[test]
fn scoped_conjunct3_withholds_a_member_an_unclean_body_calls() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("bpdep::pass_transmuted", false);
    ledger.record_mono_member("bpdep::load_ref", true);
    let scope = scope_of(ledger);
    let mut module = module_of(vec![
        func(0, vec![call(1)]),
        func(1, vec![call(2)]),
        func(2, vec![stamped_load()]),
    ]);
    let paths = ["c::f", "bpdep::pass_transmuted", "bpdep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
    assert!(!stamped(&module, 2));
}

/// The taint is transitive: a CLEAN member between the fabricator and the loader
/// does not launder the reference (it may just pass its parameter on).
#[test]
fn scoped_taint_is_transitive_through_a_clean_member() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::fabricate_and_pass", false);
    ledger.record_mono_member("dep::pass_through", true);
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let mut module = module_of(vec![
        func(0, vec![call(1)]),
        func(1, vec![call(2)]),
        func(2, vec![stamped_load(), call(3)]),
        func(3, vec![stamped_load()]),
    ]);
    let paths = ["c::f", "dep::fabricate_and_pass", "dep::pass_through", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 2);
    assert!(!stamped(&module, 2) && !stamped(&module, 3));
}

/// Attestation is POSITIVE: a module function the ledger never recorded seeds.
#[test]
fn scoped_an_unrecorded_body_seeds() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let mut module =
        module_of(vec![func(0, vec![]), func(1, vec![call(2)]), func(2, vec![stamped_load()])]);
    let paths = ["c::f", "never::recorded", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
}

/// One indirect call in the taint could reach any member.
#[test]
fn scoped_an_indirect_call_in_the_taint_strips_every_member() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::unclean", false);
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let indirect = InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: FuncTyId::new(0),
        args: vec![],
        calling_conv: CallingConv::default(),
    });
    let mut module = module_of(vec![
        func(0, vec![call(2)]),
        func(1, vec![indirect]),
        func(2, vec![stamped_load()]),
    ]);
    let paths = ["c::f", "dep::unclean", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
}

/// A function REFERENCE is an edge, not only a call: the fabricator may hand the
/// member to code that calls it with the fabricated reference.
#[test]
fn scoped_a_function_reference_constant_is_an_edge() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::unclean", false);
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let fn_ref = InstrNode::new(Inst::Const {
        ty: Ty::Func(FuncTyId::new(0)),
        value: Constant::FnDef(FuncId::new(2)),
    })
    .with_result(ValueId::new(1));
    let mut module = module_of(vec![
        func(0, vec![call(2)]),
        func(1, vec![fn_ref]),
        func(2, vec![stamped_load()]),
    ]);
    let paths = ["c::f", "dep::unclean", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
}

/// If the member list does not index the module exactly, fall back to stripping
/// every member: the bundle-wide behaviour.
#[test]
fn scoped_a_shape_mismatch_strips_every_member() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let mut module =
        module_of(vec![func(0, vec![call(1)]), func(1, vec![stamped_load()]), func(2, vec![])]);
    let paths = ["c::f", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
}

/// Two module functions under ONE attested `def_path`: the ledger cannot say which
/// body it attested, so both seed (adversarial review C2).
#[test]
fn scoped_a_def_path_naming_two_module_functions_is_not_attested() {
    let mut ledger = BorrowProvenanceLedger::default();
    ledger.record("c::f", "root", true);
    ledger.note_local_body("c::f");
    ledger.record_mono_member("dep::twin", true);
    ledger.record_mono_member("dep::load_ref", true);
    let scope = scope_of(ledger);
    let mut module = module_of(vec![
        func(0, vec![]),
        func(1, vec![]),
        func(2, vec![call(3)]),
        func(3, vec![stamped_load()]),
    ]);
    let paths = ["c::f", "dep::twin", "dep::twin", "dep::load_ref"];
    assert_eq!(scope.strip_unattested_reach(&mut module, &paths, &mut no_sites()), 1);
    assert!(!stamped(&module, 3));
}

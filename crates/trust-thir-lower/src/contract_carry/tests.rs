// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.5 (staged) — the contract carry, its installer and the staged rung.
//!
//! The modules below are MODELS of the direct lowering of the two-language
//! fixtures `tests/two-language-programs/ir-ta01_rust_contracts/p01_rust_contracts.rs`
//! (`clamp_add` with `requires x <= 1000`, `requires y <= 1000`,
//! `ensures result == x + y`; `countdown` with `decreases n`; `program`) and
//! `ir-ta02_rust_loop_invariant/p02_rust_loop_invariant.rs` (`sum_below` with
//! `requires n <= 1000` and a `while` loop carrying `invariant i <= n`,
//! `decreases n - i`), with the registry records the query + lowering hand the
//! installer. They are built with the same field vocabulary the producer uses
//! (entry param `i` IS `ValueId(i)`; a contract loop's header carries the
//! name-sorted source bindings as its parameter prefix). The REAL producer's
//! output on p01/p02 is measured by the stage-1 run-make
//! `tests/run-make/trust-ir-contract-carry-shadow`.
//!
//! Every negative twin is ONE mutation of a passing fixture, asserting its
//! specific refusal.

use std::collections::BTreeMap;

use rustc_middle::mir::Local;
use rustc_middle::mir::trust_contract::{
    TrustContractPredicateKind, TrustContractProposition as P, TrustContractPropositionDomain as D,
};
use rustc_span::Symbol;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, RejectingModuleProofAuthority};
use trust_ir::{
    BlockId, FuncId, Module, ObligationKind, Producer, ProofCertificate, ProofEvidence, ProofId,
    ProofStatus, Ty, ValueId,
};
use trust_ir_build::{ModuleBuilder, ModuleSet};

use super::*;
use crate::direct_obligations::inventory_errors_at_tier;

const CRATE: &str = "p01_rust_contracts";
const U64: D = D::MachineInt { width: 64, signed: false };

// ================================ fixtures ==================================

fn var(name: &str, domain: D) -> P {
    P::Var { name: Symbol::intern(name), domain }
}

fn b(p: P) -> Box<P> {
    Box::new(p)
}

fn typed(text: &str, proposition: P) -> TrustContractPredicateKind {
    TrustContractPredicateKind::Typed {
        text: Symbol::intern(&format!("__trust_lowered_compiler_contract__:{text}")),
        proposition,
    }
}

fn fn_clause(role: ClauseRole, ordinal: u32, predicate: TrustContractPredicateKind) -> CarryClause {
    CarryClause { role, ordinal, loop_key: None, predicate, place_bindings: None }
}

fn param(ir_index: u32, name: &str, hir_local_id: u32) -> CarryParam {
    CarryParam {
        ir_index,
        name: name.to_string(),
        hir_local_id,
        mutable: false,
        reference: ParamReference::ByValue,
    }
}

fn body(def_index: u32, def_path: &str, arity: u32, params: Vec<CarryParam>) -> ContractBodyRecord {
    ContractBodyRecord {
        def_index,
        def_path: def_path.to_string(),
        ir_param_count: Some(arity),
        params,
        binding_refusal: None,
        clauses: Vec::new(),
        loop_headers: Vec::new(),
        refusal: None,
    }
}

fn u64_arg(value: i128) -> InterpretValue {
    InterpretValue::int(Ty::U64, value).expect("a u64 argument")
}

fn run(module: &Module, func: FuncId, args: Vec<InterpretValue>) -> u128 {
    let outcome =
        Interpreter::with_module(module).execute_func(func, args).unwrap_or_else(|error| {
            panic!("the reference interpreter runs f{}: {error:?}", func.index())
        });
    match &outcome.returns[..] {
        [InterpretValue { kind: InterpretValueKind::Int(int), .. }] => int.raw,
        other => panic!("one integer result, got {other:?}"),
    }
}

/// p01 as the direct lane lowers it: `clamp_add` (f0, def 3), `countdown`
/// (f1, def 4), `program` (f2, def 5), every function `Producer::TRust`.
fn p01_module() -> (Module, Vec<(u32, FuncId)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(CRATE, crate::drop_glue_oracle::oracle_target());
    mb.set_default_producer(Producer::TRust);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let mut fb = mb.function("p01_rust_contracts::clamp_add", binary);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let sum = fb.add(Ty::U64, x, y);
    fb.ret(vec![sum]);
    let clamp_add = fb.build();

    let countdown_id = mb.peek_next_func_id().expect("a fresh FuncId");
    let mut fb = mb.function("p01_rust_contracts::countdown", unary);
    let entry = fb.create_block();
    let recurse = fb.create_block();
    let base = fb.create_block();
    let join = fb.create_block();
    let n = fb.add_block_param(entry, Ty::U64);
    let joined = fb.add_block_param(join, Ty::U64);
    fb.switch_to_block(entry);
    let zero = fb.uconst(Ty::U64, 0);
    let positive = fb.icmp(trust_ir::inst::ICmpOp::Ugt, Ty::U64, n, zero);
    fb.condbr(positive, recurse, vec![], base, vec![]);
    fb.switch_to_block(recurse);
    let one = fb.uconst(Ty::U64, 1);
    let less = fb.sub(Ty::U64, n, one);
    let inner = fb.call(countdown_id, vec![less]);
    fb.br(join, vec![inner]);
    fb.switch_to_block(base);
    let seven = fb.uconst(Ty::U64, 7);
    fb.br(join, vec![seven]);
    fb.switch_to_block(join);
    fb.ret(vec![joined]);
    let countdown = fb.build();
    assert_eq!(countdown, countdown_id);

    let mut fb = mb.function("p01_rust_contracts::program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let forty = fb.uconst(Ty::U64, 40);
    let two = fb.uconst(Ty::U64, 2);
    let added = fb.call(clamp_add, vec![forty, two]);
    let five = fb.uconst(Ty::U64, 5);
    let counted = fb.call(countdown, vec![five]);
    let total = fb.add(Ty::U64, added, counted);
    fb.ret(vec![total]);
    let program = fb.build();

    (mb.build().expect("p01 builds"), vec![(3, clamp_add), (4, countdown), (5, program)])
}

/// The query records of p01 (native clauses: the literal re-parses as `Int`;
/// `result` is spelled `_0`).
fn p01_registry() -> ContractCarryRegistry {
    let mut clamp = body(3, "clamp_add", 2, vec![param(0, "x", 2), param(1, "y", 4)]);
    clamp.clauses = vec![
        fn_clause(
            ClauseRole::Requires,
            0,
            typed("x <= 1000", P::Le(b(var("x", U64)), b(P::Int(1000)))),
        ),
        fn_clause(
            ClauseRole::Requires,
            1,
            typed("y <= 1000", P::Le(b(var("y", U64)), b(P::Int(1000)))),
        ),
        fn_clause(
            ClauseRole::Ensures,
            2,
            typed(
                "_0 == x + y",
                P::Eq(b(var("_0", U64)), b(P::Add(b(var("x", U64)), b(var("y", U64))))),
            ),
        ),
    ];
    let mut countdown = body(4, "countdown", 1, vec![param(0, "n", 2)]);
    countdown.clauses = vec![fn_clause(ClauseRole::Decreases, 0, typed("n", var("n", U64)))];
    let mut registry = ContractCarryRegistry::default();
    registry.insert(clamp);
    registry.insert(countdown);
    registry
}

const P02_HEADER: u32 = 1;

/// p02 as the direct lane lowers it: `sum_below` (f0, def 7) with the
/// `while` loop's header b1 carrying `[i, n]` (the name-sorted source
/// bindings of its clauses) then `s`, and `program` (f1, def 8).
fn p02_module() -> (Module, Vec<(u32, FuncId)>) {
    let mut mb = ModuleBuilder::new_with_target_info(
        "p02_rust_loop_invariant",
        crate::drop_glue_oracle::oracle_target(),
    );
    mb.set_default_producer(Producer::TRust);
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    let mut fb = mb.function("p02_rust_loop_invariant::sum_below", unary);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body_block = fb.create_block();
    let exit = fb.create_block();
    assert_eq!(header, BlockId::new(P02_HEADER));
    let n = fb.add_block_param(entry, Ty::U64);
    let i = fb.add_block_param(header, Ty::U64);
    let n_h = fb.add_block_param(header, Ty::U64);
    let s = fb.add_block_param(header, Ty::U64);
    fb.switch_to_block(entry);
    let zero_i = fb.uconst(Ty::U64, 0);
    let zero_s = fb.uconst(Ty::U64, 0);
    fb.br(header, vec![zero_i, n, zero_s]);
    fb.switch_to_block(header);
    let more = fb.icmp(trust_ir::inst::ICmpOp::Ult, Ty::U64, i, n_h);
    fb.condbr(more, body_block, vec![], exit, vec![]);
    fb.switch_to_block(body_block);
    let s_next = fb.add(Ty::U64, s, i);
    let one = fb.uconst(Ty::U64, 1);
    let i_next = fb.add(Ty::U64, i, one);
    fb.br(header, vec![i_next, n_h, s_next]);
    fb.switch_to_block(exit);
    fb.ret(vec![s]);
    let sum_below = fb.build();

    let mut fb = mb.function("p02_rust_loop_invariant::program", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let ten = fb.uconst(Ty::U64, 10);
    let result = fb.call(sum_below, vec![ten]);
    fb.ret(vec![result]);
    let program = fb.build();

    let module = mb.build().expect("p02 builds");
    let params: Vec<ValueId> =
        module.functions[0].blocks[1].params.iter().map(|(value, _)| *value).collect();
    assert_eq!(params, vec![i, n_h, s]);
    (module, vec![(7, sum_below), (8, program)])
}

const HIR_N: u32 = 2;
const HIR_I: u32 = 9;

fn p02_header(module: &Module) -> ContractLoopHeader {
    ContractLoopHeader {
        hir_local_id: 30,
        header: BlockId::new(P02_HEADER),
        pre_header: BlockId::new(0),
        header_params: module.functions[0].blocks[1].params.iter().map(|(v, _)| *v).collect(),
        plan_bindings: vec![("i".to_string(), HIR_I), ("n".to_string(), HIR_N)],
    }
}

fn loop_clause(
    role: ClauseRole,
    ordinal: u32,
    predicate: TrustContractPredicateKind,
) -> CarryClause {
    CarryClause {
        role,
        ordinal,
        loop_key: Some(LoopKey { index: 0, hir_local_id: 30 }),
        predicate,
        place_bindings: Some(vec![("i".to_string(), HIR_I), ("n".to_string(), HIR_N)]),
    }
}

fn p02_registry(module: &Module) -> ContractCarryRegistry {
    let mut sum = body(7, "sum_below", 1, vec![param(0, "n", HIR_N)]);
    sum.clauses = vec![
        fn_clause(
            ClauseRole::Requires,
            0,
            typed("n <= 1000", P::Le(b(var("n", U64)), b(P::Int(1000)))),
        ),
        loop_clause(
            ClauseRole::LoopInvariant,
            0,
            typed("i <= n", P::Le(b(var("i", U64)), b(var("n", U64)))),
        ),
        loop_clause(
            ClauseRole::LoopDecreases,
            1,
            typed("n - i", P::Sub(b(var("n", U64)), b(var("i", U64)))),
        ),
    ];
    sum.loop_headers = vec![p02_header(module)];
    let mut registry = ContractCarryRegistry::default();
    registry.insert(sum);
    registry
}

fn install(
    module: &mut Module,
    assigned: &[(u32, FuncId)],
    registry: ContractCarryRegistry,
) -> (ContractInstallOutcome, Vec<String>) {
    let mut errors = Vec::new();
    let outcome = install_contract_obligations(module, CRATE, assigned, registry, &mut errors);
    (outcome, errors)
}

fn installed_p01() -> (Module, Vec<(u32, FuncId)>) {
    let (mut module, assigned) = p01_module();
    let (outcome, errors) = install(&mut module, &assigned, p01_registry());
    assert!(errors.is_empty(), "{errors:#?}");
    assert_eq!(outcome.rows_installed, 4, "{outcome:#?}");
    (module, assigned)
}

fn installed_p02() -> (Module, Vec<(u32, FuncId)>) {
    let (mut module, assigned) = p02_module();
    let registry = p02_registry(&module);
    let (outcome, errors) = install(&mut module, &assigned, registry);
    assert!(errors.is_empty(), "{errors:#?}");
    assert_eq!(outcome.rows_installed, 3, "{outcome:#?}");
    (module, assigned)
}

fn binding(sort: ClauseSort, place: ClausePlace) -> ClauseBinding {
    ClauseBinding { sort, place }
}

fn bv64(place: ClausePlace) -> ClauseBinding {
    binding(ClauseSort::BitVec(64), place)
}

/// The three entry points the acceptance names, all at the pinned trust-ir.
fn assert_validates(module: &Module) {
    let plain = trust_ir_build::validate_module(module);
    assert!(plain.is_empty(), "validate_module: {plain:#?}");
    let authority =
        trust_ir_build::validate_module_with_authority(module, &RejectingModuleProofAuthority);
    assert!(authority.is_empty(), "validate_module_with_authority: {authority:#?}");
    let set = ModuleSet::new([]);
    let linked =
        trust_ir_build::validate_linked_module(module, &set, &RejectingModuleProofAuthority);
    assert!(linked.is_ok(), "validate_linked_module: {:#?}", linked.errors());
}

/// The carried summaries and rows survive the two artifact encodings the
/// finalizer writes: the binary `.trust-ir.bin` round-trips them exactly, and
/// the canonical text companion reports no loss (WS4.4's F-064/F-071 carriers
/// are at the pin), so the flip needs no lossy-companion refusal.
fn assert_artifacts_carry_it(module: &Module) {
    let bytes = trust_ir::binary::serialize_module(module).expect("the installed module encodes");
    let decoded =
        trust_ir::binary::deserialize_module(&bytes).expect("the installed module decodes");
    assert_eq!(decoded.proof_obligations, module.proof_obligations, "binary rows");
    let summaries = |m: &Module| m.functions.iter().map(|f| f.summary.clone()).collect::<Vec<_>>();
    assert_eq!(summaries(&decoded), summaries(module), "binary summaries");
    let losses = trust_ir::text_loss::text_losses(module);
    assert!(losses.is_empty(), "the text companion would drop: {losses:#?}");
}

/// The staged rung admits it; the LIVE tier (the one the finalizer runs) does
/// not — this second half pins that no contract row is born live.
fn assert_staged_only(module: &Module) {
    let staged = contract_bound_inventory_errors(module);
    assert!(staged.is_empty(), "the staged contract-bound rung admits the carry: {staged:#?}");
    let live =
        inventory_errors_at_tier(module, crate::crate_module::DIRECT_OBLIGATION_CAPABILITY.tier());
    assert!(!live.is_empty(), "the LIVE tier must refuse every contract row: zero rows born live");
    assert_eq!(
        crate::crate_module::DIRECT_OBLIGATION_CAPABILITY.marker(),
        "obligation-bearing-pending-v2",
        "the capability flip is the owner's signed act (DG-60), never this module's"
    );
}

fn contract_rows(module: &Module) -> Vec<&ProofObligation> {
    module
        .proof_obligations
        .iter()
        .filter(|row| row.source.as_ref().is_some_and(|s| s.source_id == CONTRACT_SOURCE_ID))
        .collect()
}

// ================================ positives =================================

#[test]
fn p01_summary_carries_typed_bindings_and_pending_formula_rows() {
    rustc_span::create_default_session_globals_then(|| {
        let (module, assigned) = installed_p01();
        let clamp = &module.functions[0];
        let summary = clamp.summary.as_ref().expect("clamp_add carries a summary");
        assert!(!summary.proved, "a carried summary is never proved");
        assert!(summary.backed_by.is_none());
        assert_eq!(summary.params, vec!["x".to_string(), "y".to_string()]);
        assert_eq!(summary.requires.len(), 2);
        assert_eq!(summary.ensures.len(), 1);
        assert!(summary.decreases.is_empty());

        let requires_x = &summary.requires[0];
        assert_eq!(requires_x.schema, CONTRACT_CLAUSE_SCHEMA);
        assert_eq!(
            requires_x.payload,
            "{\"le\":[{\"var\":{\"name\":\"x\",\"domain\":\"MachineInt { width: 64, signed: \
             false }\"}},{\"int\":\"1000\"}]}"
        );
        assert_eq!(
            requires_x.bindings,
            vec![("x".to_string(), bv64(ClausePlace::Param { index: 0 }))]
        );
        assert_eq!(requires_x.smtlib.as_deref(), Some("(bvule x (_ bv1000 64))"));
        assert_eq!(requires_x.sort.as_deref(), Some("Bool"));
        assert_eq!(
            summary.requires[1].bindings,
            vec![("y".to_string(), bv64(ClausePlace::Param { index: 1 }))]
        );

        let ensures = &summary.ensures[0];
        assert_eq!(ensures.schema, CONTRACT_CLAUSE_SCHEMA);
        assert_eq!(
            ensures.bindings,
            vec![
                ("_0".to_string(), bv64(ClausePlace::ResultSlot { index: 0 })),
                ("x".to_string(), bv64(ClausePlace::Param { index: 0 })),
                ("y".to_string(), bv64(ClausePlace::Param { index: 1 })),
            ]
        );
        assert_eq!(
            ensures.smtlib, None,
            "spec `+` is mathematical; a wrapping bvadd would state another formula"
        );

        let countdown = module.functions[1].summary.as_ref().expect("countdown's decreases");
        assert_eq!(countdown.decreases.len(), 1);
        assert_eq!(
            countdown.decreases[0].bindings,
            vec![("n".to_string(), bv64(ClausePlace::Param { index: 0 }))]
        );
        assert_eq!(countdown.decreases[0].smtlib, None, "a bit-vector measure has no signed order");
        assert!(module.functions[2].summary.is_none(), "program has no contract");

        let rows = contract_rows(&module);
        let kinds: Vec<_> = rows.iter().map(|row| (row.kind.clone(), row.function)).collect();
        assert_eq!(
            kinds,
            vec![
                (ObligationKind::Precondition, Some(assigned[0].1)),
                (ObligationKind::Precondition, Some(assigned[0].1)),
                (ObligationKind::Postcondition, Some(assigned[0].1)),
                (ObligationKind::Termination, Some(assigned[1].1)),
            ]
        );
        for row in &rows {
            assert_eq!(row.status, ProofStatus::Pending);
            assert!(row.site.is_none(), "a function clause is not sited");
            assert!(row.source.as_ref().unwrap().public.is_none());
            let formula = row.formula.as_ref().expect("every contract row carries its formula");
            let summary = module
                .functions
                .iter()
                .find(|f| Some(f.id) == row.function)
                .and_then(|f| f.summary.as_ref())
                .unwrap();
            assert!(
                summary.requires.contains(formula)
                    || summary.ensures.contains(formula)
                    || summary.decreases.contains(formula),
                "a row states exactly one clause of its summary"
            );
        }
        assert_eq!(
            rows[2].source.as_ref().unwrap().assertion_id,
            "p01_rust_contracts::clamp_add#ensures#c2"
        );

        assert_validates(&module);
        assert_staged_only(&module);
        assert_artifacts_carry_it(&module);

        assert_eq!(run(&module, assigned[0].1, vec![u64_arg(40), u64_arg(2)]), 42);
        assert_eq!(run(&module, assigned[2].1, vec![]), 49, "p01's EXPECT: 49");
    });
}

#[test]
fn p02_loop_rows_are_sited_at_the_recorded_header_and_bind_its_parameters() {
    rustc_span::create_default_session_globals_then(|| {
        let (module, assigned) = installed_p02();
        let sum = &module.functions[0];
        let summary = sum.summary.as_ref().expect("sum_below's requires");
        assert_eq!(summary.requires.len(), 1);
        assert_eq!(
            summary.requires[0].bindings,
            vec![("n".to_string(), bv64(ClausePlace::Param { index: 0 }))]
        );
        let header = &sum.blocks[P02_HEADER as usize];
        let (i, n) = (header.params[0].0, header.params[1].0);

        let rows = contract_rows(&module);
        assert_eq!(rows.len(), 3);
        let invariant = rows[1];
        assert_eq!(invariant.kind, ObligationKind::LoopInvariant);
        let site = invariant.site.expect("a loop row is sited");
        assert_eq!((site.function, site.block, site.inst_index), (assigned[0].1, header.id, 0));
        let formula = invariant.formula.as_ref().unwrap();
        assert_eq!(formula.schema, CONTRACT_CLAUSE_SCHEMA);
        assert_eq!(
            formula.bindings,
            vec![
                ("i".to_string(), bv64(ClausePlace::Value(i))),
                ("n".to_string(), bv64(ClausePlace::Value(n))),
            ]
        );
        assert_eq!(formula.smtlib.as_deref(), Some("(bvule i n)"));

        let measure = rows[2];
        assert_eq!(measure.kind, ObligationKind::Termination);
        assert_eq!(measure.site.map(|s| s.block), Some(header.id));
        assert_eq!(measure.formula.as_ref().unwrap().smtlib, None);

        assert_validates(&module);
        assert_staged_only(&module);
        assert_artifacts_carry_it(&module);
        assert_eq!(run(&module, assigned[0].1, vec![u64_arg(10)]), 45);
        assert_eq!(run(&module, assigned[1].1, vec![]), 45, "p02's EXPECT: 45");
    });
}

#[test]
fn clause_payload_is_the_disclosure_proposition_bytes() {
    rustc_span::create_default_session_globals_then(|| {
        let registry = p01_registry();
        let clause = &registry.bodies[&3].clauses[0];
        let TrustContractPredicateKind::Typed { proposition, .. } = &clause.predicate else {
            unreachable!()
        };
        let disclosure = crate::contract_render::render_predicate(&clause.predicate);
        let carried = crate::contract_render::render_proposition(proposition);
        assert!(
            disclosure.ends_with(&format!(",\"proposition\":{carried}}}}}")),
            "one renderer, one spelling: {disclosure}"
        );
    });
}

// ================================ negative twins ============================

#[test]
fn opaque_unsupported_and_mir_local_clauses_are_carried_unbindable_never_dropped() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, assigned) = p01_module();
        let mut registry = p01_registry();
        let clamp = registry.bodies.get_mut(&3).unwrap();
        clamp.clauses[0].predicate =
            TrustContractPredicateKind::Opaque { text: Symbol::intern("x <= LIMIT") };
        clamp.clauses[1].predicate =
            TrustContractPredicateKind::Unsupported { reason: Symbol::intern("no lane") };
        clamp.clauses[2].predicate =
            TrustContractPredicateKind::MirLocal { local: Local::from_u32(3) };
        let (outcome, errors) = install(&mut module, &assigned, registry);
        assert!(errors.is_empty(), "{errors:#?}");
        assert_eq!(outcome.clauses_opaque, 3);
        let summary = module.functions[0].summary.as_ref().unwrap();
        assert!(!summary.proved);
        let expected = [
            "{\"opaque\":{\"text\":\"x <= LIMIT\"}}",
            "{\"unsupported\":{\"reason\":\"no lane\"}}",
        ];
        for (clause, payload) in summary.requires.iter().zip(expected) {
            assert_eq!(clause.schema, CONTRACT_OPAQUE_SCHEMA);
            assert_eq!(clause.payload, payload);
            assert!(clause.bindings.is_empty(), "EMPTY bindings spell UNBINDABLE");
            assert!(clause.smtlib.is_none());
        }
        assert_eq!(summary.ensures[0].payload, "{\"mir_local\":{\"local\":3}}");
        assert_eq!(contract_rows(&module).len(), 4, "every authored clause still has its row");
        assert_validates(&module);
        assert_staged_only(&module);
    });
}

#[test]
fn a_hand_edited_proved_true_is_refused_by_the_staged_rung() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, _) = installed_p01();
        module.functions[0].summary.as_mut().unwrap().proved = true;
        let errors = contract_bound_inventory_errors(&module);
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(errors[0].contains(PROVED_FALSE_ONLY), "{}", errors[0]);
        assert!(errors[0].contains("contract-bound tier admits proved:false only"));
    });
}

#[test]
fn a_certificate_is_still_refused() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, _) = installed_p01();
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "hand".to_string(),
            evidence: ProofEvidence::Trusted("forged".to_string()),
            assurance: None,
        });
        let errors = contract_bound_inventory_errors(&module);
        assert!(
            errors.iter().any(|e| e.contains("certificates 1")),
            "the delegated obligation-bearing arm refuses every certificate: {errors:#?}"
        );
    });
}

#[test]
fn a_summary_on_a_declaration_is_refused_and_never_minted() {
    rustc_span::create_default_session_globals_then(|| {
        // The rung: a summary moved onto a body-less function.
        let (mut module, _) = installed_p01();
        let summary = module.functions[0].summary.take();
        module.functions[2].blocks.clear();
        assert!(module.functions[2].is_declaration());
        module.functions[2].summary = summary;
        let errors = contract_bound_inventory_errors(&module);
        assert!(
            errors.iter().any(|e| e.contains("body-less declaration carrying a summary")),
            "{errors:#?}"
        );

        // The installer: a FuncId that is a declaration withholds the body.
        let (mut module, assigned) = p01_module();
        module.functions[0].blocks.clear();
        let (outcome, errors) = install(&mut module, &assigned, p01_registry());
        assert_eq!(outcome.bodies_withheld, 1);
        assert!(module.functions[0].summary.is_none());
        assert!(errors.iter().any(|e| e.contains("body-less declaration")), "{errors:#?}");
    });
}

#[test]
fn non_pending_and_foreign_contract_rows_are_refused() {
    rustc_span::create_default_session_globals_then(|| {
        for status in [ProofStatus::Discharged, ProofStatus::Trusted, ProofStatus::Certified] {
            let (mut module, _) = installed_p01();
            let index = module.proof_obligations.len() - 1;
            module.proof_obligations[index].status = status.clone();
            let errors = contract_bound_inventory_errors(&module);
            assert!(
                errors.iter().any(|e| e.contains("(must be pending)")),
                "{status:?}: {errors:#?}"
            );
        }
        // A row whose formula states no clause of its summary.
        let (mut module, _) = installed_p01();
        let mut forged = module.proof_obligations[0].formula.clone().unwrap();
        forged.payload.push(' ');
        module.proof_obligations[0].formula = Some(forged);
        let errors = contract_bound_inventory_errors(&module);
        assert!(
            errors.iter().any(|e| e.contains("its formula is no requires clause")),
            "{errors:#?}"
        );
        // A contract kind the carry never mints.
        let (mut module, _) = installed_p01();
        module.proof_obligations[0].kind = ObligationKind::MemorySafety;
        let errors = contract_bound_inventory_errors(&module);
        assert!(errors.iter().any(|e| e.contains("kind MemorySafety")), "{errors:#?}");
    });
}

// ================================ mutations =================================

/// Mathematical evaluation of a proposition — the source meaning, with
/// `lookup` supplying each free name.
fn eval(p: &P, lookup: &dyn Fn(&str) -> i128) -> Result<i128, ()> {
    let bin = |a: &P, b: &P| Ok::<_, ()>((eval(a, lookup)?, eval(b, lookup)?));
    Ok(match p {
        P::Bool(v) => i128::from(*v),
        P::Int(v) => *v,
        P::UInt(v) => i128::try_from(*v).map_err(|_| ())?,
        P::Var { name, .. } => lookup(name.as_str()),
        P::Not(a) => i128::from(eval(a, lookup)? == 0),
        P::And(xs) => i128::from(xs.iter().all(|x| eval(x, lookup) == Ok(1))),
        P::Or(xs) => i128::from(xs.iter().any(|x| eval(x, lookup) == Ok(1))),
        P::Implies(a, b) => i128::from(eval(a, lookup)? == 0 || eval(b, lookup)? == 1),
        P::Eq(a, b) => i128::from(bin(a, b)?.0 == bin(a, b)?.1),
        P::Lt(a, b) => i128::from(bin(a, b)?.0 < bin(a, b)?.1),
        P::Le(a, b) => i128::from(bin(a, b)?.0 <= bin(a, b)?.1),
        P::Gt(a, b) => i128::from(bin(a, b)?.0 > bin(a, b)?.1),
        P::Ge(a, b) => i128::from(bin(a, b)?.0 >= bin(a, b)?.1),
        P::Add(a, b) => bin(a, b)?.0 + bin(a, b)?.1,
        P::Sub(a, b) => bin(a, b)?.0 - bin(a, b)?.1,
        P::Mul(a, b) => bin(a, b)?.0 * bin(a, b)?.1,
        P::Neg(a) => -eval(a, lookup)?,
        P::Div(..) | P::Rem(..) | P::Float { .. } => return Err(()),
    })
}

/// The p01 differential oracle: every carried clause of `clamp_add`, read
/// through its BINDINGS (place -> the interpreter's argument / result), must
/// agree with the clause read through the SOURCE parameter names, on every
/// sampled argument pair. Returns the disagreeing samples.
fn p01_oracle_disagreements(module: &Module, func: FuncId, propositions: &[P]) -> Vec<String> {
    let summary = module.functions[func.index() as usize].summary.as_ref().unwrap();
    let clauses: Vec<&ProofFormula> = summary.requires.iter().chain(&summary.ensures).collect();
    let mut disagreements = Vec::new();
    for (x, y) in [(5, 2000), (2000, 5), (40, 2), (1000, 0), (0, 1001)] {
        let result = i128::try_from(run(module, func, vec![u64_arg(x), u64_arg(y)])).unwrap();
        let source = |name: &str| match name {
            "x" => x,
            "y" => y,
            "_0" => result,
            other => panic!("unexpected source name {other}"),
        };
        for (clause, proposition) in clauses.iter().zip(propositions) {
            let carried = |name: &str| {
                let (_, binding) = clause.bindings.iter().find(|(n, _)| n == name).unwrap();
                match binding.place {
                    ClausePlace::Param { index: 0 } => x,
                    ClausePlace::Param { index: 1 } => y,
                    ClausePlace::ResultSlot { index: 0 } => result,
                    other => panic!("unexpected place {other:?}"),
                }
            };
            if eval(proposition, &source) != eval(proposition, &carried) {
                disagreements.push(format!("({x}, {y}) on `{}`", clause.payload));
            }
        }
    }
    disagreements
}

#[test]
fn swapping_two_same_sorted_param_indices_makes_the_p01_oracle_disagree() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, assigned) = installed_p01();
        let registry = p01_registry();
        let propositions: Vec<P> = registry.bodies[&3]
            .clauses
            .iter()
            .map(|clause| match &clause.predicate {
                TrustContractPredicateKind::Typed { proposition, .. } => proposition.clone(),
                _ => unreachable!(),
            })
            .collect();
        assert!(
            p01_oracle_disagreements(&module, assigned[0].1, &propositions).is_empty(),
            "the honest carry agrees with the source on every sample"
        );
        // The mutation: x <-> y on every clause of clamp_add (both u64, so no
        // sort or type check can see it).
        let summary = module.functions[0].summary.as_mut().unwrap();
        for clause in summary.requires.iter_mut().chain(summary.ensures.iter_mut()) {
            for (_, binding) in &mut clause.bindings {
                binding.place = match binding.place {
                    ClausePlace::Param { index: 0 } => ClausePlace::Param { index: 1 },
                    ClausePlace::Param { index: 1 } => ClausePlace::Param { index: 0 },
                    other => other,
                };
            }
        }
        assert!(trust_ir_build::validate_module(&module).is_empty(), "invisible to the validator");
        let disagreements = p01_oracle_disagreements(&module, assigned[0].1, &propositions);
        assert!(!disagreements.is_empty(), "the oracle must catch the index swap");
        assert!(disagreements.iter().any(|d| d.starts_with("(5, 2000)")), "{disagreements:#?}");
    });
}

#[test]
fn stripping_bitvec64_to_int_is_refused_by_the_staged_rung() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, _) = installed_p01();
        let summary = module.functions[0].summary.as_mut().unwrap();
        summary.requires[0].bindings[0].1.sort = ClauseSort::Int;
        let errors = contract_bound_inventory_errors(&module);
        assert!(
            errors.iter().any(|e| e.contains("width strip, refused")),
            "the staged rung refuses Int over a u64 place: {errors:#?}"
        );
        // MEASURED, not assumed: trust-ir at the pinned 5dbbf177 ADMITS the
        // strip — `clause_sort_admits` reads `Int <= any integer`, the very
        // width-strip hazard its own `ClauseBinding` doc names — so WS1.2's
        // validator is NOT what refuses this mutation; the rung above is. If
        // this assertion ever fires, trust-ir refuses it too: update the WS5.5
        // notes in DIRECT-LANE-PROOF-AUTHORITY.md, never this rung.
        let validator = trust_ir_build::validate_module(&module);
        assert!(validator.is_empty(), "trust-ir's verdict on the strip moved: {validator:#?}");
    });
}

#[test]
fn a_header_that_does_not_reresolve_fires_the_install_self_check() {
    rustc_span::create_default_session_globals_then(|| {
        type Mutation = fn(&mut ContractBodyRecord);
        let mutations: [(&str, Mutation, &str); 4] = [
            ("dropped record", |r| r.loop_headers.clear(), "has no recorded header"),
            ("wrong header", |r| r.loop_headers[0].header = BlockId::new(2), "carries parameters"),
            (
                "renumbered parameters",
                |r| r.loop_headers[0].header_params.swap(0, 1),
                "carries parameters",
            ),
            (
                "stale pre-header",
                |r| r.loop_headers[0].pre_header = BlockId::new(3),
                "does not end in `br` to the header",
            ),
        ];
        for (label, mutate, expected) in mutations {
            let (mut module, assigned) = p02_module();
            let mut registry = p02_registry(&module);
            mutate(registry.bodies.get_mut(&7).unwrap());
            let (outcome, errors) = install(&mut module, &assigned, registry);
            assert_eq!(errors.len(), 1, "{label}: {errors:#?}");
            assert!(errors[0].contains("header self-check failed"), "{label}: {}", errors[0]);
            assert!(errors[0].contains(expected), "{label}: {}", errors[0]);
            assert_eq!(outcome.loop_rows_withheld, 2, "{label}: both loop rows withheld");
            assert!(
                contract_rows(&module).iter().all(|row| row.site.is_none()),
                "{label}: no loop row is ever sited by guess"
            );
            assert_eq!(contract_rows(&module).len(), 1, "{label}: the requires row still lands");
        }
    });
}

/// `fn f(x: &mut u64) requires *x > 0`, as the query types it (`x*` is the
/// pointee leaf of a reference parameter), over the IR the direct lane emits
/// (the `&mut` parameter is a thin `Ptr`).
fn pointee_fixture() -> (Module, Vec<(u32, FuncId)>, ContractCarryRegistry) {
    let mut mb =
        ModuleBuilder::new_with_target_info("pointee", crate::drop_glue_oracle::oracle_target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("pointee::f", ft);
    let entry = fb.create_block();
    let _x = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    let f = fb.build();
    let mut record =
        body(11, "f", 1, vec![CarryParam { reference: ParamReference::Mut, ..param(0, "x", 2) }]);
    record.clauses = vec![fn_clause(
        ClauseRole::Requires,
        0,
        typed("x* > 0", P::Gt(b(var("x*", U64)), b(P::Int(0)))),
    )];
    let mut registry = ContractCarryRegistry::default();
    registry.insert(record);
    (mb.build().expect("the pointee fixture builds"), vec![(11, f)], registry)
}

#[test]
fn an_entry_pointee_requires_is_carried_opaque_and_its_approximate_binding_is_refused() {
    rustc_span::create_default_session_globals_then(|| {
        let (mut module, assigned, registry) = pointee_fixture();
        let (outcome, errors) = install(&mut module, &assigned, registry);
        assert!(errors.is_empty(), "{errors:#?}");
        let clause = &module.functions[0].summary.as_ref().unwrap().requires[0];
        assert_eq!(clause.schema, CONTRACT_OPAQUE_SCHEMA, "the producer never binds `*x`");
        assert!(clause.bindings.is_empty());
        assert!(outcome.opaque[0].3.contains("ParamPointeeEntry"), "{:?}", outcome.opaque);
        assert_validates(&module);

        // The approximate binding the carry refuses to emit: `*x` as
        // Param{0}: BitVec(64). WS1.2's binding check refuses it (the place is
        // a Ptr), on the summary and on the row alike.
        let mut lie = ProofFormula::new(CONTRACT_CLAUSE_SCHEMA, "{}");
        lie.bindings = vec![("x*".to_string(), bv64(ClausePlace::Param { index: 0 }))];
        module.functions[0].summary.as_mut().unwrap().requires[0] = lie.clone();
        module.proof_obligations[0].formula = Some(lie);
        let refused = trust_ir_build::validate_module(&module);
        let rendered = format!("{refused:?}");
        assert!(rendered.contains("InvalidFunctionSummary"), "{refused:#?}");
        assert!(rendered.contains("InvalidObligationBinding"), "{refused:#?}");
        assert!(!contract_bound_inventory_errors(&module).is_empty());
    });
}

#[test]
fn a_destructured_or_unknown_parameter_name_stays_opaque() {
    rustc_span::create_default_session_globals_then(|| {
        // `fn g((a, b): (u64, u64)) requires a <= b`: the pattern is not a
        // simple binding, so neither name has a Param of its own — even if a
        // query typed the clause.
        let (mut module, assigned) = p01_module();
        let mut registry = p01_registry();
        let clamp = registry.bodies.get_mut(&3).unwrap();
        clamp.params.clear();
        clamp.clauses.truncate(1);
        clamp.clauses[0].predicate = typed("a <= b", P::Le(b(var("a", U64)), b(var("b", U64))));
        let (outcome, errors) = install(&mut module, &assigned, registry);
        assert!(errors.is_empty(), "{errors:#?}");
        let clause = &module.functions[0].summary.as_ref().unwrap().requires[0];
        assert_eq!(clause.schema, CONTRACT_OPAQUE_SCHEMA);
        assert!(clause.bindings.is_empty());
        assert!(outcome.opaque[0].3.contains("destructured"), "{:?}", outcome.opaque);
        assert_eq!(
            module.functions[0].summary.as_ref().unwrap().params,
            vec!["__param0".to_string(), "__param1".to_string()],
            "a formal with no simple binding gets a reserved positional name"
        );
    });
}

#[test]
fn ensures_reads_of_mut_bindings_and_shared_pointees_stay_opaque() {
    rustc_span::create_default_session_globals_then(|| {
        let ensures = |name: &str| {
            fn_clause(ClauseRole::Ensures, 0, typed("e", P::Ge(b(var(name, U64)), b(P::Int(0)))))
        };
        let cx_params = [
            CarryParam { mutable: true, ..param(0, "m", 1) },
            CarryParam { reference: ParamReference::Shared, ..param(1, "s", 2) },
            CarryParam { reference: ParamReference::Mut, ..param(2, "r", 3) },
            CarryParam { reference: ParamReference::Mut, mutable: true, ..param(3, "q", 4) },
        ];
        let tys = [Ty::U64, Ty::Ptr, Ty::Ptr, Ty::RefMut(Box::new(Ty::U64))];
        let cx = ClauseContext {
            params: &cx_params,
            binding_refusal: None,
            param_tys: &tys,
            return_tys: &[Ty::U64],
            pointer_bits: Some(64),
            header: None,
        };
        for (name, why) in [
            ("m", "may be reassigned"),
            ("s*", "non-`&mut` parameter"),
            ("r*", "the IR spells it ptr"),
            ("q*", "may be reassigned"),
            ("old_m", "`old(..)`"),
            ("xs__len", "synthetic"),
        ] {
            let carried = carry_clause(&ensures(name), &cx);
            assert_eq!(carried.formula.schema, CONTRACT_OPAQUE_SCHEMA, "{name}");
            let reason = carried.opaque_reason.unwrap();
            assert!(reason.to_lowercase().contains(&why.to_lowercase()), "{name}: {reason}");
        }
        // With a typed `&mut u64` IR parameter the exit value binds.
        let tys = [Ty::U64, Ty::Ptr, Ty::RefMut(Box::new(Ty::U64))];
        let cx = ClauseContext { param_tys: &tys, ..cx };
        let carried = carry_clause(&ensures("r*"), &cx);
        assert_eq!(carried.opaque_reason, None);
        assert_eq!(
            carried.formula.bindings,
            vec![("r*".to_string(), bv64(ClausePlace::MutParamExit { index: 2 }))]
        );
        // ... and only in an ensures.
        let requires =
            fn_clause(ClauseRole::Requires, 0, typed("r", P::Ge(b(var("r*", U64)), b(P::Int(0)))));
        assert!(carry_clause(&requires, &cx).opaque_reason.unwrap().contains("ParamPointeeEntry"));
        // A body whose IR signature is not its HIR param list binds nothing.
        let cx = ClauseContext { binding_refusal: Some("a closure"), ..cx };
        assert!(carry_clause(&ensures("r*"), &cx).opaque_reason.unwrap().contains("a closure"));
    });
}

// ================================ fail-closed install =======================

#[test]
fn duplicate_registration_unspliced_bodies_and_body_refusals_fail_closed() {
    rustc_span::create_default_session_globals_then(|| {
        // A body registered twice contributes nothing.
        let (mut module, assigned) = p01_module();
        let mut registry = p01_registry();
        registry.insert(body(3, "clamp_add", 2, Vec::new()));
        let (outcome, errors) = install(&mut module, &assigned, registry);
        assert_eq!(outcome.rows_installed, 0);
        assert!(errors[0].contains("duplicate per-body registrations"), "{errors:#?}");
        assert!(module.functions.iter().all(|f| f.summary.is_none()));

        // A body that was not spliced is skipped and disclosed, never dangling.
        let (mut module, _) = p01_module();
        let (outcome, errors) = install(&mut module, &[], p01_registry());
        assert!(errors.is_empty());
        assert_eq!(outcome.bodies_skipped_unspliced, 2);
        assert!(module.proof_obligations.is_empty());

        // A clause kind the carry does not place withholds its body.
        let (mut module, assigned) = p01_module();
        let mut registry = p01_registry();
        registry.bodies.get_mut(&3).unwrap().refusal =
            Some("function contract 9 has kind Temporal".into());
        let (outcome, errors) = install(&mut module, &assigned, registry);
        assert_eq!(outcome.bodies_withheld, 1);
        assert!(errors[0].contains("kind Temporal"), "{errors:#?}");
        assert!(module.functions[0].summary.is_none());
        assert!(module.functions[1].summary.is_some(), "only the refused body is withheld");

        // A function that already carries a summary is never overwritten.
        let (mut module, assigned) = installed_p01();
        let before = module.clone();
        let (_, errors) = install(&mut module, &assigned, p01_registry());
        assert!(errors.iter().all(|e| e.contains("already carries a summary")), "{errors:#?}");
        assert_eq!(module.functions, before.functions);
        assert_eq!(module.proof_obligations, before.proof_obligations);

        // An arity disagreement between emission and the assembled signature.
        let (mut module, assigned) = p01_module();
        let mut registry = p01_registry();
        registry.bodies.get_mut(&3).unwrap().ir_param_count = Some(3);
        let (_, errors) = install(&mut module, &assigned, registry);
        assert!(errors[0].contains("recorded IR arity"), "{errors:#?}");
    });
}

// ================================ SMT-LIB rendering ==========================

#[test]
fn smtlib_rendering_is_exact_or_absent() {
    rustc_span::create_default_session_globals_then(|| {
        let i32d = D::MachineInt { width: 32, signed: true };
        let m = D::MathematicalInt;
        let cases: Vec<(P, bool, Option<(&str, &str)>)> = vec![
            // Signedness rides the operator.
            (
                P::Lt(b(var("a", i32d)), b(P::Int(-1))),
                false,
                Some(("(bvslt a (_ bv4294967295 32))", "Bool")),
            ),
            (P::Gt(b(var("u", U64)), b(var("v", U64))), false, Some(("(bvugt u v)", "Bool"))),
            // An out-of-range literal has no bit-vector spelling.
            (P::Ge(b(var("u", U64)), b(P::Int(-1))), false, None),
            (P::Le(b(var("a", i32d)), b(P::UInt(1 << 31))), false, None),
            // Spec arithmetic is mathematical: only over Int.
            (
                P::Eq(b(var("k", m)), b(P::Add(b(var("j", m)), b(P::Int(1))))),
                false,
                Some(("(= k (+ j 1))", "Bool")),
            ),
            (P::Eq(b(var("u", U64)), b(P::Add(b(var("v", U64)), b(P::Int(1))))), false, None),
            (P::Lt(b(P::Div(b(var("k", m)), b(P::Int(2)))), b(var("k", m))), false, None),
            // Connectives.
            (
                P::And(vec![
                    P::Bool(true),
                    P::Not(b(P::Eq(b(var("p", D::Bool)), b(P::Bool(false))))),
                ]),
                false,
                Some(("(and true (not (= p false)))", "Bool")),
            ),
            (P::Or(vec![]), false, Some(("false", "Bool"))),
            (
                P::Implies(b(var("p", D::Bool)), b(P::Bool(true))),
                false,
                Some(("(=> p true)", "Bool")),
            ),
            // Measures: an Int measure renders; a bit-vector one has no order.
            (P::Sub(b(var("k", m)), b(P::Int(1))), true, Some(("(- k 1)", "Int"))),
            (var("n", U64), true, None),
            (P::Int(3), true, Some(("3", "Int"))),
            // Floats and non-simple symbols.
            (
                P::Gt(b(var("f", D::Float { width: 64 })), b(P::Float { bits: 0, width: 64 })),
                false,
                None,
            ),
            (
                P::Gt(b(var("r*", U64)), b(P::Int(0))),
                false,
                Some(("(bvugt |r*| (_ bv0 64))", "Bool")),
            ),
            // A predicate of numeric sort is not a clause.
            (var("n", U64), false, None),
        ];
        for (proposition, measure, expected) in cases {
            let got = smt::render_clause(&proposition, measure);
            let got = got.as_ref().map(|(t, s)| (t.as_str(), s.as_str()));
            assert_eq!(got, expected, "{proposition:?} (measure: {measure})");
        }
    });
}

#[test]
fn every_role_mints_its_kind_and_the_identity_is_stable() {
    let expected: BTreeMap<_, _> = [
        (ClauseRole::Requires, ObligationKind::Precondition),
        (ClauseRole::Ensures, ObligationKind::Postcondition),
        (ClauseRole::Decreases, ObligationKind::Termination),
        (ClauseRole::LoopInvariant, ObligationKind::LoopInvariant),
        (ClauseRole::LoopDecreases, ObligationKind::Termination),
    ]
    .into_iter()
    .collect();
    for (role, kind) in expected {
        assert_eq!(role.obligation_kind(), kind, "{role:?}");
    }
    let long = "m::".repeat(400);
    let id = clamp_identity("c", &long, "#ensures#c7");
    assert!(id.ends_with("#ensures#c7"), "the unique tail is always kept: {id}");
    assert!(id.len() <= PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES);
    assert_eq!(CONTRACT_BOUND_MARKER, "contract-bound-v3");
}

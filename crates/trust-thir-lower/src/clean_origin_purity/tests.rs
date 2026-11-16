//! Unit tests for the F1 purity census and the cross-language cycle check (plan step 3.5). The
//! wiring (which rows are judged, the fatal, the MIR backstop) needs a `TyCtxt` and is pinned end
//! to end by `tests/run-make/trust-cg-f1-clean-recorder`.

use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer,
    Ty, ValueId,
};

use super::*;

/// Every function of `m` conserved (the effect-conservation check passed them all).
fn all(m: &Module) -> BTreeSet<FuncId> {
    m.functions.iter().map(|f| f.id).collect()
}

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn node_r(inst: Inst, r: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(r))
}

fn ret() -> InstrNode {
    node(Inst::Return { values: vec![v(0)] })
}

fn call(callee: u32) -> InstrNode {
    node_r(Inst::Call { callee: FuncId::new(callee), args: vec![v(0)] }, 50 + callee)
}

/// One function per entry, `FuncId(i)` = index `i`, one `u64 -> u64` signature; `None` is a
/// declaration (no body). Block 0 is the entry, with the parameter `%0`.
fn module(functions: Vec<(&str, Producer, Option<Vec<InstrNode>>)>) -> Module {
    let mut module = Module::new("purity");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    for (i, (name, producer, body)) in functions.into_iter().enumerate() {
        let mut f =
            Function::new(FuncId::new(i as u32), name, ty, BlockId::new(0)).with_producer(producer);
        if let Some(body) = body {
            let mut block = Block::new(BlockId::new(0)).with_param(v(0), Ty::U64);
            block.body = body;
            f.blocks.push(block);
        }
        module.functions.push(f);
    }
    module
}

fn xor() -> InstrNode {
    node_r(Inst::BinOp { op: BinOp::Xor, ty: Ty::U64, lhs: v(0), rhs: v(0) }, 1)
}

fn global_store() -> Vec<InstrNode> {
    vec![
        node_r(Inst::GlobalAddr { global: GlobalId::new(0) }, 2),
        node(Inst::Store { ty: Ty::U64, ptr: v(2), value: v(0), volatile: false, align: None }),
        ret(),
    ]
}

fn impure_finding(purity: CalleePurity) -> (String, String) {
    match purity {
        CalleePurity::Impure { function, finding } => (function, finding),
        other => panic!("expected IMPURE, got {other:?}"),
    }
}

fn undecided_reason(purity: CalleePurity) -> (String, String) {
    match purity {
        CalleePurity::Undecided { function, reason } => (function, reason),
        other => panic!("expected UNDECIDED, got {other:?}"),
    }
}

#[test]
fn a_conserved_arithmetic_callee_and_its_own_stack_are_pure() {
    let m = module(vec![
        ("twice", Producer::Clean, Some(vec![call(1), call(1), ret()])),
        ("mix", Producer::TRust, Some(vec![xor(), call(2), ret()])),
        (
            "scratch",
            Producer::TRust,
            Some(vec![
                node_r(Inst::Alloca { ty: Ty::U64, count: None, align: None }, 3),
                node(Inst::Store {
                    ty: Ty::U64,
                    ptr: v(3),
                    value: v(0),
                    volatile: false,
                    align: None,
                }),
                node_r(Inst::Load { ty: Ty::U64, ptr: v(3), volatile: false, align: None }, 4),
                ret(),
            ]),
        ),
    ]);
    assert_eq!(rust_callee_purity(&m, &all(&m), FuncId::new(1)), CalleePurity::Pure);
}

/// The design's `impure_rust_callee_refused_on_f1` shape at the unit level: a callee writing
/// through a `&mut` global. And every other effect class the MIR walk refuses.
#[test]
fn every_effect_the_mir_walk_refuses_is_impure_on_the_census() {
    let m = module(vec![
        ("calls", Producer::Clean, Some(vec![call(1), ret()])),
        ("bump", Producer::TRust, Some(global_store())),
    ]);
    let (function, finding) = impure_finding(rust_callee_purity(&m, &all(&m), FuncId::new(1)));
    assert_eq!(function, "bump");
    assert!(finding.contains("writes memory outside its own frame"), "{finding}");
    assert!(finding.contains("rooted at a global"), "{finding}");

    let gaddr = || node_r(Inst::GlobalAddr { global: GlobalId::new(0) }, 2);
    let param_ptr = || {
        node_r(
            Inst::Cast {
                op: trust_ir::CastOp::IntToPtr,
                src_ty: Ty::U64,
                dst_ty: Ty::Ptr,
                operand: v(0),
            },
            2,
        )
    };
    let cases: Vec<(&str, Vec<InstrNode>, &str)> = vec![
        (
            "a read of a global",
            vec![
                node_r(Inst::GlobalAddr { global: GlobalId::new(0) }, 2),
                node_r(Inst::Load { ty: Ty::U64, ptr: v(2), volatile: false, align: None }, 3),
                ret(),
            ],
            "reads memory outside its own frame",
        ),
        (
            "a write through a pointer the body did not allocate",
            vec![
                param_ptr(),
                node(Inst::Store {
                    ty: Ty::U64,
                    ptr: v(2),
                    value: v(0),
                    volatile: false,
                    align: None,
                }),
                ret(),
            ],
            "writes memory outside its own frame",
        ),
        (
            "an atomic",
            vec![
                gaddr(),
                node_r(
                    Inst::AtomicLoad {
                        ty: Ty::U64,
                        ptr: v(2),
                        ordering: trust_ir::Ordering::SeqCst,
                    },
                    3,
                ),
                ret(),
            ],
            "atomic",
        ),
        (
            "an indirect call",
            vec![
                node_r(
                    Inst::CallIndirect {
                        callee: v(0),
                        sig: trust_ir::value::FuncTyId::new(0),
                        args: vec![],
                        calling_conv: trust_ir::CallingConv::Rust,
                    },
                    3,
                ),
                ret(),
            ],
            "indirect call",
        ),
        ("the address of a global", vec![gaddr(), ret()], "address of a global"),
        (
            "a heap allocation",
            vec![
                node_r(
                    Inst::HeapAlloc {
                        ty: Ty::U64,
                        count: None,
                        align: None,
                        origin: trust_ir::inst::AllocOrigin::RustHeap,
                    },
                    3,
                ),
                ret(),
            ],
            "heap memory",
        ),
    ];
    for (what, body, needle) in cases {
        let m = module(vec![
            ("calls", Producer::Clean, Some(vec![call(1), ret()])),
            ("callee", Producer::TRust, Some(body)),
        ]);
        let (_, finding) = impure_finding(rust_callee_purity(&m, &all(&m), FuncId::new(1)));
        assert!(finding.contains(needle), "{what}: {finding}");
    }
}

#[test]
fn impurity_is_found_through_direct_calls_and_wins_over_an_undecided_callee() {
    // `outer` calls an upstream declaration first, then `inner`, which writes a global.
    let m = module(vec![
        ("calls", Producer::Clean, Some(vec![call(1), ret()])),
        ("outer", Producer::TRust, Some(vec![call(3), call(2), ret()])),
        ("inner", Producer::TRust, Some(global_store())),
        ("core::num::<impl u64>::wrapping_add", Producer::TRust, None),
    ]);
    let (function, _) = impure_finding(rust_callee_purity(&m, &all(&m), FuncId::new(1)));
    assert_eq!(function, "inner", "a finding is reported where it is, however deep");
}

/// t4's `inc` calls `u64::wrapping_add`, which has no body in the crate's module (upstream): the
/// census cannot decide it, and says which callee and why. So is a body the effect-conservation
/// check did not find conserved.
#[test]
fn an_upstream_callee_or_a_withdrawn_body_is_undecided_never_pure() {
    let m = module(vec![
        ("twice_inc", Producer::Clean, Some(vec![call(1), call(1), ret()])),
        ("inc", Producer::TRust, Some(vec![call(2), ret()])),
        ("core::num::<impl u64>::wrapping_add", Producer::TRust, None),
    ]);
    let (function, reason) = undecided_reason(rust_callee_purity(&m, &all(&m), FuncId::new(1)));
    assert_eq!(function, "core::num::<impl u64>::wrapping_add");
    assert!(reason.contains("no body in this crate's trust-ir module"), "{reason}");

    // `helper` has a body the effect-conservation check did NOT find conserved: its census is not
    // read, however pure it looks. A Clean body needs no verdict (its census is its declaration's).
    let m = module(vec![
        ("calls", Producer::Clean, Some(vec![call(1), ret()])),
        ("helper", Producer::TRust, Some(vec![xor(), ret()])),
    ]);
    let only_clean: BTreeSet<FuncId> = BTreeSet::new();
    let (function, reason) = undecided_reason(rust_callee_purity(&m, &only_clean, FuncId::new(1)));
    assert_eq!(function, "helper");
    assert!(reason.contains("not conserved"), "{reason}");
    let nested = module(vec![
        ("a", Producer::Clean, Some(vec![call(1), ret()])),
        ("f", Producer::TRust, Some(vec![call(2), ret()])),
        ("b", Producer::Clean, Some(vec![xor(), ret()])),
    ]);
    let rust_only: BTreeSet<FuncId> = BTreeSet::from([FuncId::new(1)]);
    assert_eq!(rust_callee_purity(&nested, &rust_only, FuncId::new(1)), CalleePurity::Pure);

    // An `undef` is an abstraction (D28): undecided, not pure.
    let m = module(vec![
        ("calls", Producer::Clean, Some(vec![call(1), ret()])),
        ("abstracted", Producer::TRust, Some(vec![node_r(Inst::Undef { ty: Ty::U64 }, 2), ret()])),
    ]);
    let (_, reason) = undecided_reason(rust_callee_purity(&m, &all(&m), FuncId::new(1)));
    assert!(reason.contains("undef"), "{reason}");
}

/// The design's `cycle_across_languages_refused_on_f1` shape at the unit level: `fn inc` ->
/// `def twice_inc` -> `inc`, directly and two hops out, and through a function value.
#[test]
fn a_cross_language_cycle_is_found_on_the_call_graph() {
    let direct = module(vec![
        ("twice_inc", Producer::Clean, Some(vec![call(1), call(1), ret()])),
        ("inc", Producer::TRust, Some(vec![call(0), ret()])),
    ]);
    assert_eq!(
        cross_language_cycles(&direct),
        vec![CrossLanguageCycle {
            clean: FuncId::new(0),
            path: vec![FuncId::new(0), FuncId::new(1), FuncId::new(0)],
        }]
    );
    let two_hops = module(vec![
        ("twice_h", Producer::Clean, Some(vec![call(1), ret()])),
        ("hop", Producer::TRust, Some(vec![call(2), ret()])),
        ("deep", Producer::TRust, Some(vec![call(0), ret()])),
    ]);
    assert_eq!(
        cross_language_cycles(&two_hops),
        vec![CrossLanguageCycle {
            clean: FuncId::new(0),
            path: vec![FuncId::new(0), FuncId::new(1), FuncId::new(2), FuncId::new(0)],
        }]
    );
    let through_a_value = module(vec![
        ("def", Producer::Clean, Some(vec![call(1), ret()])),
        (
            "takes",
            Producer::TRust,
            Some(vec![
                node_r(Inst::Const { ty: Ty::Ptr, value: Constant::FnDef(FuncId::new(0)) }, 2),
                ret(),
            ]),
        ),
    ]);
    assert_eq!(cross_language_cycles(&through_a_value).len(), 1);
}

/// What is NOT a cross-language cycle: Clean recursion (kernel-checked, one language), acyclic
/// nesting (`def a := f x` where `fn f` calls a different `def b`), and Rust recursion.
#[test]
fn clean_recursion_and_acyclic_nesting_are_not_cycles() {
    let m = module(vec![
        ("rec", Producer::Clean, Some(vec![call(0), ret()])),
        ("a", Producer::Clean, Some(vec![call(2), ret()])),
        ("f", Producer::TRust, Some(vec![call(3), ret()])),
        ("b", Producer::Clean, Some(vec![xor(), ret()])),
        ("loop_r", Producer::TRust, Some(vec![call(4), ret()])),
    ]);
    assert_eq!(cross_language_cycles(&m), Vec::new());
}

#[test]
fn the_disclosure_reader_finds_emitted_rows_and_skips_the_rest() {
    let mut m = module(vec![("twice_inc", Producer::Clean, Some(vec![ret()]))]);
    let mut spec =
        trust_ir::SpecModule::new(crate::clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME);
    spec.invariants.push(trust_ir::SpecInvariant::new(
        "fn:0",
        "{\"schema\":\"trust.clean-origin-disclosure.v1\",\"def_path\":\"m::\\\"q\\\"\",\
         \"clean_name\":\"twice_inc\",\"shape\":\"rust-call-chain\",\"tier\":\"structural\"}",
    ));
    spec.invariants.push(trust_ir::SpecInvariant::new(
        "skipped:7",
        "{\"def_path\":\"skipped_one\",\"shape\":\"structural-nat-rec\"}",
    ));
    m.spec_modules.push(spec);
    let mut other = trust_ir::SpecModule::new("user-spec");
    other
        .invariants
        .push(trust_ir::SpecInvariant::new("fn:1", "{\"def_path\":\"x\",\"shape\":\"y\"}"));
    m.spec_modules.push(other);
    assert_eq!(
        disclosed_emitted_rows(&m),
        vec![DisclosedCleanRow {
            func_id: FuncId::new(0),
            def_path: "m::\"q\"".to_string(),
            shape: "rust-call-chain".to_string(),
        }]
    );
}

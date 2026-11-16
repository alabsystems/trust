use trust_types::{CallableKind, ConstValue};

use super::*;

#[test]
fn const_param_equality_is_unknown_never_definitely_unequal() {
    // v2_const_eq_truth over a ConstParam must return None (verify BOTH
    // branches), NEVER Some(false) — else an equal `N == N` prunes the taken
    // branch and drops its safety obligations (a false PROVE).
    let n = ConstValue::ConstParam { index: 1, name: "N".to_string(), width: 64, signed: false };
    let m = ConstValue::ConstParam { index: 0, name: "M".to_string(), width: 64, signed: false };
    assert_eq!(v2_const_eq_truth(&n, &n), None, "N == N must be UNKNOWN, not Some(true/false)");
    assert_eq!(v2_const_eq_truth(&n, &m), None, "N == M must be UNKNOWN");
    assert_eq!(
        v2_const_eq_truth(&n, &ConstValue::Int(3)),
        None,
        "N == 3 must be UNKNOWN, not Some(false)"
    );
}

#[test]
fn callable_item_equality_is_unknown_and_identity_never_becomes_a_fact() {
    let first = ConstValue::CallableItem {
        def_path: "fixture::first".to_string(),
        kind: CallableKind::FnDef,
        def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
    };
    let same = first.clone();
    let second = ConstValue::CallableItem {
        def_path: "fixture::second".to_string(),
        kind: CallableKind::FnDef,
        def_path_hash: trust_types::CallableDefPathHash::new(1, 2),
    };
    assert_eq!(v2_const_eq_truth(&first, &same), None);
    assert_eq!(v2_const_eq_truth(&first, &second), None);
    assert_eq!(v2_const_eq_truth(&first, &ConstValue::Unit), None);
}

#[test]
fn const_param_divisor_is_satisfiably_zero_never_provably_nonzero() {
    // v2_divisor_is_zero_formula over a ConstParam divisor must emit the
    // SATISFIABLE `sym == 0`, NOT `Bool(false)` (provably nonzero = false
    // PROVE of `x / N`).
    use trust_types::{Operand, Sort, VerifiableBody, VerifiableFunction};
    let func = VerifiableFunction {
        name: "d".into(),
        def_path: "test::d".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let divisor = Operand::Constant(ConstValue::ConstParam {
        index: 1,
        name: "N".to_string(),
        width: 64,
        signed: false,
    });
    let f = v2_divisor_is_zero_formula(&func, &divisor);
    // Must reference the per-param symbol and be an Eq(..0), NOT Bool(false).
    match f {
        Formula::Eq(lhs, rhs) => {
            assert_eq!(*lhs, Formula::var("__trust_constparam_1_N", Sort::Int));
            assert_eq!(*rhs, Formula::Int(0));
        }
        other => {
            panic!("const-param divisor must yield a satisfiable `sym == 0`, got {other:?}")
        }
    }
}

#[test]
fn const_param_symbol_is_not_freshened_on_the_sigma_path() {
    // CONSTPARAM-SIGMA-FRESHEN-1 (reverses the wave-2 INV-2 pin, which asserted the
    // opposite): the per-param family is identity-keyed — one symbol is one value of
    // the caller — so the σ post-pass must NOT split it per occurrence. Splitting it
    // detached the guard `n < K` from σ's `buf__slice_len := K` and refuted correct
    // generic callers. The genuinely alias-prone families are still freshened.
    let k = trust_types::const_param_symbol(0, "K");
    assert!(!is_aliasing_opaque_symbol_name(&k));
    assert!(!is_aliasing_opaque_symbol_name("__trust_constparam_1_N"));
    assert!(is_aliasing_opaque_symbol_name("__unknown_const"));
    assert!(is_aliasing_opaque_symbol_name(&format!(
        "{}u64_site",
        trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX
    )));

    let guard_and_violation = Formula::And(vec![
        Formula::Lt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::var(&k, Sort::Int))),
        Formula::Not(Box::new(Formula::Lt(
            Box::new(Formula::var("n", Sort::Int)),
            Box::new(Formula::var(&k, Sort::Int)),
        ))),
    ]);
    let occ = std::cell::Cell::new(0u32);
    assert_eq!(
        freshen_aliasing_opaque_occurrences(&guard_and_violation, &occ),
        guard_and_violation,
        "the caller's ONE `K` must stay one term in the σ obligation",
    );
    assert_eq!(occ.get(), 0);
    // INV-4: it must NOT be a `__slice_len` (no spurious where-fact).
    assert!(!k.ends_with("__slice_len"));
}

/// The callee-side half of CONSTPARAM-SIGMA-FRESHEN-1: a `__trust_constparam_*`
/// leaf in a CALLEE's `P` names the callee instance's param, never the caller's
/// same-spelled one, so it is moved into the σ namespace before σ.
#[test]
fn callee_const_param_symbols_move_into_the_sigma_namespace() {
    let callee_m = trust_types::const_param_symbol(0, "M");
    let var = |name: &str| Formula::var(name, Sort::Int);
    let p = Formula::And(vec![
        Formula::Lt(Box::new(var("n")), Box::new(var(&callee_m))),
        Formula::Le(Box::new(var(&callee_m)), Box::new(var("buf__slice_len"))),
        Formula::var("__trust_constparam_1_B", Sort::Bool),
    ]);
    let isolated = isolate_callee_const_param_symbols(&p);
    let sigma_m = format!("{SIGMA_CALLEE_CONST_PARAM_PREFIX}0_M");
    assert_eq!(
        isolated,
        Formula::And(vec![
            Formula::Lt(Box::new(var("n")), Box::new(var(&sigma_m))),
            // Both occurrences of the callee's ONE `M` land on ONE σ name.
            Formula::Le(Box::new(var(&sigma_m)), Box::new(var("buf__slice_len"))),
            // Each leaf keeps its own sort (a `bool` const generic is `Sort::Bool`).
            Formula::var(&format!("{SIGMA_CALLEE_CONST_PARAM_PREFIX}1_B"), Sort::Bool),
        ]),
    );
    // The σ prefix is the one the replay lane rejects as a deliberately free var.
    assert!(SIGMA_CALLEE_CONST_PARAM_PREFIX.starts_with("__trust_sigma_"));
    assert!(!SIGMA_CALLEE_CONST_PARAM_PREFIX.starts_with(trust_types::CONST_PARAM_SYMBOL_PREFIX));

    // Identity on every `P` produced today (no family leaf).
    let plain = Formula::Lt(Box::new(var("n")), Box::new(var("buf__slice_len")));
    assert_eq!(isolate_callee_const_param_symbols(&plain), plain);

    // Binder-aware: a BOUND occurrence is not renamed (that would change meaning).
    let bound = Formula::exists(
        &[(callee_m.as_str(), Sort::Int)],
        Formula::And(vec![
            Formula::Lt(Box::new(var(&callee_m)), Box::new(var("n"))),
            Formula::Ge(
                Box::new(var(&trust_types::const_param_symbol(1, "N"))),
                Box::new(var("n")),
            ),
        ]),
    );
    assert_eq!(
        isolate_callee_const_param_symbols(&bound),
        Formula::exists(
            &[(callee_m.as_str(), Sort::Int)],
            Formula::And(vec![
                Formula::Lt(Box::new(var(&callee_m)), Box::new(var("n"))),
                Formula::Ge(
                    Box::new(var(&format!("{SIGMA_CALLEE_CONST_PARAM_PREFIX}1_N"))),
                    Box::new(var("n")),
                ),
            ]),
        ),
    );

    // A binder in the σ const-param namespace could capture a renamed leaf: the
    // whole `P` becomes the impossible caller obligation.
    let capturing = Formula::forall(
        &[(sigma_m.as_str(), Sort::Int)],
        Formula::Lt(Box::new(var(&callee_m)), Box::new(var(&sigma_m))),
    );
    assert_eq!(isolate_callee_const_param_symbols(&capturing), Formula::Bool(false));
}

// ---------------------------------------------------------------------------
// End to end through both σ producers and the solver (CONSTPARAM-SIGMA-FRESHEN-1).
//
//     pub fn pick(buf: &[u32], n: usize) -> u32 requires n < buf.len() { buf[n] }
//     pub fn caller_ok<const K: usize>(a: &[u32; K], n: usize) -> u32 {
//         if n < K { pick(a, n) } else { 0 }
//     }
//
// in the MIR shape rustc emits: the guard compares against the const param, and
// the argument is an unsize cast of `a`, whose length σ renders as the caller's `K`.
// ---------------------------------------------------------------------------

fn sym_array_ref(index: u32, name: &str) -> Ty {
    Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::SymArray {
            elem: Box::new(Ty::u32()),
            len_sym: trust_types::ConstLen { index, name: name.to_string() },
        }),
    }
}

fn u32_slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }) }
}

/// `caller<const K, const M>(a: &[u32; K], n: usize) { if n < <guard> { pick(a, n) } }`,
/// with `guard` the const param the comparison reads.
fn generic_guarded_caller(guard: trust_types::ConstValue) -> trust_types::VerifiableFunction {
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, Statement, Terminator,
        UnwindEdge, VerifiableBody, VerifiableFunction,
    };
    let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
        place,
        rvalue,
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "caller_ok".to_string(),
        def_path: "fixture::caller_ok".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: sym_array_ref(0, "K"), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: u32_slice_ref(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(guard),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::Cast(Operand::Copy(Place::local(1)), u32_slice_ref()),
                    )],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("fixture::pick"),
                        is_foreign: false,
                        func: "fixture::pick".to_string(),
                        args: vec![Operand::Move(Place::local(4)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(0, 32))),
                    )],
                    terminator: Terminator::Goto(BlockId(2)),
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn const_param(index: u32, name: &str) -> trust_types::ConstValue {
    trust_types::ConstValue::ConstParam { index, name: name.to_string(), width: 64, signed: false }
}

/// `pick(buf: &[u32], n: usize) requires <p>` with the R1/direct-summary param types.
fn pick_summaries(p: Formula) -> crate::modular::SummaryDatabase {
    let mut summaries = crate::modular::SummaryDatabase::new();
    summaries.insert(
        crate::modular::FunctionSummary::new("fixture::pick")
            .with_param_names(vec!["buf".to_string(), "n".to_string()])
            .with_param_types(vec![u32_slice_ref(), Ty::usize()])
            .with_precondition(p),
    );
    summaries
}

fn pick_requires_n_below_len() -> Formula {
    Formula::Lt(
        Box::new(Formula::var("n", Sort::Int)),
        Box::new(Formula::var("buf__slice_len", Sort::Int)),
    )
}

fn ay_verdict(vc: &trust_types::VerificationCondition) -> trust_types::VerificationResult {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    InProcessAyBackend::new().verify(vc)
}

fn mentions(formula: &Formula, needle: &str) -> bool {
    formula.free_variables().iter().any(|name| name.contains(needle))
}

/// Both σ producers, one precondition row each.
fn sigma_rows(
    caller: &trust_types::VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> (trust_types::VerificationCondition, (trust_types::VerificationCondition, Formula, Vec<Formula>))
{
    let mut ordinary = generate_callsite_precondition_vcs(caller, summaries);
    let mut attributed = generate_callsite_precondition_vcs_attributed(caller, summaries);
    assert_eq!(ordinary.len(), 1, "one precondition row: {ordinary:#?}");
    assert_eq!(attributed.len(), 1, "one attributed row: {attributed:#?}");
    let ordinary = ordinary.remove(0);
    let attributed = attributed.remove(0);
    assert!(matches!(ordinary.kind, trust_types::VcKind::Precondition { .. }), "{ordinary:#?}");
    assert_eq!(ordinary.formula, attributed.0.formula, "the twins must assemble identically");
    (ordinary, attributed)
}

/// The correct generic caller DISCHARGES: one `K` in the guard, the unsize fact and
/// σ's length. Before CONSTPARAM-SIGMA-FRESHEN-1 every occurrence was a distinct
/// `__trust_constparam_0_K__r1occ{n}` and this row was refuted (default rc 1).
#[test]
fn generic_caller_guard_on_its_own_k_discharges_the_callee_length_precondition() {
    let caller = generic_guarded_caller(const_param(0, "K"));
    let summaries = pick_summaries(pick_requires_n_below_len());
    let (ordinary, (attributed, substituted, guards)) = sigma_rows(&caller, &summaries);
    let k = trust_types::const_param_symbol(0, "K");

    assert!(!mentions(&ordinary.formula, "__r1occ"), "no split K: {:?}", ordinary.formula);
    assert!(mentions(&ordinary.formula, &k), "σ renders `buf.len()` as the caller's K");
    assert_eq!(
        substituted,
        Formula::Lt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::var(&k, Sort::Int))),
        "P[σ] reads the caller's K for `buf__slice_len`",
    );
    assert!(
        matches!(ay_verdict(&ordinary), trust_types::VerificationResult::Proved { .. }),
        "the guarded call must be PROVED: {:?}\n{:?}",
        ay_verdict(&ordinary),
        ordinary.formula,
    );
    // R1's exact per-site decision: kernel certificate + the structural gate.
    assert!(
        trust_certify::certify_vc(&attributed).is_some(),
        "R1's caller site must kernel-certify: {:?}",
        attributed.formula,
    );
    assert!(trust_router::strengthen_whole_program::is_admissible_caller_discharge(
        &attributed.formula,
        &substituted,
        &guards,
    ));
}

/// The buggy twin stays REFUTED: the guard reads a DIFFERENT const param `M`, the
/// array has length `K`, and identity keying keeps the two symbols apart.
#[test]
fn generic_caller_guard_on_a_different_const_param_stays_refuted() {
    let caller = generic_guarded_caller(const_param(1, "M"));
    let summaries = pick_summaries(pick_requires_n_below_len());
    let (ordinary, (attributed, _, _)) = sigma_rows(&caller, &summaries);
    assert!(
        matches!(ay_verdict(&ordinary), trust_types::VerificationResult::Failed { .. }),
        "a guard on M cannot discharge a length K: {:?}\n{:?}",
        ay_verdict(&ordinary),
        ordinary.formula,
    );
    assert!(trust_certify::certify_vc(&attributed).is_none());
}

/// THE PIN for "no two DISTINCT const-param values share one symbol in one VC"
/// after the family stopped being freshened. A CALLEE `P` that carries the
/// callee's own `M` spelled EXACTLY like the caller's `K`-guard symbol
/// (`__trust_constparam_0_K`: same index, same name, different item) must not be
/// discharged by the caller's guard `n < K`: the callee's `K` is its instance's
/// argument, not the caller's param. Without `isolate_callee_const_param_symbols`
/// the obligation would be `guard(n < K) ∧ ¬(n < K)`, UNSAT — a false PROVE. The
/// control (`buf__slice_len`, which σ renders from the ACTUAL argument) is the
/// previous test's PROVED row, so the two differ only in where `K` comes from.
#[test]
fn callee_const_param_cannot_meet_the_callers_symbol() {
    let caller = generic_guarded_caller(const_param(0, "K"));
    let callee_k = trust_types::const_param_symbol(0, "K");
    let summaries = pick_summaries(Formula::Lt(
        Box::new(Formula::var("n", Sort::Int)),
        Box::new(Formula::var(&callee_k, Sort::Int)),
    ));
    let (ordinary, (attributed, substituted, _)) = sigma_rows(&caller, &summaries);
    // The verdicts first: with the rename removed, this is where the test goes red
    // (ay `Proved`, kernel `Some`), which is the false PROVE the rename closes.
    assert!(
        matches!(ay_verdict(&ordinary), trust_types::VerificationResult::Failed { .. }),
        "a callee-side K must stay free (fail-closed): {:?}\n{:?}",
        ay_verdict(&ordinary),
        ordinary.formula,
    );
    assert!(
        trust_certify::certify_vc(&attributed).is_none(),
        "a callee-side K must never kernel-certify a caller site: {:?}",
        attributed.formula,
    );
    let isolated = format!("{SIGMA_CALLEE_CONST_PARAM_PREFIX}0_K");
    assert_eq!(
        substituted,
        Formula::Lt(
            Box::new(Formula::var("n", Sort::Int)),
            Box::new(Formula::var(&isolated, Sort::Int)),
        ),
        "the callee's K must leave the caller's namespace before σ",
    );
}

#[test]
fn freshen_and_substitute_owned_skip_rebuilding_untouched_trees() {
    let formula = Formula::And(vec![
        Formula::Lt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(4))),
        Formula::Ge(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(0))),
    ]);
    let ptr_before = match &formula {
        Formula::And(cs) => cs.as_ptr(),
        _ => unreachable!(),
    };
    let occ = std::cell::Cell::new(0u32);
    let after_freshen = super::freshen_aliasing_opaque_occurrences_owned(formula, &occ);
    assert_eq!(occ.get(), 0);
    let ptr_mid = match &after_freshen {
        Formula::And(cs) => cs.as_ptr(),
        _ => unreachable!(),
    };
    assert_eq!(ptr_before, ptr_mid, "non-opaque tree must be returned in place without reallocating");

    let replacements = vec![("unused".to_string(), Formula::var("x", Sort::Int))];
    let after_subst = super::substitute_summary_params_owned(after_freshen, &replacements);
    let ptr_after = match &after_subst {
        Formula::And(cs) => cs.as_ptr(),
        _ => unreachable!(),
    };
    assert_eq!(ptr_mid, ptr_after, "unmatched replacement must return non-quantified tree in place");

    // Positive control: `SymVar` and `Var` opaque occurrences still split per leaf and keep sort.
    let opaque_bool = format!("{}b_site", trust_types::OPAQUE_SCALAR_SYMBOL_PREFIX);
    let mixed = Formula::And(vec![
        Formula::SymVar(trust_types::Symbol::intern(&opaque_bool), Sort::Bool),
        Formula::var(&opaque_bool, Sort::Bool),
    ]);
    let split = super::freshen_aliasing_opaque_occurrences_owned(mixed, &occ);
    assert_eq!(occ.get(), 2);
    assert_eq!(
        split,
        Formula::And(vec![
            Formula::var_owned(format!("{opaque_bool}__r1occ0"), Sort::Bool),
            Formula::var_owned(format!("{opaque_bool}__r1occ1"), Sort::Bool),
        ]),
    );
}

#[test]
fn precondition_interval_dominance_lazy_skips_float_ctx_until_float_conjunct() {
    let caller = generic_guarded_caller(const_param(0, "K"));
    let ctx_cell: std::cell::OnceCell<super::FloatRangeCtx<'_>> = std::cell::OnceCell::new();
    let inits = std::cell::Cell::new(0u32);

    // 1. Relational precondition (`n < buf__slice_len`): rejected before `FloatRangeCtx`.
    assert!(!super::precondition_interval_dominance_lazy(
        &caller,
        || {
            inits.set(inits.get() + 1);
            ctx_cell.get_or_init(|| super::FloatRangeCtx::new(&caller, None))
        },
        BlockId(0),
        &pick_requires_n_below_len(),
        &["buf".to_string(), "n".to_string()],
        &[Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        &mut Vec::new(),
        super::FLOAT_EXP_BOUND_FUEL,
    ));
    assert_eq!(inits.get(), 0, "relational precondition must not initialize FloatRangeCtx");

    // 2. Empty `And([])`: fail-closed false, zero `FloatRangeCtx` init.
    assert!(!super::precondition_interval_dominance_lazy(
        &caller,
        || {
            inits.set(inits.get() + 1);
            ctx_cell.get_or_init(|| super::FloatRangeCtx::new(&caller, None))
        },
        BlockId(0),
        &Formula::And(Vec::new()),
        &["n".to_string()],
        &[Operand::Constant(ConstValue::Uint(3, 64))],
        &mut Vec::new(),
        super::FLOAT_EXP_BOUND_FUEL,
    ));
    assert_eq!(inits.get(), 0);

    // 3. Satisfied integer type-range/const conjuncts: proved without `FloatRangeCtx`.
    let int_pre = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(10))),
    ]);
    assert!(super::precondition_interval_dominance_lazy(
        &caller,
        || {
            inits.set(inits.get() + 1);
            ctx_cell.get_or_init(|| super::FloatRangeCtx::new(&caller, None))
        },
        BlockId(0),
        &int_pre,
        &["n".to_string()],
        &[Operand::Constant(ConstValue::Uint(3, 64))],
        &mut Vec::new(),
        super::FLOAT_EXP_BOUND_FUEL,
    ));
    assert_eq!(inits.get(), 0, "int-only dominance must not initialize FloatRangeCtx");

    // 4. Two-sided float literal bound: initializes `FloatRangeCtx` once and dominates.
    let f64_sort = Sort::Float { eb: 11, sb: 53 };
    let fp = |v: f64| Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 };
    let float_pre = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("v", f64_sort.clone())), Box::new(fp(0.0))),
        Formula::Le(Box::new(Formula::var("v", f64_sort)), Box::new(fp(1.0))),
    ]);
    assert!(super::precondition_interval_dominance_lazy(
        &caller,
        || {
            inits.set(inits.get() + 1);
            ctx_cell.get_or_init(|| super::FloatRangeCtx::new(&caller, None))
        },
        BlockId(0),
        &float_pre,
        &["v".to_string()],
        &[Operand::Constant(ConstValue::Float(0.5))],
        &mut Vec::new(),
        super::FLOAT_EXP_BOUND_FUEL,
    ));
    assert_eq!(inits.get(), 1);
}
